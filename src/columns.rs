//! Literal execution of checked row/column physical choices. No workload or
//! theorem recognisers. The sealed layout determines the carrier and codecs.
use crate::{
    syntax::{Program, Type},
    LangResult,
};
use ink_core::physical::CheckedPhysicalPlan;
use std::{cell::RefCell, collections::BTreeMap, fmt::Write};
std::thread_local! {static TYPES:RefCell<BTreeMap<String,(String,String)>>=RefCell::new(BTreeMap::new());}
pub(crate) struct Scope(BTreeMap<String, (String, String)>);
impl Drop for Scope {
    fn drop(&mut self) {
        TYPES.with(|t| *t.borrow_mut() = std::mem::take(&mut self.0));
    }
}
pub(crate) fn element(record: &str) -> Type {
    match record {
        "@U32" => Type::U32,
        "@U64" => Type::U64,
        "@Bool" => Type::Bool,
        _ => Type::Named(record.into()),
    }
}
pub(crate) fn names(t: &Type) -> Option<(String, String)> {
    let key = ink_core::registry::identity(t).ok()?;
    TYPES.with(|m| m.borrow().get(&key).cloned())
}
pub(crate) fn scope(plan: Option<&CheckedPhysicalPlan>) -> LangResult<Scope> {
    let mut types = BTreeMap::new();
    if let Some(p) = plan {
        for l in &p.plan().columns {
            let t = element(&l.record);
            let id = ink_core::registry::identity(&t)?;
            types.insert(
                id.clone(),
                (format!("InkColumns_{id}"), format!("InkColumnBuffer_{id}")),
            );
        }
    }
    Ok(Scope(
        TYPES.with(|m| std::mem::replace(&mut *m.borrow_mut(), types)),
    ))
}
pub(crate) fn emit(p: &Program, physical: Option<&CheckedPhysicalPlan>) -> LangResult<String> {
    let mut out = String::new();
    let Some(physical) = physical else {
        return Ok(out);
    };
    for layout in &physical.plan().columns {
        let schema = ink_core::column_codec::schema(p, &layout.record)?;
        let elem = element(&layout.record);
        let row = crate::state_native::ty(&elem)?;
        let (name, owner) = names(&elem).ok_or("column emission scope missing")?;
        let scalar = layout.record.starts_with('@');
        let mut gets = vec![];
        let mut pushes = vec![];
        let mut sets = vec![];
        let mut defaults = vec![];
        let mut capacities = vec![];
        let mut truncates = vec![];
        let mut append = vec![];
        let mut payload = vec![];
        let mut fields = vec![];
        let mut prepare_push = vec![];
        let mut prepare_append = vec![];
        for (i, (f, t)) in schema.fields.iter().enumerate() {
            let field = format!("c{i}");
            let rust = crate::state_native::ty(t)?;
            let value = if scalar {
                "row".into()
            } else {
                format!("row.l_{f}")
            };
            let packed = layout.packing.get(f);
            let storage = if let Some(p) = packed {
                if *t == Type::Bool {
                    "temporary::PackedBits".into()
                } else {
                    format!(
                        "temporary::PackedWords<{},{}>",
                        p.bits,
                        if *t == Type::U32 { 32 } else { 64 }
                    )
                }
            } else {
                format!("Vec<{rust}>")
            };
            fields.push(format!("{field}:{storage}"));
            defaults.push(format!("{field}:Default::default()"));
            capacities.push(format!("{field}:<{storage}>::with_capacity(n)"));
            truncates.push(format!("self.{field}.truncate(n);"));
            if packed.is_some() {
                let v = if *t == Type::Bool {
                    value.clone()
                } else {
                    format!("{value} as u64")
                };
                prepare_push.push(format!("self.{field}.prepare_push({v});"));
                prepare_append.push(format!("self.{field}.prepare_append(&other.{field});"));
                let cast = if *t == Type::Bool {
                    String::new()
                } else {
                    format!(" as {rust}")
                };
                gets.push(format!("self.{field}.get_unchecked(i){cast}"));
                let v = if *t == Type::Bool {
                    value.clone()
                } else {
                    format!("{value} as u64")
                };
                pushes.push(format!("self.{field}.push({v});"));
                sets.push(format!(
                    "if mask&(1u16<<{i})==0{{self.{field}.set(i,{v});}}"
                ));
                payload.push(format!("self.{field}.payload_bytes()"));
                append.push(format!("for i in 0..other.count{{self.{field}.push(unsafe{{other.{field}.get_unchecked(i)}});}}other.{field}.truncate(0);"));
            } else {
                prepare_push.push(format!("self.{field}.reserve(1);"));
                prepare_append.push(format!("self.{field}.reserve(other.count);"));
                gets.push(format!("(*self.{field}.get_unchecked(i)).clone()"));
                pushes.push(format!("self.{field}.push({value});"));
                sets.push(format!(
                    "if mask&(1u16<<{i})==0{{*self.{field}.get_unchecked_mut(i)={value};}}"
                ));
                payload.push(format!("self.{field}.len()*std::mem::size_of::<{rust}>()"));
                append.push(format!("self.{field}.append(&mut other.{field});"));
            }
        }
        let assemble = if scalar {
            gets[0].clone()
        } else {
            format!(
                "{row}{{{}}}",
                schema
                    .fields
                    .iter()
                    .zip(&gets)
                    .map(|((f, _), v)| format!("l_{f}:{v}"))
                    .collect::<Vec<_>>()
                    .join(",")
            )
        };
        writeln!(out,r#"
#[derive(Clone,Debug)]pub struct {name}{{count:usize,{fields}}}
impl Default for {name}{{fn default()->Self{{Self{{count:0,{defaults}}}}}}}
impl {name}{{
 pub fn len(&self)->usize{{self.count}}
 pub fn is_empty(&self)->bool{{self.count==0}}
 pub fn payload_bytes(&self)->usize{{{payload}}}
 pub fn storage_identity(&self)->usize{{{storage}}}
 pub fn with_capacity(n:usize)->Self{{Self{{count:0,{capacities}}}}}
 pub fn get(&self,i:usize)->Option<{row}>{{if i<self.count{{Some(unsafe{{self.get_unchecked(i)}})}}else{{None}}}}
 pub unsafe fn get_unchecked(&self,i:usize)->{row}{{{assemble}}}
 pub fn push(&mut self,row:{row}){{let count=self.count.checked_add(1).expect("column length overflow");{prepare_push}{pushes}self.count=count;}}
 pub fn set(&mut self,i:usize,row:{row}){{assert!(i<self.count);unsafe{{self.set_masked(i,row,0);}}}}
 unsafe fn set_masked(&mut self,i:usize,row:{row},mask:u16){{{sets}}}
 pub fn map_rows(mut self,mut f:impl FnMut({row})->{row},mask:u16)->Self{{for i in 0..self.count{{let row=f(unsafe{{self.get_unchecked(i)}});unsafe{{self.set_masked(i,row,mask);}}}}self}}
 pub fn truncate(&mut self,n:usize){{let n=n.min(self.count);{truncates}self.count=n;}}
 pub fn append(&mut self,other:&mut Self){{let n=self.count.checked_add(other.count).expect("column length overflow");{prepare_append}{append}self.count=n;other.count=0;}}
 pub fn iter(&self)->impl DoubleEndedIterator<Item={row}>+ExactSizeIterator+'_{{(0..self.count).map(move|i|unsafe{{self.get_unchecked(i)}})}}
 pub fn into_rows(self)->Vec<{row}>{{self.into_iter().collect()}}
 pub fn drain<R:std::ops::RangeBounds<usize>>(&mut self,range:R)->std::vec::IntoIter<{row}>{{let mut rows=std::mem::take(self).into_rows();let removed=rows.drain(range).collect::<Vec<_>>();*self=rows.into();removed.into_iter()}}
 pub fn sort(&mut self){{let mut rows=std::mem::take(self).into_rows();rows.sort_by(|a,b|{{{compare}}});*self=rows.into();}}
}}
impl From<Vec<{row}>> for {name}{{fn from(rows:Vec<{row}>)->Self{{rows.into_iter().collect()}}}}
impl std::iter::FromIterator<{row}> for {name}{{fn from_iter<I:IntoIterator<Item={row}>>(rows:I)->Self{{let rows=rows.into_iter();let mut out=Self::with_capacity(rows.size_hint().0);for row in rows{{out.push(row);}}out}}}}
pub struct Into_{name}{{data:{name},front:usize,back:usize}}
impl Iterator for Into_{name}{{type Item={row};fn next(&mut self)->Option<{row}>{{if self.front==self.back{{None}}else{{let i=self.front;self.front+=1;Some(unsafe{{self.data.get_unchecked(i)}})}}}}fn size_hint(&self)->(usize,Option<usize>){{let n=self.back-self.front;(n,Some(n))}}}}
impl DoubleEndedIterator for Into_{name}{{fn next_back(&mut self)->Option<{row}>{{if self.front==self.back{{None}}else{{self.back-=1;Some(unsafe{{self.data.get_unchecked(self.back)}})}}}}}}
impl ExactSizeIterator for Into_{name}{{}}
impl IntoIterator for {name}{{type Item={row};type IntoIter=Into_{name};fn into_iter(self)->Self::IntoIter{{let back=self.count;Into_{name}{{data:self,front:0,back}}}}}}
impl Wire for {name}{{fn from_json(v:&Json)->Result<Self,String>{{<Vec<{row}> as Wire>::from_json(v).map(Into::into)}}fn to_json(&self)->Json{{Json::Array(self.iter().map(|v|v.to_json()).collect())}}}}
impl BinaryValue for {name}{{fn from_binary(v:value_wire::Validated<'_>)->Result<Self,String>{{v.require_kind("list")?;v.items()?.map(|x|<{row} as BinaryValue>::from_binary(x?)).collect::<Result<Vec<_>,_>>().map(Into::into)}}fn write_binary(&self,w:&mut value_wire::Encoder)->Result<(),String>{{w.frame(|w|{{w.word(self.len().try_into().map_err(|_|"wire sequence size")?)?;for row in self.iter(){{row.write_binary(w)?;}}Ok(())}})}}}}
impl InkDataEq for {name}{{fn ink_data_eq(&self,r:&Self)->bool{{self.len()==r.len()&&self.iter().zip(r.iter()).all(|(a,b)|a.ink_data_eq(&b))}}}}
impl PartialEq for {name}{{fn eq(&self,r:&Self)->bool{{self.ink_data_eq(r)}}}}
#[derive(Clone,Debug)]pub struct {owner}({name});
pub struct {owner}View<'a>{{data:&'a {name},start:usize,end:usize}}
impl {owner}View<'_>{{
 pub fn len(&self)->u32{{(self.end-self.start).try_into().expect("buffer exceeds u32")}}
 pub fn get(&self,i:u32)->Option<{row}>{{if(i as usize)<self.end-self.start{{self.data.get(self.start+i as usize)}}else{{None}}}}
 pub fn with_item<R>(&self,i:u32,f:impl FnOnce(Option<&{row}>)->R)->R{{let value=self.get(i);f(value.as_ref())}}
 pub unsafe fn get_unchecked(&self,i:u32)->{row}{{self.data.get_unchecked(self.start+i as usize)}}
 pub fn with_range<R>(&self,start:u32,count:u32,f:impl FnOnce({owner}View<'_>)->R)->R{{let start=self.start+(start as usize).min(self.end-self.start);let end=start+(count as usize).min(self.end-start);f({owner}View{{data:self.data,start,end}})}}
}}
impl {owner}{{
 pub fn new(xs:{name})->Self{{Self(xs)}}
 pub fn len(&self)->u32{{self.0.len().try_into().expect("buffer exceeds u32")}}
 pub fn get(&self,i:u32)->Option<{row}>{{self.0.get(i as usize)}}
 pub unsafe fn get_unchecked(&self,i:u32)->{row}{{self.0.get_unchecked(i as usize)}}
 pub fn with_item<R>(&self,i:u32,f:impl FnOnce(Option<&{row}>)->R)->R{{let v=self.get(i);f(v.as_ref())}}
 pub fn with_range<R>(&self,start:u32,count:u32,f:impl FnOnce({owner}View<'_>)->R)->R{{let start=(start as usize).min(self.0.len());let end=start+(count as usize).min(self.0.len()-start);f({owner}View{{data:&self.0,start,end}})}}
 pub fn push(mut self,v:{row})->Self{{assert!(self.0.len()<u32::MAX as usize,"buffer length exhausted");self.0.push(v);self}}
 pub fn set(mut self,i:u32,v:{row})->Self{{if(i as usize)<self.0.len(){{self.0.set(i as usize,v);}}self}}
 pub fn swap(mut self,a:u32,b:u32)->Self{{if(a as usize)<self.0.len()&&(b as usize)<self.0.len(){{let x=self.0.get(a as usize).unwrap();let y=self.0.get(b as usize).unwrap();self.0.set(a as usize,y);self.0.set(b as usize,x);}}self}}
 pub fn fill_range(mut self,start:u32,count:u32,v:{row})->Self{{let a=(start as usize).min(self.0.len());let n=(count as usize).min(self.0.len()-a);for i in a..a+n{{self.0.set(i,v.clone());}}self}}
 pub fn copy_within(mut self,source:u32,destination:u32,count:u32)->Self{{let a=(source as usize).min(self.0.len());let b=(destination as usize).min(self.0.len());let n=(count as usize).min(self.0.len()-a).min(self.0.len()-b);if b>a{{for i in(0..n).rev(){{let v=self.0.get(a+i).unwrap();self.0.set(b+i,v);}}}}else if b<a{{for i in 0..n{{let v=self.0.get(a+i).unwrap();self.0.set(b+i,v);}}}}self}}
 pub fn truncate(mut self,n:u32)->Self{{self.0.truncate(n as usize);self}}
 pub fn pop(self)->Self{{let n=self.len().saturating_sub(1);self.truncate(n)}}
 pub fn map_inplace(self,f:impl FnMut({row})->{row})->Self{{Self(self.0.map_rows(f,0))}}
 pub fn map_masked(self,f:impl FnMut({row})->{row},mask:u16)->Self{{Self(self.0.map_rows(f,mask))}}
 pub fn map_indexed_inplace(self,mut f:impl FnMut(u32,{row})->{row})->Self{{let mut i=0u32;Self(self.0.map_rows(|v|{{let out=f(i,v);i=i.wrapping_add(1);out}},0))}}
 pub fn filter_inplace(self,mut f:impl FnMut({row})->bool)->Self{{Self(self.0.into_iter().filter(|v|f(v.clone())).collect())}}
 pub fn scan_inplace(self,mut acc:{row},mut f:impl FnMut({row},{row})->{row})->Self{{Self(self.0.into_iter().map(|v|{{acc=f(acc.clone(),v);acc.clone()}}).collect())}}
 pub fn split(mut self,at:u32)->(Self,Self){{let at=(at as usize).min(self.0.len());let rows=self.0.drain(at..).collect::<Vec<_>>();(self,Self(rows.into()))}}
 pub fn append(mut self,mut other:Self)->Self{{self.0.append(&mut other.0);self}}
 pub fn freeze(self)->{name}{{self.0}}
}}
impl Wire for {owner}{{fn from_json(_: &Json)->Result<Self,String>{{Err("temporary storage is internal to a pure invocation".into())}}fn to_json(&self)->Json{{Json::Null}}}}
impl InkDataEq for {owner}{{fn ink_data_eq(&self,_:&Self)->bool{{panic!("temporary storage has no value equality")}}}}
"#,storage=if layout.packing.contains_key(&schema.fields[0].0){"self.c0.storage_identity()"}else{"self.c0.as_ptr()as usize"},prepare_push=prepare_push.join(""),prepare_append=prepare_append.join(""),capacities=capacities.join(","),fields=fields.join(","),defaults=defaults.join(","),payload=payload.join("+"),pushes=pushes.join(""),sets=sets.join(""),truncates=truncates.join(""),append=append.join(""),compare=if scalar{"a.partial_cmp(b).unwrap_or(std::cmp::Ordering::Equal)".into()}else{schema.fields.iter().map(|(f,_)|format!("let order=a.l_{f}.partial_cmp(&b.l_{f}).unwrap_or(std::cmp::Ordering::Equal);if order!=std::cmp::Ordering::Equal{{return order;}}" )).collect::<String>()+"std::cmp::Ordering::Equal"}).unwrap();
        if schema.fields.iter().all(|(_, t)| *t != Type::F32) {
            writeln!(out, "impl Eq for {name}{{}} ").unwrap();
        }
    }
    Ok(out)
}

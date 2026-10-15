//! Type-directed spelling of the existing portable writer, without JSON trees.
//! Recursive bindings retain the shared codec. Column iterators preserve the
//! same logical order and budgets while yielding owned rows rather than loans.
use crate::{
    snapshot_wire::{Layout, Schema},
    syntax::{Program, Type},
    LangResult,
};
use std::fmt::Write;
fn supported(t: &Type, s: &Schema) -> bool {
    match (t, s) {
        (_, Schema::Bind(..) | Schema::Ref(..)) => false,
        (Type::List(t), Schema::List(s)) => supported(t, s),
        (Type::Vector(t, _), Schema::Vector(s, _)) | (Type::Option(t), Schema::Option(s)) => {
            supported(t, s)
        }
        (Type::Result(a, b), Schema::Result(x, y)) => supported(a, x) && supported(b, y),
        (_, Schema::Record(_)) => true,
        _ => true,
    }
}
fn value(
    p: &Program,
    t: &Type,
    s: &Schema,
    v: &str,
    depth: usize,
    serial: &mut usize,
) -> LangResult<String> {
    if depth > 128 || !supported(t, s) {
        return Err("typed snapshot fallback".into());
    }
    let mut out = format!("writer.tick({depth})?;");
    let owned_list_items = matches!(t,Type::List(inner) if crate::columns::names(inner).is_some());
    match (t, s) {
        (Type::Unit, Schema::Unit) => {}
        (Type::Bool, Schema::Bool) => write!(out, "writer.bytes(&[(*({v})) as u8])?;").unwrap(),
        (Type::U32, Schema::U32) | (Type::U64, Schema::U64) | (Type::I32, Schema::I32) => {
            write!(out, "writer.bytes(&({v}).to_le_bytes())?;").unwrap()
        }
        (Type::F32, Schema::F32) | (Type::F64, Schema::F64) => {
            write!(out, "writer.bytes(&({v}).to_bits().to_le_bytes())?;").unwrap()
        }
        (Type::String, Schema::String) => write!(out, "writer.raw(({v}).as_bytes())?;").unwrap(),
        (Type::Int, Schema::Int) => write!(out, "writer.integer({v})?;").unwrap(),
        (Type::Named(_), Schema::Id) => {
            write!(out, "writer.bytes(&({v}).0.to_le_bytes())?;").unwrap()
        }
        (Type::Named(n), Schema::Enum(_)) => {
            let variants = if n == "ArithmeticError" {
                vec!["Overflow".to_string()]
            } else {
                p.enums[n].clone()
            };
            let native = crate::state_native::ty(t)?;
            write!(out, "writer.bytes(&(match {v}{{").unwrap();
            for (i, name) in variants.iter().enumerate() {
                write!(out, "{native}::l_{name}=>{i}u32,").unwrap();
            }
            out.push_str("}).to_le_bytes())?;");
        }
        (Type::Named(n), Schema::Record(fields)) => {
            for (f, fs) in fields {
                let ft = p.records[n]
                    .iter()
                    .find(|(name, _)| name == f)
                    .ok_or("snapshot field")?;
                let access = if crate::state_native::boxed_field(n, &ft.1, p) {
                    format!("&*({v}).l_{f}")
                } else {
                    format!("&({v}).l_{f}")
                };
                out.push_str(&value(p, &ft.1, fs, &access, depth + 1, serial)?);
            }
        }
        (Type::List(t), Schema::List(s)) | (Type::Vector(t, _), Schema::Vector(s, _)) => {
            if matches!(s.as_ref(), Schema::Bind(..) | Schema::Ref(..)) {
                return Err("recursive typed snapshot fallback".into());
            }
            if matches!(t.as_ref(), Type::Unknown) {
                return Err("snapshot type".into());
            }
            *serial += 1;
            let item = format!("snapshot_item_{serial}");
            write!(
                out,
                "for {item} in ({v}).iter(){{{}
}}",
                value(p, t, s, &if owned_list_items {format!("&{item}")} else {item.clone()}, depth + 1, serial)?
            )
            .unwrap();
        }
        (Type::Option(t), Schema::Option(s)) => {
            *serial += 1;
            let item = format!("snapshot_some_{serial}");
            write!(
                out,
                "match {v}{{Some({item})=>{{writer.bytes(&[1])?;{}}},None=>writer.bytes(&[0])?,}}",
                value(p, t, s, &item, depth + 1, serial)?
            )
            .unwrap();
        }
        (Type::Result(a, b), Schema::Result(x, y)) => {
            *serial += 1;
            let item = format!("snapshot_result_{serial}");
            write!(out,"match {v}{{Ok({item})=>{{writer.bytes(&[0])?;{}}},Err({item})=>{{writer.bytes(&[1])?;{}}},}}",value(p,a,x,&item,depth+1,serial)?,value(p,b,y,&item,depth+1,serial)?).unwrap();
        }
        _ => return Err("typed snapshot schema mismatch".into()),
    }
    // Lists count their length after their own value tick, before child ticks.
    if let (Type::List(_), Schema::List(_)) = (t, s) {
        let tick = format!("writer.tick({depth})?;");
        out = out.replacen(
            &tick,
            &format!("{tick}writer.list_length(({v}).len())?;"),
            1,
        );
    }
    out.push_str("writer.value_end()?;");
    if out.len() > 1_000_000 {
        return Err("typed snapshot spelling budget".into());
    }
    Ok(out)
}
pub fn checkpoint(p: &Program, layout: &Layout) -> Option<String> {
    let mut serial = 0;
    let mut body=String::from("let mut writer=TypedSnapshotWriter::new(limits);writer.bytes(&self.version.to_le_bytes())?;");
    for (n, k, vs) in &layout.roots {
        let state = p.states.iter().find(|s| &s.name == n)?;
        let Type::Table(kt, vt) = &state.ty else {
            return None;
        };
        write!(body,"writer.rows(self.l_{n}.len())?;let mut previous=None;for(key,value)in self.l_{n}.iter(){{if previous.is_some_and(|p|p>=key){{return Err(\"snapshot keys must be strictly ordered\".into())}}previous=Some(key);").ok()?;
        body.push_str(&value(p, kt, k, "key", 0, &mut serial).ok()?);
        body.push_str(&value(p, vt, vs, "value", 0, &mut serial).ok()?);
        body.push('}');
    }
    body.push_str("writer.count(self.outbox.len())?;let mut prior=None;for event in &self.outbox{if event.commit==0||event.commit>self.version||prior.is_some_and(|p|p>=(event.commit,event.position)){return Err(\"invalid snapshot event sequence\".into())}writer.bytes(&event.commit.to_le_bytes())?;writer.bytes(&event.position.to_le_bytes())?;match &event.data{");
    for (i, (n, s)) in layout.events.iter().enumerate() {
        write!(
            body,
            "EventData::l_{n}(value)=>{{writer.bytes(&({i}u32).to_le_bytes())?;{}}},",
            value(p, &p.events[n], s, "value", 0, &mut serial).ok()?
        )
        .ok()?;
    }
    if layout.events.is_empty() {
        body.push_str("_=>unreachable!(\"empty event type\"),");
    }
    body.push_str("}prior=Some((event.commit,event.position));}writer.finish(&layout)");
    Some(body)
}
fn decoded(
    p: &Program,
    t: &Type,
    s: &Schema,
    depth: usize,
    serial: &mut usize,
) -> LangResult<String> {
    if depth > 128 || !supported(t, s) {
        return Err("typed restore fallback".into());
    }
    let expression=match(t,s){
  (Type::Unit,Schema::Unit)=>"()".into(),(Type::Bool,Schema::Bool)=>"reader.boolean()?".into(),
  (Type::U32,Schema::U32)=>"reader.u32()?".into(),(Type::U64,Schema::U64)=>"reader.u64()?".into(),(Type::I32,Schema::I32)=>"reader.u32()? as i32".into(),
  (Type::F32,Schema::F32)=>"f32::from_bits(reader.u32()?)".into(),(Type::F64,Schema::F64)=>"f64::from_bits(reader.u64()?)".into(),(Type::String,Schema::String)=>"std::str::from_utf8(reader.raw()?).map_err(|_|\"invalid UTF-8\")?.to_owned()".into(),(Type::Int,Schema::Int)=>"reader.integer()?".into(),
  (Type::Named(_),Schema::Id)=>format!("{}(u128::from_le_bytes(reader.take(16)?.try_into().unwrap()))",crate::state_native::ty(t)?),
  (Type::Named(n),Schema::Enum(_))=>{let variants=if n=="ArithmeticError"{vec!["Overflow".to_string()]}else{p.enums[n].clone()};let name=crate::state_native::ty(t)?;let mut body=String::from("match reader.u32()?{");for(i,v)in variants.iter().enumerate(){write!(body,"{i}=>{name}::l_{v},").unwrap();}body.push_str("_=>return Err(\"invalid enum tag\".into())}");body},
  (Type::Named(n),Schema::Record(fields))=>{let mut body=format!("{}{{",crate::state_native::ty(t)?);for(f,s)in fields{let t=&p.records[n].iter().find(|(name,_)|name==f).ok_or("snapshot field")?.1;let v=decoded(p,t,s,depth+1,serial)?;write!(body,"l_{f}:{},",if crate::state_native::boxed_field(n,t,p){format!("Box::new({v})")}else{v}).unwrap();}body.push('}');body},
  (Type::List(t),Schema::List(s))=>{let value=decoded(p,t,s,depth+1,serial)?;*serial+=1;let name=format!("snapshot_values_{serial}");let collection=crate::state_native::ty(&Type::List(t.clone()))?;format!("{{let count=reader.sequence()?;let mut {name}:{collection}=Default::default();for _ in 0..count{{{name}.push({value});}}{name}}}")},
  (Type::Vector(t,n),Schema::Vector(s,m))if n==m=>{let value=decoded(p,t,s,depth+1,serial)?;format!("[{}]",(0..*n).map(|_|value.clone()).collect::<Vec<_>>().join(","))},
  (Type::Option(t),Schema::Option(s))=>format!("match reader.byte()?{{0=>None,1=>Some({}),_=>return Err(\"invalid Option tag\".into())}}",decoded(p,t,s,depth+1,serial)?),
  (Type::Result(a,b),Schema::Result(x,y))=>format!("match reader.byte()?{{0=>Ok({}),1=>Err({}),_=>return Err(\"invalid Result tag\".into())}}",decoded(p,a,x,depth+1,serial)?,decoded(p,b,y,depth+1,serial)?),
  _=>return Err("typed restore schema mismatch".into()),
 };
    if expression.len() > 1_000_000 {
        return Err("typed restore spelling budget".into());
    }
    Ok(format!("{{reader.tick({depth})?;{expression}}}"))
}
pub fn restore(p: &Program, layout: &Layout) -> Option<String> {
    let mut serial = 0;
    let mut body=String::from("let mut reader=TypedSnapshotReader::new(&layout,bytes,limits)?;let mut state=Self::new();state.version=reader.u64()?;");
    for (n, k, v) in &layout.roots {
        let Type::Table(kt, vt) = &p.states.iter().find(|s| &s.name == n)?.ty else {
            return None;
        };
        let key = decoded(p, kt, k, 0, &mut serial).ok()?;
        let value = decoded(p, vt, v, 0, &mut serial).ok()?;
        write!(body,"let count=reader.sequence()?;if count>reader.left/2{{return Err(\"snapshot row limit exceeded\".into())}}let mut previous=None;for _ in 0..count{{let key={key};let value={value};if previous.as_ref().is_some_and(|p|p>=&key){{return Err(\"duplicate or unordered snapshot key\".into())}}previous=Some(key.clone());state.l_{n}.insert(key,value);}}").ok()?;
    }
    body.push_str("let count=reader.sequence()?;let mut prior=None;for _ in 0..count{let commit=reader.u64()?;let position=reader.u64()?;let channel=reader.u32()?;let data=match channel{");
    for (i, (n, s)) in layout.events.iter().enumerate() {
        write!(
            body,
            "{i}=>EventData::l_{n}({}),",
            decoded(p, &p.events[n], s, 0, &mut serial).ok()?
        )
        .ok()?;
    }
    body.push_str("_=>return Err(\"unknown snapshot event channel\".into())};if commit==0||commit>state.version||prior.is_some_and(|p|p>=(commit,position)){return Err(\"invalid snapshot event sequence\".into())}prior=Some((commit,position));state.outbox.push(Event{commit,position,data});}reader.finish()?;");
    Some(body)
}

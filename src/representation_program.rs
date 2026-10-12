//! Standalone typed programs from compile-time checked representations.
//! Admission is complete before emission. Generated code imports no Ink crate.
use ink_core::{
    logic::{Declaration, Sort},
    representation::CheckedRepresentation,
    syntax::Type,
    LangResult,
};
use std::{collections::BTreeMap, fmt::Write};

struct Emit<'a> {
    checked: &'a CheckedRepresentation,
    types: BTreeMap<String, (usize, Type, Sort)>,
    packed_ids: std::collections::BTreeSet<String>,
}
fn data(sort: &Sort) -> LangResult<&str> {
    if let Sort::Data(id) = sort {
        Ok(id)
    } else {
        Err("expected source datatype".into())
    }
}
fn fields(bindings: &[String]) -> String {
    if bindings.is_empty() {
        String::new()
    } else {
        format!("({})", bindings.join(","))
    }
}
fn borrowed(sort: &Sort, expression: &str) -> String {
    if matches!(sort, Sort::Data(_)) {
        format!("&({expression})")
    } else {
        expression.into()
    }
}
fn stored(sort: &Sort, expression: &str) -> String {
    if matches!(sort, Sort::Data(_)) {
        format!("std::sync::Arc::new({expression})")
    } else {
        expression.into()
    }
}
impl Emit<'_> {
    fn sort(&self, t: &Type) -> LangResult<&Sort> {
        Ok(&self
            .types
            .get(&serde_json::to_string(t).map_err(|e| e.to_string())?)
            .ok_or("missing source codec sort")?
            .2)
    }
    fn codec(
        &self,
        t: &Type,
        direction: &str,
        expression: &str,
        depth: &str,
    ) -> LangResult<String> {
        let index = self
            .types
            .get(&serde_json::to_string(t).map_err(|e| e.to_string())?)
            .ok_or("missing source codec")?
            .0;
        Ok(format!("{direction}_{index}({expression},{depth})?"))
    }
    fn wire(&self) -> LangResult<String> {
        let p = self.checked.module().program();
        let mut out = String::new();
        for (_, (index, t, sort)) in &self.types {
            if ink_core::local_collections::owned(t, p) {
                continue;
            }
            let ty = crate::definition_native::ty(sort)?;
            writeln!(
                out,
                "fn read_{index}(v:&Json,d:usize)->Result<{ty},String>{{Ok("
            )
            .unwrap();
            let native = match t {
                Type::U64 => "v.as_u64().unwrap()".into(),
                Type::F32 => "{let bits=if let Some(x)=v.get(\"F32Bits\"){x.as_u64().unwrap() as u32}else{(v.as_f64().unwrap() as f32).to_bits()};bits as u64}".into(),
                Type::U32 => "v.as_u64().unwrap()".into(),
                Type::I32 => "v.as_i64().unwrap() as i32 as u32 as u64".into(),
                Type::Int => {
                    let id=data(sort)?;
                    let natural=self.checked.projection().objects[id].payload["declaration"]["Datatype"]["constructors"][1]["fields"][0]["Data"].as_str().ok_or("binary magnitude datatype")?;
                    format!("{{let text=v.get(\"Int\").and_then(Json::as_str).map(str::to_owned).unwrap_or_else(||v.to_string());let n=text.parse::<num_bigint::BigInt>().unwrap();let bits=n.bits() as usize;let(_,bytes)=n.to_bytes_le();let mut tail=D_{natural}::C0;for bit in (0..bits).rev(){{tail=if bytes[bit/8]&(1<<(bit%8))==0{{D_{natural}::C1(Some(std::sync::Arc::new(tail)))}}else{{D_{natural}::C2(Some(std::sync::Arc::new(tail)))}};}}if bits==0{{D_{id}::C0}}else if n.sign()==num_bigint::Sign::Minus{{D_{id}::C2(std::sync::Arc::new(tail))}}else{{D_{id}::C1(std::sync::Arc::new(tail))}}}}")
                }
                Type::String => {let id=data(sort)?;let step=if self.packed_ids.contains(id){"tail.prepend(byte as u64)".into()}else{format!("D_{id}::C1(byte as u64,Some(std::sync::Arc::new(tail)))")};format!("{{let mut tail=D_{id}::C0;for byte in v.as_str().unwrap().bytes().rev(){{tail={step};}}tail}}")},
                Type::Named(n) if p.ids.contains(n) => {let id=data(sort)?;format!("{{let x=u128::from_str_radix(v.as_str().unwrap(),16).unwrap();D_{id}::C0((x>>64)as u64,x as u64)}}")},
                Type::Bool => "v.as_bool().unwrap()".into(),
                Type::Unit => format!("{{D_{}::C0}}", data(sort)?),
                Type::Named(n) if p.enums.contains_key(n) => {
                    let id=data(sort)?;
                    let branches=p.enums[n].iter().enumerate().map(|(i,v)|format!("{:?}=>D_{id}::C{i},",format!("{n}.{v}"))).collect::<String>();
                    format!("{{let text=v.as_str().unwrap();match text{{{branches}_=>unreachable!(\"caller enum precondition\")}}}}")
                }
                Type::Named(n) if p.records.contains_key(n) => {
                    let fs=&p.records[n];
                    let args=fs.iter().map(|(name,t)| {
                        let read=self.codec(t,"read",&format!("xs.get({name:?}).unwrap()",),"d+1")?;
                        Ok(stored(self.sort(t)?, &read))
                    }).collect::<LangResult<Vec<_>>>()?;
                    format!("{{let xs=v.as_object().unwrap();D_{}::C0{}}}",data(sort)?,fields(&args))
                }
                Type::Option(a) => {
                    let id=data(sort)?;
                    let read=stored(self.sort(a)?,&self.codec(a,"read","x","d+1")?);
                    format!("{{let xs=one_tag(v,\"Option\")?;if let Some(x)=xs.get(\"Some\"){{D_{id}::C1({read})}}else{{D_{id}::C0}}}}")
                }
                Type::Result(a,b) => {
                    let id=data(sort)?;
                    let a=stored(self.sort(a)?,&self.codec(a,"read","x","d+1")?);
                    let b=stored(self.sort(b)?,&self.codec(b,"read","x","d+1")?);
                    format!("{{let xs=one_tag(v,\"Result\")?;if let Some(x)=xs.get(\"Ok\"){{D_{id}::C0({a})}}else{{let x=xs.get(\"Err\").unwrap();D_{id}::C1({b})}}}}")
                }
                Type::Vector(a,n) => {let args=(0..*n as usize).map(|i|Ok(stored(self.sort(a)?,&self.codec(a,"read",&format!("&xs[{i}]"),"d+1")?))).collect::<LangResult<Vec<_>>>()?;format!("{{let xs=v.as_array().unwrap();D_{}::C0{}}}",data(sort)?,fields(&args))},
                Type::List(a) => {
                    let id=data(sort)?;
                    let read=stored(self.sort(a)?,&self.codec(a,"read","x","d+1")?);
                    let step=if self.packed_ids.contains(id){format!("tail.prepend({read})")}else{format!("D_{id}::C1({read},Some(std::sync::Arc::new(tail)))")};
                    format!("{{let xs=v.as_array().unwrap();let mut tail=D_{id}::C0;for x in xs.iter().rev(){{tail={step};}}tail}}")
                }
                _ => return Err("unsupported standalone source codec".into()),
            };
            writeln!(
                out,
                "{native})}}\nfn write_{index}(v:&{ty},d:usize)->Result<Json,String>{{Ok("
            )
            .unwrap();
            let json = match t {
                Type::U64 | Type::Bool => "json!(v)".into(),
                Type::F32 => "{let bits=*v as u32;let x=f32::from_bits(bits);if x.is_finite(){json!(x)}else{json!({\"F32Bits\":bits})}}".into(),
                Type::U32 => "{json!(v)}".into(),
                Type::I32 => "{json!(*v as u32 as i32)}".into(),
                Type::Int => {
                    let id=data(sort)?;
                    let natural=self.checked.projection().objects[id].payload["declaration"]["Datatype"]["constructors"][1]["fields"][0]["Data"].as_str().ok_or("binary magnitude datatype")?;
                    format!("{{match v{{D_{id}::C0=>json!({{\"Int\":\"0\"}}),D_{id}::C1(tail)|D_{id}::C2(tail)=>{{let mut cursor=tail.as_ref();let mut magnitude=num_bigint::BigUint::from(0u8);let mut bits=0;loop{{match cursor{{D_{natural}::C0=>break,D_{natural}::C1(tail)|D_{natural}::C2(tail)=>{{if matches!(cursor,D_{natural}::C2(_)){{magnitude|=num_bigint::BigUint::from(1u8)<<bits;}}bits+=1;cursor=tail.as_deref().expect(\"live recursive edge\");}}}}}}let sign=if matches!(v,D_{id}::C2(_)){{num_bigint::Sign::Minus}}else{{num_bigint::Sign::Plus}};json!({{\"Int\":num_bigint::BigInt::from_biguint(sign,magnitude).to_string()}})}}}}}}")
                }
                Type::String => {let id=data(sort)?;if self.packed_ids.contains(id){"{json!(String::from_utf8(v.cells().map(|byte|byte as u8).collect()).unwrap())}".into()}else{format!("{{let mut cursor=v;let mut bytes=vec![];loop{{match cursor{{D_{id}::C0=>break,D_{id}::C1(byte,tail)=>{{bytes.push(*byte as u8);cursor=tail.as_deref().expect(\"live recursive edge\");}}}}}}json!(String::from_utf8(bytes).unwrap())}}")}},
                Type::Named(n) if p.ids.contains(n) => {let id=data(sort)?;format!("{{let D_{id}::C0(high,low)=v;json!(format!(\"{{:032x}}\",((*high as u128)<<64)|*low as u128))}}")},
                Type::Unit => "Json::Null".into(),
                Type::Named(n) if p.enums.contains_key(n) => {
                    let id=data(sort)?;
                    let branches=p.enums[n].iter().enumerate().map(|(i,v)|format!("D_{id}::C{i}=>json!({:?}),",format!("{n}.{v}"))).collect::<String>();
                    format!("match v{{{branches}}}")
                }
                Type::Named(n) if p.records.contains_key(n) => {
                    let fs=&p.records[n];
                    let bs=(0..fs.len()).map(|i|format!("b{i}")).collect::<Vec<_>>();
                    let pairs=fs.iter().enumerate().map(|(i,(name,t))|Ok(format!("{:?}:{}",name,self.codec(t,"write",&format!("&b{i}"),"d+1")?))).collect::<LangResult<Vec<_>>>()?;
                    format!("{{let D_{}::C0{}=v;json!({{{}}})}}",data(sort)?,fields(&bs),pairs.join(","))
                }
                Type::Option(a) => format!("match v{{D_{}::C0=>json!({{\"None\":null}}),D_{}::C1(x)=>json!({{\"Some\":{}}})}}",data(sort)?,data(sort)?,self.codec(a,"write","x","d+1")?),
                Type::Result(a,b) => format!("match v{{D_{}::C0(x)=>json!({{\"Ok\":{}}}),D_{}::C1(x)=>json!({{\"Err\":{}}})}}",data(sort)?,self.codec(a,"write","x","d+1")?,data(sort)?,self.codec(b,"write","x","d+1")?),
                Type::Vector(a,n)=>{let bs=(0..*n).map(|i|format!("b{i}")).collect::<Vec<_>>();let xs=(0..*n).map(|i|self.codec(a,"write",&format!("&b{i}"),"d+1")).collect::<LangResult<Vec<_>>>()?;format!("{{let D_{}::C0{}=v;Json::Array(vec![{}])}}",data(sort)?,fields(&bs),xs.join(","))},
                Type::List(a) => if self.packed_ids.contains(data(sort)?){format!("{{let mut xs=vec![];for x in v.cells(){{xs.push({});}}Json::Array(xs)}}",self.codec(a,"write","&x","d+1")?)}else{format!("{{let mut cursor=v;let mut xs=vec![];loop{{match cursor{{D_{}::C0=>break,D_{}::C1(x,tail)=>{{xs.push({});cursor=tail.as_deref().expect(\"live recursive edge\");}}}}}}Json::Array(xs)}}",data(sort)?,data(sort)?,self.codec(a,"write","x","d+1")?)},
                _ => unreachable!(),
            };
            writeln!(out, "{json})}}").unwrap();
        }
        Ok(out)
    }
    fn tables(&self) -> LangResult<String> {
        let p = self.checked.module().program();
        let projection = self.checked.projection();
        let mut out = String::new();
        let mut roots = vec![];
        writeln!(out,"fn logical_from_tables(tables:&[Vec<(Json,Json)>])->Result<D_{},String>{{if tables.len()!={}{{return Err(\"representation table count mismatch\".into())}}",projection.state,p.states.len()).unwrap();
        let mut order = p.states.iter().map(|s| &s.name).collect::<Vec<_>>();
        order.sort();
        for (i, (root, model)) in p.states.iter().zip(&projection.tables).enumerate() {
            let position = order.iter().position(|n| *n == &root.name).unwrap();
            let id = &model.datatype;
            let t = &model.value_type;
            let read = stored(self.sort(t)?, &self.codec(t, "read", "row", "0")?);
            let key_read = stored(
                self.sort(&model.key_type)?,
                &self.codec(&model.key_type, "read", "key", "0")?,
            );
            writeln!(out,"let rows=&tables[{position}];let mut root{i}=D_{id}::C0;for (key,row) in rows.iter().rev(){{root{i}=D_{id}::C1({key_read},{read},Some(std::sync::Arc::new(root{i})));}}").unwrap();
            roots.push(format!("std::sync::Arc::new(root{i})"));
        }
        writeln!(out,"Ok(D_{}::C0{})}}\nfn logical_tables(state:&D_{})->Result<Vec<Vec<(Json,Json)>>,String>{{let D_{}::C0{}=state;",projection.state,fields(&roots),projection.state,projection.state,fields(&(0..roots.len()).map(|i|format!("r{i}")).collect::<Vec<_>>())).unwrap();
        for (i, model) in projection.tables.iter().enumerate() {
            let id = &model.datatype;
            let write = self.codec(&model.value_type, "write", "value", "0")?;
            let key_write = self.codec(&model.key_type, "write", "key", "0")?;
            writeln!(out,"let mut rows{i}=vec![];let mut cursor=r{i}.as_ref();loop{{match cursor{{D_{id}::C0=>break,D_{id}::C1(key,value,tail)=>{{rows{i}.push(({key_write},{write}));cursor=tail.as_deref().expect(\"live recursive edge\");}}}}}}").unwrap();
        }
        let ordered = order
            .iter()
            .map(|name| {
                format!(
                    "rows{}",
                    p.states.iter().position(|s| &s.name == *name).unwrap()
                )
            })
            .collect::<Vec<_>>();
        writeln!(out, "Ok(vec![{}])}}", ordered.join(",")).unwrap();
        let list = &projection.events;
        let declaration: Declaration =
            serde_json::from_value(projection.objects[list].payload["declaration"].clone())
                .map_err(|e| e.to_string())?;
        let Declaration::Datatype { constructors } = declaration else {
            return Err("event list datatype".into());
        };
        let event = data(&constructors[1].fields[0])?;
        if self.packed_ids.contains(list) {
            writeln!(out,"fn logical_events(events:&D_{list})->Result<Vec<(usize,Json)>,String>{{let mut out=vec![];for event in events.cells(){{let value=match event.as_ref(){{").unwrap();
        } else {
            writeln!(out,"fn logical_events(events:&D_{list})->Result<Vec<(usize,Json)>,String>{{let mut cursor=events;let mut out=vec![];loop{{match cursor{{D_{list}::C0=>break,D_{list}::C1(event,tail)=>{{let value=match event.as_ref(){{").unwrap();
        }
        if p.events.is_empty() {
            writeln!(
                out,
                "D_{event}::C0=>return Err(\"unknown source event\".into()),"
            )
            .unwrap();
        }
        for (i, (_, t)) in p.events.iter().enumerate() {
            writeln!(
                out,
                "D_{event}::C{i}(value)=>({i},{}),",
                self.codec(t, "write", "value", "0")?
            )
            .unwrap();
        }
        if self.packed_ids.contains(list) {
            out.push_str("};out.push(value);}Ok(out)}\n");
        } else {
            out.push_str("};out.push(value);cursor=tail.as_deref().expect(\"live recursive edge\");}}}Ok(out)}\n");
        }
        Ok(out)
    }
}

/// Emit one already selected representation as an ordinary compiled program.
/// The private checker witness is consumed only by this compile-time function.
pub fn lower(checked: &CheckedRepresentation) -> LangResult<String> {
    lower_native(checked, false, false, false,None)
}
/// Explicit exact packed storage for scalar columns, lists and local owners.
pub fn lower_packed(checked: &CheckedRepresentation) -> LangResult<String> {
    lower_native(checked, false, true, false,None)
}

/// Standalone native host for the C lowering's type-specific borrowed ABI.
/// C bodies are linked separately. This emits no interpreter or Ink dependency.
pub fn lower_c_host(checked: &CheckedRepresentation) -> LangResult<String> {
    lower_native(checked, true, false, false,None)
}

pub fn lower_memo(checked: &CheckedRepresentation) -> LangResult<String> {
    lower_native(checked, false, false, true,None)
}
pub fn lower_planned(plan: &ink_core::planning::CheckedPlan) -> LangResult<String> {
    let checked=plan.representation().ok_or("planned representation missing")?;
    let physical=plan.physical();
    let definitions=physical.map(|p|p.plan().definitions).unwrap_or_default();
    lower_native(checked,false,definitions==ink_core::physical::Definitions::Packed,definitions==ink_core::physical::Definitions::Memo,physical)
}
fn lower_native(
    checked: &CheckedRepresentation,
    foreign: bool,
    packed: bool,
    memo: bool,
    physical: Option<&ink_core::physical::CheckedPhysicalPlan>,
) -> LangResult<String> {
    let reachable = checked.definition().reachable_executable_declarations()?;
    let types = checked
        .projection()
        .types
        .iter()
        // Source projection also records internal-only carrier types. Emitting
        // codecs for unreachable ones references datatypes the literal emitter
        // correctly omitted (for example an unused Table<_,Bool> remove result).
        .filter(|(_, sort)| match sort {
            Sort::Data(id) => reachable.contains_key(id),
            _ => true,
        })
        .enumerate()
        .filter(|(_, (_, sort))| match sort {
            Sort::Data(id) => reachable.contains_key(id),
            _ => true,
        })
        .map(|(i, (key, sort))| {
            Ok((
                key.clone(),
                (
                    i,
                    serde_json::from_str::<Type>(key).map_err(|e| e.to_string())?,
                    sort.clone(),
                ),
            ))
        })
        .collect::<LangResult<BTreeMap<_, _>>>()?;
    let packed_ids = if let Some(physical)=physical {
        physical.plan().packed_datatypes.iter().cloned().collect()
    } else if packed {
        checked
            .definition()
            .reachable_executable_declarations()?
            .into_iter()
            .filter_map(|(id, d)| match d {
                Declaration::Datatype { constructors: c }
                    if c.len() == 2
                        && c[0].fields.is_empty()
                        && c[1].fields.len() == 2
                        && c[1].fields[1] == Sort::SelfType
                        && matches!(c[1].fields[0], Sort::Bool | Sort::U64 | Sort::Data(_)) =>
                {
                    Some(id)
                }
                _ => None,
            })
            .collect()
    } else {
        Default::default()
    };
    let e = Emit {
        checked,
        types,
        packed_ids,
    };
    let p = checked.module().program();
    let plan = checked.plan();
    let (queries, observers) = ink_core::field_projection::host_observers(checked)?;
    let transitions: BTreeMap<String,Declaration> = BTreeMap::new();
    let emission = if let Some(physical)=physical {
        crate::definition_native::lower_typed_planned(checked.definition(),&queries,physical)?
    } else if foreign {
        crate::definition_native::lower_typed_shared_datatypes(checked.definition(), &queries)?
    } else if memo {
        crate::definition_native::lower_typed_memo(checked.definition(), &queries)?
    } else if packed {
        crate::definition_native::lower_typed_packed(checked.definition(), &queries)?
    } else {
        crate::definition_native::lower_typed_shared_projected(checked.definition(), &queries)?
    };
    let mut out = emission.source;
    if foreign {
        let residuals = queries
            .iter()
            .chain(transitions.iter())
            .map(|(n, d)| (n.clone(), d.clone()))
            .collect();
        out.push_str(&crate::representation_ffi::emit(
            checked.definition(),
            &residuals,
        )?);
    }
    out.push_str("\nuse serde_json::{Value as Json,json};\nmod portable{\n");
    out.push_str(ink_core::SNAPSHOT_WIRE_RUST_SOURCE);
    out.push_str("\n}\npub use portable::Limits as SnapshotLimits;\n");
    let layout = ink_core::snapshot::layout(checked.snapshot_module().program())?;
    writeln!(out,"fn snapshot_layout()->portable::Layout{{portable::Layout{{program:{:?},schema:{:?},roots:vec![",layout.program,layout.schema).unwrap();
    for (n, k, v) in &layout.roots {
        writeln!(
            out,
            "({n:?}.into(),{},{}),",
            crate::snapshot_code::schema_code(k),
            crate::snapshot_code::schema_code(v)
        )
        .unwrap();
    }
    out.push_str("],events:vec![");
    for (n, t) in &layout.events {
        writeln!(
            out,
            "({n:?}.into(),{}),",
            crate::snapshot_code::schema_code(t)
        )
        .unwrap();
    }
    out.push_str("]}}\n");
    out.push_str("fn one_tag<'a>(v:&'a Json,_kind:&str)->Result<&'a serde_json::Map<String,Json>,String>{Ok(v.as_object().unwrap())}\n");
    out.push_str(&e.wire()?);
    out.push_str(&e.tables()?);
    let physical = crate::definition_native::ty(&plan.physical_state)?;
    out.push_str("pub use portable::Event;\npub struct Outcome<T>{pub result:T,pub committed:bool,pub version:u64,pub events:Vec<Event>}\npub struct OutcomeView<'a,T>{pub result:T,pub committed:bool,pub version:u64,pub events:&'a[Event]}\nimpl<T> OutcomeView<'_,T>{pub fn into_owned(self)->Outcome<T>{Outcome{result:self.result,committed:self.committed,version:self.version,events:self.events.to_vec()}}}\n");
    writeln!(out,"struct HostTransaction{{physical:{physical},version:u64,removed:Vec<portable::Event>}}\n pub struct State{{physical:{physical},version:u64,outbox:Vec<portable::Event>,layout:portable::Layout,host:Option<HostTransaction>}}\nimpl State{{").unwrap();
    let empty = checked
        .projection()
        .tables
        .iter()
        .map(|t| format!("std::sync::Arc::new(D_{}::C0)", t.datatype))
        .collect::<Vec<_>>();
    out.push_str("// CALLER CONTRACT: arguments must have the declared types and canonical values.\n// No runtime type validation. Malformed input may panic, trap or corrupt state.\n");
    writeln!(out,"pub fn new()->Result<Self,String>{{let logical=D_{}::C0{};Ok(Self{{physical:f_{}(&logical),version:0,outbox:vec![],layout:snapshot_layout(),host:None}})}}",checked.projection().state,fields(&empty),plan.encode).unwrap();
    writeln!(out,"pub fn restore(bytes:&[u8])->Result<Self,String>{{let layout=snapshot_layout();let saved=portable::decode(&layout,bytes,SnapshotLimits::default())?;let logical=logical_from_tables(&saved.tables)?;Ok(Self{{physical:f_{}(&logical),version:saved.version,outbox:saved.outbox,layout,host:None}})}}",plan.encode).unwrap();
    writeln!(out,"pub fn checkpoint(&self)->Result<Vec<u8>,String>{{let logical=f_{}({});portable::encode(&self.layout,&portable::Logical{{version:self.version,tables:logical_tables(&logical)?,outbox:self.outbox.clone()}},SnapshotLimits::default())}}",plan.decode,borrowed(&plan.physical_state,"self.physical")).unwrap();
    out.push_str("pub fn version(&self)->u64{self.version}\npub fn outbox_json(&self)->Json{Json::Array(self.outbox.iter().map(|e|json!({\"commit\":e.commit,\"position\":e.position,\"channel\":self.layout.events[e.channel].0,\"value\":e.value})).collect())}\npub fn acknowledge_through(&mut self,commit:u64,position:u64){let n=self.outbox.iter().take_while(|e|(e.commit,e.position)<=(commit,position)).count();let removed=self.outbox.drain(..n);if let Some(host)=&mut self.host{host.removed.extend(removed.filter(|e|e.commit<=host.version));}}\n pub fn begin_transaction(&mut self)->Result<bool,String>{if self.host.is_some(){return Err(\"state transaction already in progress\".into())}self.host=Some(HostTransaction{physical:self.physical.clone(),version:self.version,removed:vec![]});Ok(true)}\n pub fn commit_transaction(&mut self){self.host=None;}\n pub fn rollback_transaction(&mut self){if let Some(host)=self.host.take(){self.physical=host.physical;self.version=host.version;self.outbox.retain(|e|e.commit<=host.version);let mut restored=host.removed;restored.append(&mut self.outbox);self.outbox=restored;}}\n");
    // Typed query entry points bypass JSON and the complete transaction envelope.
    for source in &p.actions {
        let a = &plan.actions[&source.name];
        let name = format!("q_{}", a.execute);
        let Some(Declaration::Function { params, result, .. }) = queries.get(&name) else {
            continue;
        };
        let inputs = params[2..]
            .iter()
            .enumerate()
            .map(|(i, (_, s))| {
                Ok(format!(
                    "a{i}:{}{}",
                    if matches!(s, Sort::Data(_)) { "&" } else { "" },
                    crate::definition_native::ty(s)?
                ))
            })
            .collect::<LangResult<Vec<_>>>()?;
        let mut args = vec![
            borrowed(&plan.physical_state, "self.physical"),
            "self.version".into(),
        ];
        args.extend((0..inputs.len()).map(|i| format!("a{i}")));
        writeln!(
            out,
            "pub fn query_{}(&self,{})->{}{{f_{name}({})}}",
            source.name,
            inputs.join(","),
            crate::definition_native::ty(result)?,
            args.join(",")
        )
        .unwrap();
    }
    // The direct native bridge accepts the sealed definition's typed carriers.
    // Replies own their values; committed events borrow the existing outbox.
    for source in &p.actions {
        let a = &plan.actions[&source.name];
        let reply_sort = e.sort(&source.result)?;
        let reply_ty = crate::definition_native::ty(reply_sort)?;
        let inputs = source
            .params
            .iter()
            .enumerate()
            .map(|(i, (_, t))| {
                let sort = e.sort(t)?;
                Ok(format!(
                    "a{i}:{}{}",
                    if matches!(sort, Sort::Data(_)) {
                        "&"
                    } else {
                        ""
                    },
                    crate::definition_native::ty(sort)?
                ))
            })
            .collect::<LangResult<Vec<_>>>()?;
        let mut args = vec![
            borrowed(&plan.physical_state, "self.physical"),
            "self.version".into(),
        ];
        args.extend((0..inputs.len()).map(|i| format!("a{i}")));
        writeln!(
            out,
            "pub fn invoke_view_{}(&mut self,{})->Result<OutcomeView<'_,{reply_ty}>,String>{{",
            source.name,
            inputs.join(",")
        )
        .unwrap();
        let query = format!("q_{}", a.execute);
        if queries.contains_key(&query) {
            writeln!(out,"let result=f_{query}({});Ok(OutcomeView{{result,committed:false,version:self.version,events:&self.outbox[self.outbox.len()..]}})}}",args.join(",")).unwrap();
            continue;
        }
        let observation = data(
            a.compact.as_ref().map(|c| &c.result)
                .unwrap_or(&checked.projection().actions[&source.name].result),
        )?;
        let observe = a.compact.as_ref().map(|c| c.observe.as_str())
            .unwrap_or(&observers[&source.name]);
        let observed_fields = if a.compact.is_some() {
            "reply,committed,version,events"
        } else {
            "reply,committed,version,_,events"
        };
        writeln!(
            out,
            "let executed={}({});let observed=f_{}({});let next=f_{}({});",
            if transitions.contains_key(&format!("t_{}", a.execute)) {
                format!("f_t_{}", a.execute)
            } else {
                format!("f_{}", a.execute)
            },
            args.join(","),
            observe,
            borrowed(&a.result, "executed"),
            a.next,
            borrowed(&a.result, "executed")
        )
        .unwrap();
        let owned_reply = if matches!(reply_sort, Sort::Data(_)) {
            "reply.as_ref().clone()"
        } else {
            "*reply"
        };
        writeln!(out,"let(result,committed,version,events)=match &observed{{D_{observation}::C0({observed_fields})=>({owned_reply},*committed,*version,events),D_{observation}::C1(..)=>return Err(\"commit sequence exhausted\".into())}};let start=self.outbox.len();let staged=logical_events(events)?;if committed{{self.outbox.try_reserve(staged.len()).map_err(|_|\"outbox allocation failure\")?;for(position,(channel,value))in staged.into_iter().enumerate(){{self.outbox.push(Event{{commit:version,position:position as u64,channel,value}});}}}}self.physical=next;self.version=version;Ok(OutcomeView{{result,committed,version,events:&self.outbox[start..]}})}}").unwrap();
    }
    out.push_str(
        "pub fn invoke_json(&mut self,name:&str,args:&Json)->Result<Json,String>{match name{\n",
    );
    for source in &p.actions {
        let a = &plan.actions[&source.name];
        let observation = data(
            a.compact
                .as_ref()
                .map(|c| &c.result)
                .unwrap_or(&checked.projection().actions[&source.name].result),
        )?;
        let observe = a
            .compact
            .as_ref()
            .map(|c| c.observe.as_str())
            .unwrap_or(&observers[&source.name]);
        let observed_fields = if a.compact.is_some() {
            "reply,committed,version,events"
        } else {
            "reply,committed,version,_,events"
        };
        writeln!(out, "{:?}=>{{let xs=args.as_array().unwrap();", source.name).unwrap();
        let mut args = vec![
            borrowed(&plan.physical_state, "self.physical"),
            "self.version".into(),
        ];
        for (i, (_, t)) in source.params.iter().enumerate() {
            let sort = e.sort(t)?;
            writeln!(
                out,
                "let a{i}={};",
                e.codec(t, "read", &format!("&xs[{i}]"), "0")?
            )
            .unwrap();
            args.push(borrowed(sort, &format!("a{i}")));
        }
        let query = format!("q_{}", a.execute);
        if queries.contains_key(&query) {
            writeln!(out,"let reply=f_{query}({});let result={};Ok(json!({{\"result\":result,\"committed\":false,\"version\":self.version,\"events\":[]}}))}},",args.join(","),e.codec(&source.result,"write","&reply","0")?).unwrap();
            continue;
        }
        writeln!(
            out,
            "let executed={}({});",
            if transitions.contains_key(&format!("t_{}", a.execute)) {
                format!("f_t_{}", a.execute)
            } else {
                format!("f_{}", a.execute)
            },
            args.join(",")
        )
        .unwrap();
        let executed = borrowed(&a.result, "executed");
        writeln!(out,"let observed=f_{}({executed});let next=f_{}({executed});let(reply,committed,version,events)=match &observed{{D_{observation}::C0({observed_fields})=>(reply,*committed,*version,events),D_{observation}::C1(..)=>return Err(\"commit sequence exhausted\".into())}};let result={};let staged=logical_events(events)?;let mut published=vec![];",observe,a.next,e.codec(&source.result,"write","reply","0")?).unwrap();
        let names = p
            .events
            .keys()
            .map(|n| format!("{n:?}"))
            .collect::<Vec<_>>();
        writeln!(out,"if committed{{let channels:&[&str]=&[{}];for(position,(channel,value))in staged.into_iter().enumerate(){{published.push(json!({{\"commit\":version,\"position\":position as u64,\"channel\":channels[channel],\"value\":value}}));self.outbox.push(portable::Event{{commit:version,position:position as u64,channel,value}});}}}}self.physical=next;self.version=version;Ok(json!({{\"result\":result,\"committed\":committed,\"version\":version,\"events\":published}}))}},",names.join(",")).unwrap();
    }
    out.push_str("_=>Err(format!(\"unknown action {name}\"))}}}\n");
    if out.len() > 16_000_000 {
        return Err("standalone representation source size limit".into());
    }
    Ok(out)
}

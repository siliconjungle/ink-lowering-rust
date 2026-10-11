//! Literal compilation of sealed database definitions. No layout or cache rules.
use ink_core::{
    definition::CheckedDefinition,
    representation::{CheckedMigration, CheckedRepresentation},
    LangResult,
};
fn executable_identity(d: &CheckedDefinition) -> LangResult<String> {
    ink_core::registry::identity(&(
        "ink-sealed-executable-v1",
        d.bundle_sha256(),
        d.exports(),
        d.choices(),
    ))
}
/// Compile a bounded set of pinned definitions for transaction-boundary switches.
/// The generated executor refuses any other definition closure identity.
pub fn lower(
    representations: &[CheckedRepresentation],
    migrations: &[CheckedMigration],
) -> LangResult<String> {
    if representations.is_empty() || representations.len() > 16 || migrations.len() > 16 {
        return Err("native representation bundle limit".into());
    }
    let source = representations[0].module().identity()?;
    if representations
        .iter()
        .any(|c| c.module().identity().ok().as_ref() != Some(&source))
    {
        return Err("native bundle changes source".into());
    }
    if migrations.iter().any(|m| m.source_identity() != source) {
        return Err("native migration bundle changes source".into());
    }
    let mut definitions: Vec<&CheckedDefinition> =
        representations.iter().map(|c| c.definition()).collect();
    definitions.extend(migrations.iter().map(|c| c.definition()));
    let mut output = String::from("use ink_core as __ink_rep_core;\n");
    for (i, d) in definitions.iter().enumerate() {
        let emitted = crate::definition_native::lower_shared(d)?;
        output.push_str(&format!("mod definition_{i} {{\n{}\n", emitted.source));
        output.push_str("use super::__ink_rep_core as ink_core;\n");
        if let Some(checked) = representations.get(i) {
            output.push_str("pub fn transition(action:&str,args:&[Value])->Result<(Value,Value), &'static str>{validate_inputs(args)?;match action{\n");
            for (name, action) in &checked.plan().actions {
                let object: ink_core::library::Object =
                    serde_json::from_str(&d.bundle().objects[&action.execute])
                        .map_err(|e| e.to_string())?;
                let ink_core::logic::Declaration::Function { params, .. } = object.declaration
                else {
                    return Err("representation execute is not a function".into());
                };
                output.push_str(&format!("{name:?} if args.len()=={}=>{{\n", params.len()));
                let mut inputs = Vec::new();
                for (j, (_, sort)) in params.iter().enumerate() {
                    output.push_str(&format!(
                        "let a{j}={};\n",
                        crate::definition_native::decode_value(sort, &format!("&args[{j}]"))
                    ));
                    inputs.push(format!(
                        "{}a{j}",
                        if matches!(sort, ink_core::logic::Sort::Data(_)) {
                            "&"
                        } else {
                            ""
                        }
                    ));
                }
                let executed = if matches!(action.result, ink_core::logic::Sort::Data(_)) {
                    "&executed"
                } else {
                    "executed"
                };
                let observed_sort = &checked.projection().actions[name].result;
                output.push_str(&format!("let executed=f_{}({});\nlet observed=f_{}({executed});\nlet next=f_{}({executed});\nOk(({},{}))}},\n",action.execute,inputs.join(","),action.observe,action.next,crate::definition_native::encode_value(observed_sort,"observed",false),crate::definition_native::encode_value(&checked.plan().physical_state,"next",false)));
            }
            output.push_str("_=>Err(\"unknown representation action or argument count\"),}}\n");
            let physical_sort = &checked.plan().physical_state;
            let physical_type = crate::definition_native::ty(physical_sort)?;
            let bounds = if let ink_core::logic::Sort::Data(id) = physical_sort {
                output.push_str(&crate::representation_bounds::emit(d,Some(id))?);
                format!("if !same_storage(state,&next){{bounded_storage(Storage::D_{id}(&next))?;}}")
            } else {
                output.push_str(&crate::representation_bounds::emit(d,None)?);
                String::new()
            };
            output.push_str(&format!("pub fn prepared_transition(action:&str,state:&{physical_type},args:&[Value],_compact:bool)->Result<(Value,{physical_type}), &'static str>{{validate_inputs(args)?;match action{{\n"));
            for (name, action) in &checked.plan().actions {
                let object: ink_core::library::Object =
                    serde_json::from_str(&d.bundle().objects[&action.execute])
                        .map_err(|e| e.to_string())?;
                let ink_core::logic::Declaration::Function { params, .. } = object.declaration
                else {
                    return Err("representation execute is not a function".into());
                };
                output.push_str(&format!("{name:?} if args.len()=={}=>{{\n", params.len()-1));
                let mut inputs = Vec::new();
                for (j, (_, sort)) in params.iter().enumerate() {
                    if j == 0 { inputs.push(if matches!(physical_sort, ink_core::logic::Sort::Data(_)) { "state" } else { "*state" }.to_string()); continue; }
                    output.push_str(&format!(
                        "let a{j}={};\n",
                        crate::definition_native::decode_value(sort, &format!("&args[{}]",j-1))
                    ));
                    inputs.push(format!(
                        "{}a{j}",
                        if matches!(sort, ink_core::logic::Sort::Data(_)) {
                            "&"
                        } else {
                            ""
                        }
                    ));
                }
                let executed = if matches!(action.result, ink_core::logic::Sort::Data(_)) {
                    "&executed"
                } else {
                    "executed"
                };
                let observed_sort = &checked.projection().actions[name].result;
                let projected={
                    let ink_core::logic::Sort::Data(obs_id)=observed_sort else{return Err("query observation datatype".into());};
                    let ink_core::logic::Declaration::Datatype{constructors}= &checked.definition().executable_declarations()?[obs_id] else{return Err("query observation declaration".into());};
                    let fields=&constructors[0].fields;
                    format!("match &observed{{D_{obs_id}::C0(reply,committed,version,_state,events)=>Value::Data{{datatype:{obs_id:?}.into(),constructor:0,arguments:vec![{},Value::Bool(*committed),Value::U64(*version),Value::Bool(false),{}]}},_=>return Err(\"commit sequence exhausted\")}}",crate::definition_native::encode_value(&fields[0],"reply",true),crate::definition_native::encode_value(&fields[4],"events",true))
                };
                let observation_bounds=if let ink_core::logic::Sort::Data(id)=observed_sort {format!("bounded_storage(Storage::D_{id}(&observed))?;")}else{String::new()};
                output.push_str(&format!("let executed=f_{}({});\nlet observed=f_{}({executed});\nlet next=f_{}({executed});\n{observation_bounds}\n{bounds}\nOk(({},{}))}},\n",action.execute,inputs.join(","),action.observe,action.next,projected,"next"));
            }
            output.push_str("_=>Err(\"unknown representation action or argument count\"),}}\n");
        }
        output.push_str(include_str!("representation_transport.rs.txt"));
        if let Some(checked) = representations.get(i) {
            let sort = &checked.plan().physical_state;
            let t = crate::definition_native::ty(sort)?;
            let warm=if let ink_core::logic::Sort::Data(id)=sort {format!("bounded_storage(Storage::D_{id}(&result)).map_err(str::to_owned)?;")}else{String::new()};
            output.push_str(&format!("pub fn prepare(t:ink_core::logic::Term)->ink_core::LangResult<Box<dyn std::any::Any>>{{let value=input(t,0)?;validate_inputs(std::slice::from_ref(&value)).map_err(str::to_owned)?;let result=(||->Result<{t},&'static str>{{Ok({})}})().map_err(str::to_owned)?;{warm}Ok(Box::new(result))}}\n", crate::definition_native::decode_value(sort,"&value")));
            output.push_str(&format!("pub fn materialise(t:&dyn std::any::Any)->ink_core::LangResult<ink_core::logic::Term>{{let value=t.downcast_ref::<{t}>().ok_or(\"prepared state identity\")?;Ok(output({}))}}\n",crate::definition_native::encode_value(sort,"value",true)));
            output.push_str(&format!("pub fn run_prepared(action:&str,t:&dyn std::any::Any,args:Vec<ink_core::logic::Term>,compact:bool)->ink_core::LangResult<(ink_core::logic::Term,Box<dyn std::any::Any>)>{{let state=t.downcast_ref::<{t}>().ok_or(\"prepared state identity\")?;let values=args.into_iter().map(|x|input(x,0)).collect::<ink_core::LangResult<Vec<_>>>()?;let (observed,next)=prepared_transition(action,state,&values,compact).map_err(str::to_owned)?;Ok((output(observed),Box::new(next)))}}\n"));
        }

        output.push_str("}\n");
    }
    output.push_str("pub struct Native;\nimpl ink_runtime::representation::Executor for Native {\nfn execute(&self, definition:&ink_core::definition::CheckedDefinition, _context:&ink_core::logic::Context,function:&str,args:Vec<ink_core::logic::Term>)->ink_core::LangResult<ink_core::logic::Term>{\nlet executable=ink_core::registry::identity(&(\"ink-sealed-executable-v1\",definition.bundle_sha256(),definition.exports(),definition.choices()))?;\nmatch executable.as_str(){\n");
    for (i, d) in definitions.iter().enumerate() {
        output.push_str(&format!("{:?}=>{{\n", executable_identity(d)?));
        output.push_str(&format!("let values=args.into_iter().map(|x|definition_{i}::input(x,0)).collect::<ink_core::LangResult<Vec<_>>>()?;\n"));
        output.push_str(&format!(
            "Ok(definition_{i}::output(definition_{i}::invoke(function,&values).map_err(str::to_owned)?))\n}},\n"
        ));
    }
    output.push_str(
        "_=>Err(\"native executor does not contain the pinned definition\".into()),\n}\n}\n",
    );
    output.push_str("fn transition(&self,checked:&ink_core::representation::CheckedRepresentation,action:&str,args:Vec<ink_core::logic::Term>)->ink_core::LangResult<(ink_core::logic::Term,ink_core::logic::Term)>{\nlet d=checked.definition();let executable=ink_core::registry::identity(&(\"ink-sealed-executable-v1\",d.bundle_sha256(),d.exports(),d.choices()))?;\nmatch (checked.request().representation.as_str(),executable.as_str()){\n");
    for (i, checked) in representations.iter().enumerate() {
        output.push_str(&format!("({:?},{:?})=>{{let values=args.into_iter().map(|x|definition_{i}::input(x,0)).collect::<ink_core::LangResult<Vec<_>>>()?;let (observed,next)=definition_{i}::transition(action,&values).map_err(str::to_owned)?;Ok((definition_{i}::output(observed),definition_{i}::output(next)))}},\n",checked.request().representation,executable_identity(checked.definition())?));
    }
    output.push_str("_=>Err(\"native executor does not contain the pinned representation\".into()),}}\n");
    for mode in ["prepare", "materialise", "transition_prepared", "transition_prepared_readonly"] {
        let signature = match mode {
            "prepare" => "fn prepare(&self,c:&ink_core::representation::CheckedRepresentation,p:&ink_core::logic::Term)->ink_core::LangResult<Option<Box<dyn std::any::Any>>>",
            "materialise" => "fn materialise(&self,c:&ink_core::representation::CheckedRepresentation,p:&dyn std::any::Any)->ink_core::LangResult<ink_core::logic::Term>",
            "transition_prepared_readonly" => "fn transition_prepared_readonly(&self,c:&ink_core::representation::CheckedRepresentation,action:&str,p:&dyn std::any::Any,args:Vec<ink_core::logic::Term>)->ink_core::LangResult<Option<(ink_core::logic::Term,Box<dyn std::any::Any>)>>",
            _ => "fn transition_prepared(&self,c:&ink_core::representation::CheckedRepresentation,action:&str,p:&dyn std::any::Any,args:Vec<ink_core::logic::Term>)->ink_core::LangResult<(ink_core::logic::Term,Box<dyn std::any::Any>)>",
        };
        output.push_str(signature);
        output.push_str("{let d=c.definition();let executable=ink_core::registry::identity(&(\"ink-sealed-executable-v1\",d.bundle_sha256(),d.exports(),d.choices()))?;match (c.request().representation.as_str(),executable.as_str()){\n");
        for (i,c) in representations.iter().enumerate() {
            let body = match mode { "prepare" => format!("definition_{i}::prepare(p.clone()).map(Some)"), "materialise" => format!("definition_{i}::materialise(p)"), "transition_prepared_readonly"=>format!("definition_{i}::run_prepared(action,p,args,true).map(Some)"), _ => format!("definition_{i}::run_prepared(action,p,args,false)") };
            output.push_str(&format!("({:?},{:?})=>{body},\n",c.request().representation,executable_identity(c.definition())?));
        }
        output.push_str("_=>Err(\"prepared executor identity mismatch\".into()),}}\n");
    }
    output.push_str("}\n");
    Ok(output)
}

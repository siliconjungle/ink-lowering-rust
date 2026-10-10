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
        }
        output.push_str(r#"pub fn input(t:ink_core::logic::Term,depth:usize)->ink_core::LangResult<Value>{
if depth>128{return Err("native representation value depth".into());}
Ok(match t{ink_core::logic::Term::Bool(x)=>Value::Bool(x),ink_core::logic::Term::U64(x)=>Value::U64(x),ink_core::logic::Term::Construct{datatype,constructor,arguments}=>Value::Data{datatype,constructor,arguments:arguments.into_iter().map(|x|input(x,depth+1)).collect::<ink_core::LangResult<_>>()?},_=>return Err("native input is not a value".into())})}
pub fn output(t:Value)->ink_core::logic::Term{match t{Value::Bool(x)=>ink_core::logic::Term::Bool(x),Value::U64(x)=>ink_core::logic::Term::U64(x),Value::Data{datatype,constructor,arguments}=>ink_core::logic::Term::Construct{datatype,constructor,arguments:arguments.into_iter().map(output).collect()}}}
"#);
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
    output.push_str(
        "_=>Err(\"native executor does not contain the pinned representation\".into()),}}}\n",
    );
    Ok(output)
}

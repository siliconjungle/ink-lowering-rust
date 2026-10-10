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
    let mut output = String::new();
    for (i, d) in definitions.iter().enumerate() {
        let emitted = crate::definition_native::lower(d)?;
        output.push_str(&format!("mod definition_{i} {{\n{}\n}}\n", emitted.source));
    }
    output.push_str("pub struct Native;\nimpl ink_runtime::representation::Executor for Native {\nfn execute(&self, definition:&ink_core::definition::CheckedDefinition, _context:&ink_core::logic::Context,function:&str,args:Vec<ink_core::logic::Term>)->ink_core::LangResult<ink_core::logic::Term>{\nlet executable=ink_core::registry::identity(&(\"ink-sealed-executable-v1\",definition.bundle_sha256(),definition.exports(),definition.choices()))?;\nmatch executable.as_str(){\n");
    for (i, d) in definitions.iter().enumerate() {
        output.push_str(&format!(
            "{:?}=>{{\nuse definition_{i}::Value;\n",
            executable_identity(d)?
        ));
        output.push_str(r#"fn input(t:ink_core::logic::Term,depth:usize)->ink_core::LangResult<Value>{
if depth>128{return Err("native representation value depth".into());}
Ok(match t{ink_core::logic::Term::Bool(x)=>Value::Bool(x),ink_core::logic::Term::U64(x)=>Value::U64(x),ink_core::logic::Term::Construct{datatype,constructor,arguments}=>Value::Data{datatype,constructor,arguments:arguments.into_iter().map(|x|input(x,depth+1)).collect::<ink_core::LangResult<_>>()?},_=>return Err("native input is not a value".into())})}
fn output(t:Value)->ink_core::logic::Term{match t{Value::Bool(x)=>ink_core::logic::Term::Bool(x),Value::U64(x)=>ink_core::logic::Term::U64(x),Value::Data{datatype,constructor,arguments}=>ink_core::logic::Term::Construct{datatype,constructor,arguments:arguments.into_iter().map(output).collect()}}}
let values=args.into_iter().map(|x|input(x,0)).collect::<ink_core::LangResult<Vec<_>>>()?;
"#);
        output.push_str(&format!(
            "Ok(output(definition_{i}::invoke(function,&values).map_err(str::to_owned)?))\n}},\n"
        ));
    }
    output.push_str(
        "_=>Err(\"native executor does not contain the pinned definition\".into()),\n}\n}\n}\n",
    );
    Ok(output)
}

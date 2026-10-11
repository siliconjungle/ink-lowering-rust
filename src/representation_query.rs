//! Compile-time elimination of read-only observation envelopes by existing
//! definitional computation. No cache name, layout recogniser or new proof rule.
use ink_core::{
    logic::{Branch, Declaration, Sort, Term},
    representation::CheckedRepresentation,
    syntax::ActionKind,
    LangResult,
};
use std::collections::{BTreeMap, BTreeSet};

pub(crate) fn binders(
    t: &Term,
    env: &BTreeMap<String, String>,
    used: &mut BTreeSet<String>,
    serial: &mut usize,
) -> Term {
    let go = |t: &Term, used: &mut BTreeSet<String>, serial: &mut usize| {
        binders(t, env, used, serial)
    };
    match t {
        Term::Var(n) => Term::Var(env.get(n).unwrap_or(n).clone()),
        Term::Construct {
            datatype,
            constructor,
            arguments,
        } => Term::Construct {
            datatype: datatype.clone(),
            constructor: *constructor,
            arguments: arguments.iter().map(|a| go(a, used, serial)).collect(),
        },
        Term::Call {
            function,
            arguments,
        } => Term::Call {
            function: function.clone(),
            arguments: arguments.iter().map(|a| go(a, used, serial)).collect(),
        },
        Term::SelfCall(arguments) => {
            Term::SelfCall(arguments.iter().map(|a| go(a, used, serial)).collect())
        }
        Term::Binary { op, left, right } => Term::Binary {
            op: op.clone(),
            left: Box::new(go(left, used, serial)),
            right: Box::new(go(right, used, serial)),
        },
        Term::If {
            condition,
            on_true,
            on_false,
        } => Term::If {
            condition: Box::new(go(condition, used, serial)),
            on_true: Box::new(go(on_true, used, serial)),
            on_false: Box::new(go(on_false, used, serial)),
        },
        Term::Match {
            scrutinee,
            branches,
        } => Term::Match {
            scrutinee: Box::new(go(scrutinee, used, serial)),
            branches: branches
                .iter()
                .map(|b| {
                    let mut local = env.clone();
                    let bindings = b
                        .bindings
                        .iter()
                        .map(|n| {
                            let fresh = loop {
                                let n = format!("inkQueryBinder{}", *serial);
                                *serial += 1;
                                if used.insert(n.clone()) {
                                    break n;
                                }
                            };
                            local.insert(n.clone(), fresh.clone());
                            fresh
                        })
                        .collect();
                    Branch {
                        bindings,
                        body: binders(&b.body, &local, used, serial),
                    }
                })
                .collect(),
        },
        _ => t.clone(),
    }
}

/// Literal query bodies for which the already checked observation computes to
/// an unchanged logical state/version and no events. The old physical state
/// remains related to that logical state; computing a replacement is redundant.
/// Backend emission/codec correspondence remains a trusted compiler boundary.
pub fn declarations(checked: &CheckedRepresentation) -> LangResult<BTreeMap<String, Declaration>> {
    // Normalisation uses internal '$' binders. Rename them with lexical scope
    // before passing the residual term back through the ordinary type checker.
    fn reply(
        t: &Term,
        logical: &Term,
        version: &Term,
        observation: &str,
        events: &str,
    ) -> Option<Term> {
        match t {
            Term::Construct {
                datatype,
                constructor: 0,
                arguments,
            } if datatype == observation
                && arguments.len() == 5
                && arguments[1] == Term::Bool(false)
                && &arguments[2] == version
                && &arguments[3] == logical
                && arguments[4]
                    == (Term::Construct {
                        datatype: events.into(),
                        constructor: 0,
                        arguments: vec![],
                    }) =>
            {
                Some(arguments[0].clone())
            }
            Term::If {
                condition,
                on_true,
                on_false,
            } => Some(Term::If {
                condition: condition.clone(),
                on_true: Box::new(reply(on_true, logical, version, observation, events)?),
                on_false: Box::new(reply(on_false, logical, version, observation, events)?),
            }),
            Term::Match {
                scrutinee,
                branches,
            } => Some(Term::Match {
                scrutinee: scrutinee.clone(),
                branches: branches
                    .iter()
                    .map(|b| {
                        Some(Branch {
                            bindings: b.bindings.clone(),
                            body: reply(&b.body, logical, version, observation, events)?,
                        })
                    })
                    .collect::<Option<Vec<_>>>()?,
            }),
            _ => None,
        }
    }
    let ds = checked.definition().executable_declarations()?;
    let Sort::Data(physical) = &checked.plan().physical_state else {
        return Ok(BTreeMap::new());
    };
    let Declaration::Datatype { constructors } = &ds[physical] else {
        return Err("physical datatype".into());
    };
    let mut out = BTreeMap::new();
    for source in &checked.module().program().actions {
        if source.kind != ActionKind::Query {
            continue;
        }
        let a = &checked.plan().actions[&source.name];
        let Declaration::Function { params, .. } = &ds[&a.execute] else {
            return Err("query function".into());
        };
        let Sort::Data(observation) = &checked.projection().actions[&source.name].result else {
            return Err("query observation".into());
        };
        let mut branches = vec![];
        for (tag, c) in constructors.iter().enumerate() {
            let bindings = (0..c.fields.len())
                .map(|i| format!("__ink_query_{tag}_{i}"))
                .collect::<Vec<_>>();
            let mut env = params[1..].to_vec();
            env.extend(bindings.iter().cloned().zip(c.fields.iter().map(|s| {
                if *s == Sort::SelfType {
                    Sort::Data(physical.clone())
                } else {
                    s.clone()
                }
            })));
            let state = Term::Construct {
                datatype: physical.clone(),
                constructor: tag,
                arguments: bindings.iter().cloned().map(Term::Var).collect(),
            };
            let mut args = vec![state.clone()];
            args.extend(params[1..].iter().map(|p| Term::Var(p.0.clone())));
            let execute = Term::Call {
                function: a.execute.clone(),
                arguments: args,
            };
            let observed = Term::Call {
                function: a.observe.clone(),
                arguments: vec![execute],
            };
            let logical = Term::Call {
                function: checked.plan().decode.clone(),
                arguments: vec![state],
            };
            // A bounded normalisation failure merely retains literal execution.
            let (Ok(observed), Ok(logical)) = (
                checked.context().evaluate(&env, &observed),
                checked.context().evaluate(&env, &logical),
            ) else {
                break;
            };
            let Some(body) = reply(
                &observed,
                &logical,
                &Term::Var(params[1].0.clone()),
                observation,
                &checked.projection().events,
            ) else {
                break;
            };
            branches.push(Branch { bindings, body });
        }
        if branches.len() != constructors.len() {
            continue;
        }
        let result = checked.projection().types
            [&serde_json::to_string(&source.result).map_err(|e| e.to_string())?]
            .clone();
        let body = Term::Match {
            scrutinee: Box::new(Term::Var(params[0].0.clone())),
            branches,
        };
        let body = binders(
            &body,
            &BTreeMap::new(),
            &mut params.iter().map(|p| p.0.clone()).collect(),
            &mut 0,
        );
        // Recheck the residual term's type before handing it to literal emitters.
        checked.context().evaluate(params, &body)?;
        out.insert(
            format!("q_{}", a.execute),
            Declaration::Function {
                params: params.clone(),
                result,
                body,
                recursive: None,
            },
        );
    }
    Ok(out)
}

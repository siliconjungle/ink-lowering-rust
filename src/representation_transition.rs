//! Erase private logical observations when an independent physical next-state
//! carrier supplies publication. This is compiler liveness, not admission of a
//! new algorithm. Unknown envelopes or normalization failures keep the baseline.
use ink_core::{
    logic::{Branch, Declaration, Sort, Term},
    representation::CheckedRepresentation,
    LangResult,
};
use std::collections::BTreeMap;

pub fn declarations(checked: &CheckedRepresentation) -> LangResult<BTreeMap<String, Declaration>> {
    let ds = checked.definition().executable_declarations()?;
    let mut out = BTreeMap::new();
    let empty = Term::Construct {
        datatype: checked.projection().state.clone(),
        constructor: 0,
        arguments: checked
            .projection()
            .tables
            .iter()
            .map(|t| Term::Construct {
                datatype: t.datatype.clone(),
                constructor: 0,
                arguments: vec![],
            })
            .collect(),
    };
    fn erase(t: &Term, carrier: &str, observation: &str, empty: &Term) -> Option<Term> {
        match t {
            Term::Construct {
                datatype,
                constructor: 0,
                arguments,
            } if datatype == carrier && arguments.len() == 2 => {
                // Preserve the physical component exactly, including any nested
                // values that happen to use a source observation datatype.
                Some(Term::Construct {
                    datatype: datatype.clone(),
                    constructor: 0,
                    arguments: vec![
                        arguments[0].clone(),
                        erase(&arguments[1], observation, observation, empty)?,
                    ],
                })
            }
            Term::Construct {
                datatype,
                constructor,
                arguments,
            } if datatype == observation => {
                let index = match (*constructor, arguments.len()) {
                    (0, 5) => 3,
                    (1, 3) => 2,
                    _ => return None,
                };
                let mut args = arguments.clone();
                args[index] = empty.clone();
                Some(Term::Construct {
                    datatype: datatype.clone(),
                    constructor: *constructor,
                    arguments: args,
                })
            }
            Term::If {
                condition,
                on_true,
                on_false,
            } => Some(Term::If {
                condition: condition.clone(),
                on_true: Box::new(erase(on_true, carrier, observation, empty)?),
                on_false: Box::new(erase(on_false, carrier, observation, empty)?),
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
                            body: erase(&b.body, carrier, observation, empty)?,
                        })
                    })
                    .collect::<Option<_>>()?,
            }),
            _ => None,
        }
    }
    for source in &checked.module().program().actions {
        let a = &checked.plan().actions[&source.name];
        let Sort::Data(result_id) = &a.result else {
            continue;
        };
        let Sort::Data(observation) = &checked.projection().actions[&source.name].result else {
            continue;
        };
        let Declaration::Datatype { constructors } = &ds[result_id] else {
            continue;
        };
        if constructors.len() != 1
            || constructors[0].fields
                != [
                    checked.plan().physical_state.clone(),
                    Sort::Data(observation.clone()),
                ]
        {
            continue;
        }
        let env = vec![
            ("__next".into(), checked.plan().physical_state.clone()),
            ("__observe".into(), Sort::Data(observation.clone())),
        ];
        let result = Term::Construct {
            datatype: result_id.clone(),
            constructor: 0,
            arguments: vec![Term::Var("__next".into()), Term::Var("__observe".into())],
        };
        // Check the two eliminators independently; names/layout metadata cannot
        // establish that the discarded field has no consumers.
        let next = checked.context().evaluate(
            &env,
            &Term::Call {
                function: a.next.clone(),
                arguments: vec![result.clone()],
            },
        );
        let observed = checked.context().evaluate(
            &env,
            &Term::Call {
                function: a.observe.clone(),
                arguments: vec![result],
            },
        );
        if next.as_ref().ok() != Some(&Term::Var("__next".into()))
            || observed.as_ref().ok() != Some(&Term::Var("__observe".into()))
        {
            continue;
        }
        let Declaration::Function {
            params,
            result,
            recursive: None,
            ..
        } = &ds[&a.execute]
        else {
            continue;
        };
        let Sort::Data(physical_id) = &checked.plan().physical_state else {
            continue;
        };
        let Declaration::Datatype { constructors } = &ds[physical_id] else {
            continue;
        };
        let mut branches = vec![];
        for (tag, constructor) in constructors.iter().enumerate() {
            let bindings = (0..constructor.fields.len())
                .map(|i| format!("__physical_{tag}_{i}"))
                .collect::<Vec<_>>();
            let bound = Term::Construct {
                datatype: physical_id.clone(),
                constructor: tag,
                arguments: bindings.iter().cloned().map(Term::Var).collect(),
            };
            let mut scope = params[1..].to_vec();
            scope.extend(
                bindings
                    .iter()
                    .cloned()
                    .zip(constructor.fields.iter().cloned()),
            );
            let mut args = vec![bound];
            args.extend(params[1..].iter().map(|(n, _)| Term::Var(n.clone())));
            let Ok(normal) = checked.context().evaluate(
                &scope,
                &Term::Call {
                    function: a.execute.clone(),
                    arguments: args,
                },
            ) else {
                break;
            };
            let Some(erased) = erase(&normal, result_id, observation, &empty) else {
                break;
            };
            branches.push(Branch {
                bindings,
                body: erased,
            });
        }
        if branches.len() != constructors.len() {
            continue;
        }
        let body = Term::Match {
            scrutinee: Box::new(Term::Var(params[0].0.clone())),
            branches,
        };
        let body = crate::representation_query::binders(
            &body,
            &BTreeMap::new(),
            &mut params.iter().map(|(n, _)| n.clone()).collect(),
            &mut 0,
        );
        checked.context().evaluate(params, &body)?;
        out.insert(
            format!("t_{}", a.execute),
            Declaration::Function {
                params: params.clone(),
                result: result.clone(),
                body,
                recursive: None,
            },
        );
    }
    Ok(out)
}

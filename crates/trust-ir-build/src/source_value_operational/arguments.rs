use super::execution::{Inputs, run_prefix, select, states, successful};
use super::*;

fn list_cases(
    assembler: &mut Assembler<'_>,
    value: Expr,
    proposition: bool,
    motive: impl Fn(Expr) -> Expr,
    nil: impl FnOnce(&mut Assembler<'_>) -> Result<Expr>,
    cons: impl FnOnce(&mut Assembler<'_>, Expr, Expr) -> Result<Expr>,
) -> Result<Expr> {
    let l = assembler.local(app("IRList", [c("IRScalar")]))?;
    let motive_expr = l.lam(motive(l.term().clone()));
    let base = nil(assembler)?;
    let head = assembler.local(c("IRScalar"))?;
    let tail = assembler.local(app("IRList", [c("IRScalar")]))?;
    let ih = assembler.local(motive(tail.term().clone()))?;
    let branch = cons(assembler, head.term().clone(), tail.term().clone())?;
    Ok(Expr::apps(
        Expr::const_(
            Name::from_string("IRList.rec"),
            vec![if proposition {
                Level::zero()
            } else {
                Level::succ(Level::zero())
            }],
        ),
        [
            c("IRScalar"),
            motive_expr,
            base,
            head.lam(tail.lam(ih.lam(branch))),
            value,
        ],
    ))
}

fn scalar_cases(
    assembler: &mut Assembler<'_>,
    value: Expr,
    proposition: bool,
    motive: impl Fn(Expr) -> Expr,
    mut branch: impl FnMut(&mut Assembler<'_>, &str, Expr, Option<Expr>) -> Result<Expr>,
) -> Result<Expr> {
    let v = assembler.local(c("IRScalar"))?;
    let mut arguments = vec![v.lam(motive(v.term().clone()))];
    for (name, fields) in [
        ("undef_", vec![]),
        ("bool_", vec!["Bool"]),
        ("int_", vec!["Nat"]),
        ("float_", vec!["Nat"]),
        ("unit_", vec![]),
        ("ptr_", vec!["Nat"]),
        ("nullptr_", vec![]),
        ("fat_", vec!["Nat", "Nat"]),
        ("fnptr_", vec!["Nat"]),
        ("aggv", vec!["IRScalar"]),
        ("vnil", vec![]),
        ("vcons", vec!["IRScalar", "IRScalar"]),
    ] {
        let mut parameters = Vec::new();
        let mut values = Vec::new();
        for field in &fields {
            let local = assembler.local(c(field))?;
            values.push(local.term().clone());
            parameters.push(local);
        }
        // The actual recursor places all recursive hypotheses AFTER its fields.
        for (field, ty) in values.iter().zip(&fields) {
            if *ty == "IRScalar" {
                parameters.push(assembler.local(motive(field.clone()))?);
            }
        }
        let constructed = app(&format!("IRScalar.{name}"), values.clone());
        let body = branch(
            assembler,
            name,
            constructed,
            if name == "int_" {
                Some(values[0].clone())
            } else {
                None
            },
        )?;
        arguments.push(
            parameters
                .iter()
                .rev()
                .fold(body, |body, local| local.lam(body)),
        );
    }
    arguments.push(value);
    Ok(Expr::apps(
        Expr::const_(
            Name::from_string("IRScalar.rec"),
            vec![if proposition {
                Level::zero()
            } else {
                Level::succ(Level::zero())
            }],
        ),
        arguments,
    ))
}

fn args(x: Expr, y: Expr) -> Expr {
    list("IRScalar", [int(x), int(y)])
}
fn fit(profile: ScalarProfile, x: Expr) -> Expr {
    app("ir_nat_ltb", [x, profile.limit()])
}
fn pair_result(subject: &Subject<'_>, input: &Inputs, x: Expr, y: Expr) -> Expr {
    choose(
        input.model.config_type(),
        fit(subject.profile, x.clone()),
        choose(
            input.model.config_type(),
            fit(subject.profile, y.clone()),
            select(
                input.fuel.clone(),
                &states(subject, input, x, y),
                input.model.config_type(),
            ),
            input.bad("IRFault.bad_field"),
        ),
        input.bad("IRFault.bad_field"),
    )
}

// Exact arity and constructor decisions, independently of the byte evaluator.
// No runtime operation, catalog or initializer is called in this projection.
struct Expected {
    function: Expr,
    admitted: Expr,
}

fn expected_function(
    subject: &Subject<'_>,
    input: &Inputs,
    assembler: &mut Assembler<'_>,
) -> Result<Expected> {
    let values = assembler.local(app("IRList", [c("IRScalar")]))?;
    let ty = input.model.config_type();
    let result = list_cases(
        assembler,
        values.term().clone(),
        false,
        |_| ty.clone(),
        |_| Ok(input.bad("IRFault.bad_field")),
        |a, x, tail| {
            list_cases(
                a,
                tail,
                false,
                |_| ty.clone(),
                |_| Ok(input.bad("IRFault.bad_field")),
                |a, y, more| {
                    list_cases(
                        a,
                        more,
                        false,
                        |_| ty.clone(),
                        |a| {
                            scalar_cases(
                                a,
                                x.clone(),
                                false,
                                |_| ty.clone(),
                                |a, name, _, left| {
                                    if name != "int_" {
                                        return Ok(input.bad("IRFault.bad_field"));
                                    }
                                    scalar_cases(
                                        a,
                                        y.clone(),
                                        false,
                                        |_| ty.clone(),
                                        |_, name, _, right| {
                                            if name != "int_" {
                                                return Ok(input.bad("IRFault.bad_field"));
                                            }
                                            Ok(pair_result(
                                                subject,
                                                input,
                                                left.clone().unwrap(),
                                                right.unwrap(),
                                            ))
                                        },
                                    )
                                },
                            )
                        },
                        |_, _, _| Ok(input.bad("IRFault.bad_field")),
                    )
                },
            )
        },
    )?;
    Ok(Expected {
        admitted: values.lam(result.clone()),
        function: values.lam(choose(
            ty,
            input.memory_guard(),
            result,
            input.bad("IRFault.bad_addr"),
        )),
    })
}

fn initial_guarded(subject: &Subject<'_>, input: &Inputs, arguments: Expr) -> Expr {
    let guard = app(
        "ir_byte_values_match_v1",
        [
            input.model.context().clone(),
            list(
                "IRTy",
                [subject.profile.scalar_type(), subject.profile.scalar_type()],
            ),
            arguments.clone(),
        ],
    );
    // Arity is retained independently of value typing, as in the real init.
    let guard = app(
        "Bool.and",
        [
            app(
                "ir_nat_eqb",
                [
                    nat(2),
                    app("ir_byte_length_v1", [c("IRScalar"), arguments.clone()]),
                ],
            ),
            guard,
        ],
    );
    choose(
        input.model.config_type(),
        guard,
        input.current(subject, arguments).running(&input.model),
        input.bad("IRFault.bad_field"),
    )
}
fn in_memory(
    subject: &Subject<'_>,
    input: &Inputs,
    assembler: &mut Assembler<'_>,
    arguments: Expr,
    memory: &PendingEquality,
) -> Result<PendingEquality> {
    let branch = initial_guarded(subject, input, arguments.clone());
    let proof = mapped(
        assembler,
        memory.clone(),
        input.model.config_type(),
        |flag| {
            choose(
                input.model.config_type(),
                flag,
                branch.clone(),
                input.bad("IRFault.bad_addr"),
            )
        },
    )?;
    assembler.convert_endpoints(proof, input.initial(subject, arguments), branch)
}
fn expected_in_memory(
    input: &Inputs,
    assembler: &mut Assembler<'_>,
    expected: &Expected,
    arguments: Expr,
    memory: &PendingEquality,
) -> Result<PendingEquality> {
    // ScopedLocal lambdas are deferred binders: retain ordinary application and
    // let the owning Scope perform capture-safe closing, never beta-substitute
    // an unclosed binder's raw body.
    let raw = Expr::app(expected.function.clone(), arguments.clone());
    let branch = Expr::app(expected.admitted.clone(), arguments);
    let proof = mapped(
        assembler,
        memory.clone(),
        input.model.config_type(),
        |flag| {
            choose(
                input.model.config_type(),
                flag,
                branch.clone(),
                input.bad("IRFault.bad_addr"),
            )
        },
    )?;
    let right = choose(
        input.model.config_type(),
        memory.right().clone(),
        branch,
        input.bad("IRFault.bad_addr"),
    );
    assembler.convert_endpoints(proof, raw, right)
}

fn halted_run(input: &Inputs, fuel: Expr, state: Expr) -> PendingEquality {
    let fields = state.get_app_args();
    PendingEquality::candidate(
        input.model.config_type(),
        input.run(fuel.clone(), state.clone()),
        state.clone(),
        app(
            "ir_byte_run_halted_v1",
            [
                input.model.world_type().clone(),
                input.model.context().clone(),
                input.model.providers().clone(),
                fields[1].clone(),
                fields[2].clone(),
                fuel,
            ],
        ),
    )
}

fn goal(subject: &Subject<'_>, input: &Inputs, expected: &Expected, arguments: Expr) -> Expr {
    eq(
        input.model.config_type(),
        input.run(
            input.fuel.clone(),
            input.initial(subject, arguments.clone()),
        ),
        Expr::app(expected.function.clone(), arguments),
    )
}
fn finish(
    subject: &Subject<'_>,
    input: &Inputs,
    assembler: &mut Assembler<'_>,
    expected: &Expected,
    arguments: Expr,
    initial: PendingEquality,
    middle: PendingEquality,
    normalized_expected: PendingEquality,
) -> Result<Expr> {
    let mapped = mapped(assembler, initial, input.model.config_type(), |state| {
        input.run(input.fuel.clone(), state)
    })?;
    let equation = assembler.compose(mapped, middle)?;
    let equation = assembler.compose(equation, symm(&normalized_expected))?;
    let final_goal = goal(subject, input, expected, arguments);
    let fields = final_goal.get_app_args();
    Ok(assembler
        .convert_endpoints(equation, fields[1].clone(), fields[2].clone())?
        .term()
        .clone())
}
fn malformed(
    subject: &Subject<'_>,
    input: &Inputs,
    assembler: &mut Assembler<'_>,
    expected: &Expected,
    arguments: Expr,
    memory: &PendingEquality,
) -> Result<Expr> {
    malformed_with_guard(subject, input, assembler, expected, arguments, memory, None)
}
fn malformed_with_guard(
    subject: &Subject<'_>,
    input: &Inputs,
    assembler: &mut Assembler<'_>,
    expected: &Expected,
    arguments: Expr,
    memory: &PendingEquality,
    guard: Option<PendingEquality>,
) -> Result<Expr> {
    let initial = in_memory(subject, input, assembler, arguments.clone(), memory)?;
    let initial = if let Some(guard) = guard {
        let mapped = mapped(assembler, guard, input.model.config_type(), |flag| {
            choose(
                input.model.config_type(),
                flag,
                input
                    .current(subject, arguments.clone())
                    .running(&input.model),
                input.bad("IRFault.bad_field"),
            )
        })?;
        let mapped = assembler.convert_endpoints(
            mapped,
            initial.right().clone(),
            input.bad("IRFault.bad_field"),
        )?;
        assembler.compose(initial, mapped)?
    } else {
        assembler.convert_endpoints(
            initial,
            input.initial(subject, arguments.clone()),
            input.bad("IRFault.bad_field"),
        )?
    };
    let projected = expected_in_memory(input, assembler, expected, arguments.clone(), memory)?;
    let projected = assembler.convert_endpoints(
        projected,
        Expr::app(expected.function.clone(), arguments.clone()),
        input.bad("IRFault.bad_field"),
    )?;
    finish(
        subject,
        input,
        assembler,
        expected,
        arguments,
        initial,
        halted_run(input, input.fuel.clone(), input.bad("IRFault.bad_field")),
        projected,
    )
}

fn ints(
    subject: &Subject<'_>,
    environment: &Environment,
    input: &Inputs,
    assembler: &mut Assembler<'_>,
    expected: &Expected,
    x: Expr,
    y: Expr,
    memory: &PendingEquality,
) -> Result<Expr> {
    let arguments = args(x.clone(), y.clone());
    let proposition = goal(subject, input, expected, arguments.clone());
    let prove_bad = |a: &mut Assembler<'_>,
                     xf: &PendingEquality,
                     yf: Option<&PendingEquality>|
     -> Result<PendingProof> {
        let initial = in_memory(subject, input, a, arguments.clone(), memory)?;
        let yflag = fit(subject.profile, y.clone());
        let start = input
            .current(subject, arguments.clone())
            .running(&input.model);
        let branch = |gx: Expr, gy: Expr| {
            choose(
                input.model.config_type(),
                app("Bool.and", [gx, app("Bool.and", [gy, c("Bool.true")])]),
                start.clone(),
                input.bad("IRFault.bad_field"),
            )
        };
        let first = mapped(a, xf.clone(), input.model.config_type(), |gx| {
            branch(gx, yflag.clone())
        })?;
        let first = a.convert_endpoints(
            first,
            initial.right().clone(),
            branch(xf.right().clone(), yflag.clone()),
        )?;
        let initial = a.compose(initial, first)?;
        let initial = if let Some(yf) = yf {
            let second = mapped(a, yf.clone(), input.model.config_type(), |gy| {
                branch(xf.right().clone(), gy)
            })?;
            a.compose(initial, second)?
        } else {
            initial
        };
        let initial = a.convert_endpoints(
            initial,
            input.initial(subject, arguments.clone()),
            input.bad("IRFault.bad_field"),
        )?;
        let projected = expected_in_memory(input, a, expected, arguments.clone(), memory)?;
        let pair = |gx: Expr, gy: Expr| {
            choose(
                input.model.config_type(),
                gx,
                choose(
                    input.model.config_type(),
                    gy,
                    select(
                        input.fuel.clone(),
                        &states(subject, input, x.clone(), y.clone()),
                        input.model.config_type(),
                    ),
                    input.bad("IRFault.bad_field"),
                ),
                input.bad("IRFault.bad_field"),
            )
        };
        let first = mapped(a, xf.clone(), input.model.config_type(), |gx| {
            pair(gx, yflag.clone())
        })?;
        let first = a.convert_endpoints(
            first,
            projected.right().clone(),
            pair(xf.right().clone(), yflag.clone()),
        )?;
        let projected = a.compose(projected, first)?;
        let projected = if let Some(yf) = yf {
            let second = mapped(a, yf.clone(), input.model.config_type(), |gy| {
                pair(xf.right().clone(), gy)
            })?;
            a.compose(projected, second)?
        } else {
            projected
        };
        let projected = a.convert_endpoints(
            projected,
            Expr::app(expected.function.clone(), arguments.clone()),
            input.bad("IRFault.bad_field"),
        )?;
        let proof = finish(
            subject,
            input,
            a,
            expected,
            arguments.clone(),
            initial,
            halted_run(input, input.fuel.clone(), input.bad("IRFault.bad_field")),
            projected,
        )?;
        Ok(PendingProof::candidate(proposition.clone(), proof))
    };
    let proof = assembler.branch_proposition(
        fit(subject.profile, x.clone()),
        proposition.clone(),
        |a, xf| prove_bad(a, &xf, None),
        |a, xf| {
            a.branch_proposition(
                fit(subject.profile, y.clone()),
                proposition.clone(),
                |a, yf| prove_bad(a, &xf, Some(&yf)),
                |a, yf| {
                    let hx = PendingProof::candidate(
                        subject.profile.bound(x.clone()),
                        app(
                            "ir_byte_separation_lt_of_ltb_v1",
                            [x.clone(), subject.profile.limit(), xf.term().clone()],
                        ),
                    );
                    let hy = PendingProof::candidate(
                        subject.profile.bound(y.clone()),
                        app(
                            "ir_byte_separation_lt_of_ltb_v1",
                            [y.clone(), subject.profile.limit(), yf.term().clone()],
                        ),
                    );
                    let (states, equations) = successful(
                        subject,
                        environment,
                        a,
                        input,
                        x.clone(),
                        y.clone(),
                        hx,
                        hy,
                        memory.clone(),
                    )?;
                    let running =
                        run_prefix(a, input, input.fuel.clone(), &states, &equations[1..])?;
                    let projected =
                        expected_in_memory(input, a, expected, arguments.clone(), memory)?;
                    let pair = |gx: Expr, gy: Expr| {
                        choose(
                            input.model.config_type(),
                            gx,
                            choose(
                                input.model.config_type(),
                                gy,
                                select(input.fuel.clone(), &states, input.model.config_type()),
                                input.bad("IRFault.bad_field"),
                            ),
                            input.bad("IRFault.bad_field"),
                        )
                    };
                    let first = mapped(a, xf.clone(), input.model.config_type(), |gx| {
                        pair(gx, fit(subject.profile, y.clone()))
                    })?;
                    let first = a.convert_endpoints(
                        first,
                        projected.right().clone(),
                        pair(c("Bool.true"), fit(subject.profile, y.clone())),
                    )?;
                    let projected = a.compose(projected, first)?;
                    let second = mapped(a, yf, input.model.config_type(), |gy| {
                        pair(c("Bool.true"), gy)
                    })?;
                    let projected = a.compose(projected, second)?;
                    let projected = a.convert_endpoints(
                        projected,
                        Expr::app(expected.function.clone(), arguments.clone()),
                        running.right().clone(),
                    )?;
                    let proof = finish(
                        subject,
                        input,
                        a,
                        expected,
                        arguments.clone(),
                        equations[0].clone(),
                        running,
                        projected,
                    )?;
                    Ok(PendingProof::candidate(proposition.clone(), proof))
                },
            )
        },
    )?;
    Ok(proof.term().clone())
}

fn admitted_args(
    subject: &Subject<'_>,
    environment: &Environment,
    input: &Inputs,
    assembler: &mut Assembler<'_>,
    expected: &Expected,
    arguments: Expr,
    memory: &PendingEquality,
) -> Result<Expr> {
    list_cases(
        assembler,
        arguments,
        true,
        |arguments| goal(subject, input, expected, arguments),
        |a| malformed(subject, input, a, expected, list("IRScalar", []), memory),
        |a, x, tail| {
            let outer = |tail| app("IRList.cons", [c("IRScalar"), x.clone(), tail]);
            list_cases(
                a,
                tail,
                true,
                |tail| goal(subject, input, expected, outer(tail)),
                |a| {
                    malformed(
                        subject,
                        input,
                        a,
                        expected,
                        outer(list("IRScalar", [])),
                        memory,
                    )
                },
                |a, y, more| {
                    let outer = |more| outer(app("IRList.cons", [c("IRScalar"), y.clone(), more]));
                    list_cases(
                        a,
                        more,
                        true,
                        |more| goal(subject, input, expected, outer(more)),
                        |a| {
                            scalar_cases(
                                a,
                                x.clone(),
                                true,
                                |x| {
                                    goal(subject, input, expected, list("IRScalar", [x, y.clone()]))
                                },
                                |a, name, left, xint| {
                                    if name != "int_" {
                                        return malformed(
                                            subject,
                                            input,
                                            a,
                                            expected,
                                            list("IRScalar", [left, y.clone()]),
                                            memory,
                                        );
                                    }
                                    scalar_cases(
                                        a,
                                        y.clone(),
                                        true,
                                        |y| {
                                            goal(
                                                subject,
                                                input,
                                                expected,
                                                list("IRScalar", [left.clone(), y]),
                                            )
                                        },
                                        |a, name, right, yint| {
                                            if name != "int_" {
                                                let xfit =
                                                    fit(subject.profile, xint.clone().unwrap());
                                                let guard = PendingEquality::candidate(
                                                    c("Bool"),
                                                    app(
                                                        "Bool.and",
                                                        [xfit.clone(), c("Bool.false")],
                                                    ),
                                                    c("Bool.false"),
                                                    app("Bool.and_false", [xfit]),
                                                );
                                                return malformed_with_guard(
                                                    subject,
                                                    input,
                                                    a,
                                                    expected,
                                                    list("IRScalar", [left.clone(), right]),
                                                    memory,
                                                    Some(guard),
                                                );
                                            }
                                            ints(
                                                subject,
                                                environment,
                                                input,
                                                a,
                                                expected,
                                                xint.clone().unwrap(),
                                                yint.unwrap(),
                                                memory,
                                            )
                                        },
                                    )
                                },
                            )
                        },
                        |a, third, tail| {
                            let arguments = outer(app("IRList.cons", [c("IRScalar"), third, tail]));
                            let length =
                                app("ir_byte_length_v1", [c("IRScalar"), arguments.clone()]);
                            // Actual eqb peels once and uses subtraction. Its existing
                            // checked walk bridge proves 2 != 3+length(tail), without a
                            // finite-tail, arity or successful-entry hypothesis.
                            let arity = PendingEquality::candidate(
                                c("Bool"),
                                app("ir_nat_eqb", [nat(2), length.clone()]),
                                app("ir_nat_eqb_walk", [nat(2), length.clone()]),
                                app("ir_nat_eqb_walk_eq", [nat(2), length]),
                            );
                            let arity = a.convert_endpoints(
                                arity.clone(),
                                arity.left().clone(),
                                c("Bool.false"),
                            )?;
                            let values_match = app(
                                "ir_byte_values_match_v1",
                                [
                                    input.model.context().clone(),
                                    list(
                                        "IRTy",
                                        [
                                            subject.profile.scalar_type(),
                                            subject.profile.scalar_type(),
                                        ],
                                    ),
                                    arguments.clone(),
                                ],
                            );
                            let guard = mapped(a, arity, c("Bool"), |flag| {
                                app("Bool.and", [flag, values_match.clone()])
                            })?;
                            let guard = a.convert_endpoints(
                                guard.clone(),
                                guard.left().clone(),
                                c("Bool.false"),
                            )?;
                            malformed_with_guard(
                                subject,
                                input,
                                a,
                                expected,
                                arguments,
                                memory,
                                Some(guard),
                            )
                        },
                    )
                },
            )
        },
    )
}

fn typed_bound(profile: ScalarProfile, value: Expr) -> PendingProof {
    let word = app(profile.to_nat(), [value.clone()]);
    let fin = app(
        "BitVec.toFin",
        [nat(profile.bits()), app(profile.to_bitvec(), [value])],
    );
    PendingProof::candidate(
        profile.bound(word),
        Expr::proj(Name::from_string("Fin"), 1, fin),
    )
}

pub(super) fn derive(
    subject: &Subject<'_>,
    environment: &Environment,
) -> Result<(Expr, Expr, Expr, Expr)> {
    let mut scope = LocalScope::new();
    let mut assembler = Assembler::new(&mut scope, subject.limits)?;
    let w = assembler.local(Expr::type_())?;
    let memory = assembler.local(c("IRByteMemoryV1"))?;
    let host = assembler.local(w.term().clone())?;
    let providers = assembler.local(app("IRByteProvidersV1", [w.term().clone()]))?;
    let values = assembler.local(app("IRList", [c("IRScalar")]))?;
    let fuel = assembler.local(c("Nat"))?;
    let input = Inputs {
        model: MachineModel::new(
            w.term().clone(),
            &subject.reflected,
            providers.term().clone(),
        ),
        memory: memory.term().clone(),
        host: host.term().clone(),
        fuel: fuel.term().clone(),
    };
    let expected = expected_function(subject, &input, &mut assembler)?;
    let proposition = goal(subject, &input, &expected, values.term().clone());
    let total = assembler.branch_proposition(
        input.memory_guard(),
        proposition.clone(),
        |a, memory| {
            let branch = initial_guarded(subject, &input, values.term().clone());
            let initial = mapped(a, memory.clone(), input.model.config_type(), |flag| {
                choose(
                    input.model.config_type(),
                    flag,
                    branch.clone(),
                    input.bad("IRFault.bad_addr"),
                )
            })?;
            let initial = a.convert_endpoints(
                initial,
                input.initial(subject, values.term().clone()),
                input.bad("IRFault.bad_addr"),
            )?;
            let projected =
                expected_in_memory(&input, a, &expected, values.term().clone(), &memory)?;
            let projected = a.convert_endpoints(
                projected,
                Expr::app(expected.function.clone(), values.term().clone()),
                input.bad("IRFault.bad_addr"),
            )?;
            let term = finish(
                subject,
                &input,
                a,
                &expected,
                values.term().clone(),
                initial,
                halted_run(&input, input.fuel.clone(), input.bad("IRFault.bad_addr")),
                projected,
            )?;
            Ok(PendingProof::candidate(proposition.clone(), term))
        },
        |a, memory| {
            Ok(PendingProof::candidate(
                proposition.clone(),
                admitted_args(
                    subject,
                    environment,
                    &input,
                    a,
                    &expected,
                    values.term().clone(),
                    &memory,
                )?,
            ))
        },
    )?;
    let parameters = [
        w.clone(),
        memory.clone(),
        host.clone(),
        providers.clone(),
        values,
        fuel.clone(),
    ];
    let total_claim = close(assembler.local_scope(), &parameters, proposition, false)
        .map_err(|e| format!("total claim closure: {e}"))?;
    let total_proof = close(
        assembler.local_scope(),
        &parameters,
        total.term().clone(),
        true,
    )
    .map_err(|e| format!("total proof closure: {e}"))?;
    // Reuse this SAME construction ledger for the derived typed theorem.
    let x = assembler.local(c(subject.profile.uint_name()))?;
    let y = assembler.local(c(subject.profile.uint_name()))?;
    let xn = app(subject.profile.to_nat(), [x.term().clone()]);
    let yn = app(subject.profile.to_nat(), [y.term().clone()]);
    let arguments = args(xn.clone(), yn.clone());
    let raw = PendingEquality::candidate(
        input.model.config_type(),
        input.run(
            input.fuel.clone(),
            input.initial(subject, arguments.clone()),
        ),
        Expr::app(expected.function.clone(), arguments.clone()),
        Expr::apps(
            total_proof.clone(),
            [
                w.term().clone(),
                memory.term().clone(),
                host.term().clone(),
                providers.term().clone(),
                arguments.clone(),
                fuel.term().clone(),
            ],
        ),
    );
    let hx = typed_bound(subject.profile, x.term().clone());
    let hy = typed_bound(subject.profile, y.term().clone());
    let xf = PendingEquality::candidate(
        c("Bool"),
        fit(subject.profile, xn.clone()),
        c("Bool.true"),
        app(
            "ir_byte_ltb_of_lt_v1",
            [xn.clone(), subject.profile.limit(), hx.term().clone()],
        ),
    );
    let yf = PendingEquality::candidate(
        c("Bool"),
        fit(subject.profile, yn.clone()),
        c("Bool.true"),
        app(
            "ir_byte_ltb_of_lt_v1",
            [yn.clone(), subject.profile.limit(), hy.term().clone()],
        ),
    );
    let actual_states = states(subject, &input, xn.clone(), yn.clone());
    let pair = |gx: Expr, gy: Expr| {
        choose(
            input.model.config_type(),
            input.memory_guard(),
            choose(
                input.model.config_type(),
                gx,
                choose(
                    input.model.config_type(),
                    gy,
                    select(
                        input.fuel.clone(),
                        &actual_states,
                        input.model.config_type(),
                    ),
                    input.bad("IRFault.bad_field"),
                ),
                input.bad("IRFault.bad_field"),
            ),
            input.bad("IRFault.bad_addr"),
        )
    };
    let first = mapped(&mut assembler, xf, input.model.config_type(), |gx| {
        pair(gx, fit(subject.profile, yn.clone()))
    })?;
    let first = assembler.convert_endpoints(
        first,
        raw.right().clone(),
        pair(c("Bool.true"), fit(subject.profile, yn.clone())),
    )?;
    let raw = assembler.compose(raw, first)?;
    let second = mapped(&mut assembler, yf, input.model.config_type(), |gy| {
        pair(c("Bool.true"), gy)
    })?;
    let raw = assembler.compose(raw, second)?;
    let source_word = app(
        subject.profile.to_nat(),
        [Expr::apps(
            Expr::const_(subject.source.source().clone(), vec![]),
            [x.term().clone(), y.term().clone()],
        )],
    );
    let source_equation = PendingEquality::candidate(
        c("Nat"),
        source_word.clone(),
        subject.denotation(xn, yn),
        Expr::apps(
            subject.source.proof().clone(),
            [x.term().clone(), y.term().clone()],
        ),
    );
    let final_map = mapped(
        &mut assembler,
        symm(&source_equation),
        input.model.config_type(),
        |answer| {
            let mut states = actual_states.clone();
            let last = states.len() - 1;
            states[last] = input.returned(answer);
            choose(
                input.model.config_type(),
                input.memory_guard(),
                select(input.fuel.clone(), &states, input.model.config_type()),
                input.bad("IRFault.bad_addr"),
            )
        },
    )?;
    let raw =
        assembler.convert_endpoints(raw.clone(), raw.left().clone(), final_map.left().clone())?;
    let typed = assembler.compose(raw, final_map)?;
    let typed_parameters = [w, memory, host, providers, x, y, fuel];
    let typed_claim = close(
        assembler.local_scope(),
        &typed_parameters,
        typed.proposition(),
        false,
    )?;
    let typed_proof = close(
        assembler.local_scope(),
        &typed_parameters,
        typed.term().clone(),
        true,
    )?;
    Ok((total_claim, total_proof, typed_claim, typed_proof))
}

// Copyright 2026 Andrew Yates | License: Apache-2.0
// Exercise the shared datatype declaration and term printers together through AY.
#![allow(clippy::disallowed_methods)]

use ay::{Logic, Solver};
use trust_ir_contract::{Formula, Sort};

#[test]
fn reserved_and_digit_prefixed_variable_names_agree_in_ay() {
    for name in ["let", "forall", "set-logic", "1source", "1.5"] {
        let variable = Formula::Var(name.into(), Sort::Int);
        let declaration = format!(
            "(declare-const {} Int)\n",
            trust_ir_contract::escape_smtlib_symbol(name)
        );
        for contradict in [false, true] {
            let mut script = declaration.clone();
            for value in if contradict { &[7, 8][..] } else { &[7][..] } {
                let assertion =
                    Formula::Eq(Box::new(variable.clone()), Box::new(Formula::Int(*value)));
                script.push_str(&format!("(assert {})\n", assertion.to_smtlib()));
            }
            let mut solver = Solver::try_new(Logic::All).expect("AY symbol solver");
            solver.parse_smtlib2(&script).unwrap_or_else(|error| {
                panic!("AY refused shared symbol SMT-LIB: {error}\n{script}")
            });
            let result = solver.check_sat();
            assert_eq!(result.is_unsat(), contradict, "{name}: {result:?}");
            assert_eq!(result.is_sat(), !contradict, "{name}: {result:?}");
        }
    }
}

#[test]
fn quoted_datatype_declarations_and_terms_agree_in_ay() {
    let sort = Sort::Datatype {
        name: "source::Option Int".into(),
        constructors: vec![
            ("source::None".into(), vec![]),
            (
                "source::Some".into(),
                vec![("stored value".into(), Sort::Int)],
            ),
        ],
    };
    let some = Formula::Ctor {
        ctor: "source::Some".into(),
        args: vec![Formula::Int(42)],
        sort: sort.clone(),
    };
    let value = Formula::Sel {
        datatype: "source::Option Int".into(),
        field: "stored value".into(),
        field_sort: Sort::Int,
        arg: Box::new(some.clone()),
    };
    let none = Formula::Ctor {
        ctor: "source::None".into(),
        args: vec![],
        sort: sort.clone(),
    };
    let claims = Formula::And(vec![
        Formula::Eq(Box::new(value), Box::new(Formula::Int(42))),
        Formula::IsCtor {
            datatype: "source::Option Int".into(),
            ctor: "source::Some".into(),
            arg: Box::new(some),
        },
        Formula::IsCtor {
            datatype: "source::Option Int".into(),
            ctor: "source::None".into(),
            arg: Box::new(none),
        },
    ]);
    // Check the positive case too: an always-UNSAT result must not pass.
    for negate in [false, true] {
        let assertion = if negate {
            Formula::Not(Box::new(claims.clone()))
        } else {
            claims.clone()
        };
        let mut script = sort.datatype_declarations().join("\n");
        script.push_str(&format!("\n(assert {})\n", assertion.to_smtlib()));
        let mut solver = Solver::try_new(Logic::All).expect("AY datatype solver");
        solver.parse_smtlib2(&script).unwrap_or_else(|error| {
            panic!("AY refused shared datatype SMT-LIB: {error}\n{script}")
        });
        let result = solver.check_sat();
        if negate {
            assert!(result.is_unsat(), "datatype laws must hold: {result:?}");
        } else {
            assert!(
                result.is_sat(),
                "datatype context must be inhabited: {result:?}"
            );
        }
    }
}

// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn every_multiresult_flag_is_typed_without_inventing_a_fact_and_duplicate_callee_policies_stay_distinct()
 {
    let mut m = module();
    m.types.push(Ty::Bool);
    m.predicates.push(Pred::Interval { lo: 0, hi: 1 });
    let flag = Ty::Refine(TyId::new(3), PredId::new(10));
    m.func_types[1].returns = vec![Ty::I32, Ty::Bool];
    m.func_types.push(sig(vec![Ty::U64], vec![Ty::U64]));
    let mut body = vec![
        node(
            Inst::Overflow {
                op: trust_ir::inst::OverflowOp::AddOverflow,
                ty: Ty::I32,
                lhs: v(0),
                rhs: v(0),
            },
            &[1, 2],
        ),
        node(
            Inst::CmpXchg {
                ty: Ty::I32,
                ptr: v(90),
                expected: v(0),
                desired: v(0),
                success: Ordering::SeqCst,
                failure: Ordering::SeqCst,
                weak: false,
            },
            &[3, 4],
        ),
        node(
            Inst::Call {
                callee: FuncId::new(20),
                args: vec![v(0)],
            },
            &[5, 6],
        ),
    ];
    for value in [2, 4, 6] {
        body.push(node(
            Inst::Store {
                ty: flag.clone(),
                ptr: v(90),
                value: v(value),
                volatile: false,
                align: None,
            },
            &[],
        ));
    }
    m.functions = vec![
        function(10, 0, vec![(v(0), Ty::I32)], body),
        function(20, 1, vec![], vec![]),
    ];
    let (errors, _, _) = run(&m);
    assert_eq!(errors.iter().filter(|e|matches!(e,ValidationError::RefinementNotImplied{location,required,..}if location.contains("store value")&&required.contains("in[0, 1]"))).count(),3);
    assert!(errors.iter().any(|e|matches!(e,ValidationError::RefinementNotImplied{location,..}if location.contains("call @"))));
    m.functions.push(function(20, 2, vec![], vec![]));
    let (errors, _, _) = run(&m);
    assert!(!errors.iter().any(|e|matches!(e,ValidationError::RefinementNotImplied{location,..}if location.contains("call @"))));
    assert_eq!(errors.iter().filter(|e|matches!(e,ValidationError::RefinementNotImplied{location,..}if location.contains("store value"))).count(),3);
}

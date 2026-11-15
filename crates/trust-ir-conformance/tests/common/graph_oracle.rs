// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use trust_ir::TyId;

#[test]
fn graph_oracle_requires_valid_whole_result_graphs() {
    let wire = json!({"ok":{"graph":{"version":2,"nodes":[["int",32,"7"],["bool",true]],"roots":[0,1,0]}}});
    let verdict = lean_verdict(&wire);
    assert!(
        matches!(verdict, Verdict::Graph(_)),
        "successful IPC must retain a graph"
    );
    assert_eq!(
        verdict,
        Verdict::Ok(vec![
            Val::Int { width: 32, raw: 7 },
            Val::Bool(true),
            Val::Int { width: 32, raw: 7 }
        ])
    );
    for bad in [
        json!({"ok":{"graph":{"version":2,"nodes":[],"roots":[]}},"ub":"contradictory verdict"}),
        json!({"ok":[]}),
        json!({"ok":[{"int":{"width":32,"raw":"7"}}]}),
        json!({"ok":{"graph":{"version":1,"nodes":[],"roots":[]}}}),
        json!({"ok":{"graph":{"version":2,"nodes":[["cons",0,0]],"roots":[0]}}}),
        json!({"ok":{"graph":{"version":2,"nodes":[["int",8,"256"]],"roots":[0]}}}),
    ] {
        let error = lean_verdict(&bad);
        assert!(
            matches!(error, Verdict::Error(_)),
            "invalid observation must refuse: {bad}"
        );
        assert!(matches!(compare(&error, &error), Comparison::Mismatch(_)));
    }
    assert!(matches!(
        compare(
            &Verdict::Error("failed Rust observation".into()),
            &Verdict::Unsupported("coverage".into())
        ),
        Comparison::Mismatch(_)
    ));
    // Root order and multiplicity are actual observations.
    let mut changed = wire.clone();
    changed["ok"]["graph"]["roots"] = json!([1, 0, 0]);
    assert!(matches!(
        compare(&verdict, &lean_verdict(&changed)),
        Comparison::Mismatch(_)
    ));
    changed["ok"]["graph"]["roots"] = json!([0, 1]);
    assert!(matches!(
        compare(&verdict, &lean_verdict(&changed)),
        Comparison::Mismatch(_)
    ));
}

#[test]
fn graph_oracle_collects_full_huge_results_and_preserves_positional_policy() {
    use trust_ir::interpret::{ArrayValue, InterpretOutcome};
    let lane = InterpretValue::int(Ty::U32, 7).unwrap();
    let array = ArrayValue::splat(lane.clone(), u64::MAX);
    let value = InterpretValue {
        ty: Ty::Array(TyId::new(0), u64::MAX),
        kind: InterpretValueKind::Array(array),
    };
    let outcome = Ok(InterpretOutcome {
        returns: vec![value, lane],
        steps: 1,
        host_calls: 0,
    });
    let rust = rust_verdict(&outcome);
    let Verdict::Graph(graph) = &rust else {
        panic!("runtime success must use a graph")
    };
    assert!(
        graph.nodes().len() < 10,
        "logical extent must not control collection"
    );
    // The separate scalar root deliberately has its own node. Altering the
    // array payload must be caught through deferred word obligations alone.
    let wire = json!({"ok":{"graph":{"version":2,"nodes":[["int",32,"7"],["uniform",u64::MAX.to_string(),0],["array",u64::MAX.to_string(),1],["int",32,"7"]],"roots":[2,3]}}});
    assert_eq!(compare(&rust, &lean_verdict(&wire)), Comparison::Agree);
    let mut changed = wire.clone();
    changed["ok"]["graph"]["nodes"][0][2] = json!("8");
    assert!(
        matches!(
            compare(&rust, &lean_verdict(&changed)),
            Comparison::Mismatch(_)
        ),
        "runtime graph values must be compared"
    );
    // Arrays and positional aggregate values have always shared W5b's
    // ordered-content observation. Other collection kinds remain distinct.
    let values = vec![Val::Int { width: 32, raw: 7 }; 3];
    let array = Verdict::Graph(expected_graph(&[Val::Array(values.clone())]).unwrap());
    let dense = Verdict::Graph(expected_graph(&[Val::Aggregate(values.clone())]).unwrap());
    assert_eq!(compare(&array, &dense), Comparison::Agree);
    assert_eq!(compare(&dense, &array), Comparison::Agree);
    assert_ne!(array, Verdict::Ok(vec![Val::Vector(values.clone())]));
    assert_ne!(
        array,
        Verdict::Ok(vec![Val::Aggregate(values[..2].to_vec())])
    );
}

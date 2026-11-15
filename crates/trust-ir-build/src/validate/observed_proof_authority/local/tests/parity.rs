// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn complete_actual_local_admission_oracle_matches_routed_accepted_and_nonrouted_certificates() {
    let m = fixture();
    let a = input(&m);
    assert_eq!(normalized(&oracle(&a, 1)), (1, None));
    run(&a, 1);
    run(&a, 0);
}
#[test]
fn routing_requires_any_discharged_then_exactly_one_local_row_before_other_checks() {
    for status in [
        ProofStatus::Pending,
        ProofStatus::Certified,
        ProofStatus::Trusted,
        ProofStatus::Discharged,
    ] {
        let mut m = fixture();
        m.proof_obligations[1].status = status;
        m.proof_obligations.push(row(2, ProofStatus::Pending));
        run(&input(&m), 1);
    }
}
#[test]
fn raw_kind_custom_payload_and_every_formula_field_are_compared_in_original_first_order() {
    for field in 0..10 {
        let mut m = fixture();
        match field {
            0 => m.proof_obligations[1].function = None,
            1 => {
                m.proof_obligations[1].kind = ObligationKind::Custom {
                    namespace: "é🦀\0".repeat(300),
                    name: "claim".into(),
                }
            }
            2 => m.proof_obligations[1].formula = None,
            3 => m.proof_obligations[0].formula = None,
            n => {
                let f = m.proof_obligations[1].formula.as_mut().unwrap();
                match n {
                    4 => f.schema.push('x'),
                    5 => f.payload.push('x'),
                    6 => f.smtlib = None,
                    7 => f.sort = None,
                    8 => f.bindings[0].0.push('x'),
                    _ => f.bindings[0].1.place = ClausePlace::WorldPost,
                }
            }
        }
        run(&input(&m), 1);
    }
    let mut m = fixture();
    for r in &mut m.proof_obligations {
        r.kind = ObligationKind::Custom {
            namespace: "é🦀".into(),
            name: "claim".into(),
        };
    }
    run(&input(&m), 1);
    m.proof_obligations[0].kind = ObligationKind::Custom {
        namespace: "é🦀".into(),
        name: "other".into(),
    };
    run(&input(&m), 1);
}
#[test]
fn local_and_far_scope_unique_ids_and_missing_callee_are_exact_and_do_not_chain() {
    for case in 0..6 {
        let mut m = fixture();
        match case {
            0 => m.functions.clear(),
            1 => m.proof_obligations[0].function = None,
            2 => m.proof_obligations[0].function = Some(FuncId::new(8)),
            3 => m.proof_obligations.push(m.proof_obligations[0].clone()),
            4 => {
                m.proof_obligations.remove(0);
            }
            _ => m.functions.push(m.functions[0].clone()),
        };
        let mut a = input(&m);
        if case == 5 {
            a.kernel.clear();
            a.discharged = vec![m.proof_certificates[0].lineage_ref()];
        }
        run(&a, 1);
    }
}
#[test]
fn all_site_presence_and_function_block_instruction_differences_preserve_first_restatement_error() {
    let far = ObligationSite::new(FuncId::new(7), BlockId::new(9), 4);
    for local in [
        None,
        Some(far),
        Some(ObligationSite::new(FuncId::new(8), BlockId::new(9), 4)),
        Some(ObligationSite::new(FuncId::new(7), BlockId::new(10), 4)),
        Some(ObligationSite::new(FuncId::new(7), BlockId::new(9), 5)),
    ] {
        for site in [None, Some(far)] {
            let mut m = fixture();
            m.proof_obligations[0].site = site;
            m.proof_obligations[1].site = local;
            run(&input(&m), 1);
        }
    }
}
#[test]
fn full_coverage_partial_order_none_and_all_recorded_siblings_match_weakest_supply() {
    let bounds = [
        CoverageBound::Unbounded,
        CoverageBound::Unrecorded,
        CoverageBound::UnwindBounded { depth: u64::MAX },
        CoverageBound::UnwindBounded { depth: 0 },
        CoverageBound::ModelBounded { size: u64::MAX },
        CoverageBound::ModelBounded { size: 0 },
    ];
    for need in bounds {
        for supply in bounds {
            let mut m = fixture();
            m.proof_certificates[0].assurance = assurance(supply);
            m.proof_certificates[1].assurance = assurance(need);
            run(&input(&m), 1);
        }
    }
    run(&input(&coverage_fixture()), 1);
    let mut m = fixture();
    m.proof_certificates[1].assurance = assurance(CoverageBound::Unbounded);
    run(&input(&m), 1);
}
#[test]
fn exact_original_kernel_identity_includes_prover_and_evidence_but_excludes_assurance() {
    let mut m = fixture();
    let mut a = input(&m);
    a.kernel[0].prover.push('x');
    run(&a, 1);
    drop(a);
    m.proof_certificates[0].assurance = assurance(CoverageBound::Unbounded);
    let a = input(&m);
    run(&a, 1);
}
#[test]
fn deep_raw_binding_sort_equality_and_malformed_widths_are_not_normalized_or_truncated() {
    let mut m = fixture();
    let mut s = ClauseSort::BitVec(0);
    for _ in 0..40 {
        s = ClauseSort::Array(
            Box::new(ClauseSort::Float {
                eb: 0,
                sb: u32::MAX,
            }),
            Box::new(s),
        );
    }
    for row in &mut m.proof_obligations {
        row.formula.as_mut().unwrap().bindings[0].1.sort = s.clone();
    }
    run(&input(&m), 1);
    m.proof_obligations[0].formula.as_mut().unwrap().bindings[0]
        .1
        .sort = ClauseSort::Bool;
    run(&input(&m), 1);
}

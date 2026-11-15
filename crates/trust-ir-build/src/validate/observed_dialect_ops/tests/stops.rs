// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    clippy::field_reassign_with_default,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
fn every(m: &Module, n: &InstrNode, r: Option<&DialectSchemaRegistry>) {
    let (_, baseline, begin, end) = run(m, n, r);
    for cut in begin + 1..=end {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let values = setup(m, &mut s);
        assert_eq!(
            validate_dialect_node_observed(m, n, &values, r, BlockId::new(1), &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(s.first_refusal().unwrap().cause, "original dialect stop");
        let _ = values.retire_observed(&mut s, site());
        drop(s);
        assert_eq!(&o.events[..cut], &baseline.events[..cut]);
        assert!(
            o.events[cut..]
                .iter()
                .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
        );
    }
}
#[test]
fn every_actual_builtin_decoder_child_string_and_publication_callback_is_interruptible() {
    let m = fixture();
    for op in [
        trust_ir::dialect::vector::pack_lanes(vec_ty(Ty::I32, 4), [v(1); 4]),
        trust_ir::dialect::vector::shuffle(vec_ty(Ty::I32, 4), v(4), vec![0, 1, 2, 4]),
        DialectInst::new("vector", "unknown"),
        DialectInst::new("gpu", "unknown"),
        DialectInst::new("avx512", "mask_cmp"),
        DialectInst::new("ane", "tensor_conv"),
        trust_ir::dialect::trust_rust::thread_local_addr(""),
    ] {
        every(&m, &node(op, 1), None);
    }
}
#[test]
fn every_actual_frozen_schema_header_operand_function_attribute_and_publication_callback_refuses() {
    let m = fixture();
    let r = schema();
    for op in [
        operation(),
        operation().with_operand(v(0)),
        DialectInst::new("absent", "read"),
        operation().with_version(2),
        operation().with_attr("slot", AttrValue::Bool(false)),
    ] {
        every(&m, &node(op, 1), Some(&r));
    }
    let mut m = fixture();
    m.func_types[1].params = vec![Ty::I64];
    let r = callback_schema();
    every(&m, &node(call(14), 1), Some(&r));
}
#[test]
fn actual_late_frozen_registry_and_operation_data_rows_are_observed() {
    let m = fixture();
    let schemas = (0..12)
        .map(|i| DialectSchema {
            namespace: format!("a{i:02}"),
            version: 1,
            operations: vec![],
        })
        .chain([DialectSchema {
            namespace: "z".into(),
            version: 1,
            operations: (0..12)
                .map(|i| OperationSchema {
                    name: format!("a{i:02}"),
                    operands: vec![],
                    results: vec![],
                    attributes: vec![],
                })
                .chain([OperationSchema {
                    name: "z".into(),
                    operands: vec![],
                    results: vec![],
                    attributes: vec![],
                }])
                .collect(),
        }]);
    let r = DialectSchemaRegistry::new(schemas).unwrap();
    let n = node(DialectInst::new("z", "z"), 0);
    assert!(run(&m, &n, Some(&r)).0.is_empty());
    every(&m, &n, Some(&r));
}
#[test]
fn first_unknown_operand_prevents_later_actual_type_lookup_work_without_dropping_payload_work() {
    let m = fixture();
    let mut traces = Vec::new();
    for tail in [[v(0), v(1)], [v(18), v(17)]] {
        let op = trust_ir::dialect::vector::pack_lanes(
            vec_ty(Ty::I32, 4),
            [v(0), v(999), tail[0], tail[1]],
        );
        let (out, o, begin, end) = run(&m, &node(op, 1), None);
        assert!(out.is_empty());
        traces.push(o.events[begin..end].to_vec());
    }
    assert_eq!(traces[0], traces[1]);
}
#[test]
fn complete_source_exact_and_one_short_work_copy_caps_preserve_whole_result_or_refusal() {
    let m = fixture();
    let r = schema();
    let n = node(DialectInst::new("vector", "bad"), 0);
    let (_, baseline, _, end) = run(&m, &n, Some(&r));
    for copy in [false, true] {
        let cap: usize = baseline.events[..end]
            .iter()
            .map(|e| if copy { e.copy_bytes } else { e.work })
            .sum();
        for short in [false, true] {
            let mut o = Observer::default();
            if copy {
                o.byte_cap = Some(cap - usize::from(short))
            } else {
                o.work_cap = Some(cap - usize::from(short))
            }
            let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
            let values = setup(&m, &mut s);
            let out = validate_dialect_node_observed(
                &m,
                &n,
                &values,
                Some(&r),
                BlockId::new(1),
                &mut s,
                site(),
            );
            if short {
                assert_eq!(out, Err(ObservedValueError::AdmissionRefused));
                assert_eq!(
                    s.first_refusal().unwrap().cause,
                    if copy { "copy" } else { "work" }
                );
            } else {
                let out = out.unwrap();
                assert_eq!(out, original(&m, &n, Some(&r)));
                let _ = retire_validation_errors_observed(out, &mut s, site());
            }
            let _ = values.retire_observed(&mut s, site());
        }
    }
}
#[test]
fn repeated_builtin_and_schema_queries_consume_one_unchanged_cumulative_original_owner() {
    let m = fixture();
    let r = schema();
    let n = node(operation(), 1);
    let (_, baseline, _, end) = run(&m, &n, Some(&r));
    for copy in [false, true] {
        let cap = baseline.events[..end]
            .iter()
            .map(|e| if copy { e.copy_bytes } else { e.work })
            .sum();
        let mut o = Observer::default();
        if copy {
            o.byte_cap = Some(cap)
        } else {
            o.work_cap = Some(cap)
        }
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let values = setup(&m, &mut s);
        let out = validate_dialect_node_observed(
            &m,
            &n,
            &values,
            Some(&r),
            BlockId::new(1),
            &mut s,
            site(),
        )
        .unwrap();
        assert_eq!(
            validate_dialect_node_observed(
                &m,
                &n,
                &values,
                Some(&r),
                BlockId::new(1),
                &mut s,
                site()
            ),
            Err(ObservedValueError::AdmissionRefused)
        );
        let _ = retire_validation_errors_observed(out, &mut s, site());
        let _ = values.retire_observed(&mut s, site());
    }
}
#[test]
fn zero_instruction_fuel_and_existing_original_stop_never_create_a_new_context() {
    let m = fixture();
    let n = node(operation(), 1);
    let r = schema();
    let (_, _, begin, _) = run(&m, &n, Some(&r));
    let mut options = InterpretOptions::default();
    options.fuel = 0;
    let mut o = Observer::default();
    let mut s = ObservedSession::new(options, &mut o);
    let values = setup(&m, &mut s);
    let out =
        validate_dialect_node_observed(&m, &n, &values, Some(&r), BlockId::new(1), &mut s, site())
            .unwrap();
    assert!(out.is_empty());
    assert_eq!(s.remaining_fuel(), 0);
    retire_validation_errors_observed(out, &mut s, site()).unwrap();
    values.retire_observed(&mut s, site()).unwrap();
    drop(s);
    let mut o = Observer {
        stop: Some(begin + 1),
        ..Observer::default()
    };
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let values = setup(&m, &mut s);
    assert!(
        s.admit(ExecutionProgress {
            phase: ExecutionPhase::Validation,
            site: site(),
            work: 1,
            copy_bytes: 0
        })
        .is_err()
    );
    let count = calls.get();
    for _ in 0..2 {
        assert_eq!(
            validate_dialect_node_observed(
                &m,
                &n,
                &values,
                Some(&r),
                BlockId::new(1),
                &mut s,
                site()
            ),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(calls.get(), count);
    }
    assert_eq!(s.first_refusal().unwrap().cause, "original dialect stop");
    let _ = values.retire_observed(&mut s, site());
}
#[test]
fn actual_setup_and_partial_target_debits_are_retained_after_exhaustion_and_cleanup() {
    let m = fixture();
    let r = schema();
    let n = node(operation().with_attr("unknown", AttrValue::U64(0)), 1);
    let (_, baseline, begin, end) = run(&m, &n, Some(&r));
    let middle = begin + (end - begin) / 2;
    for copy in [false, true] {
        let cap: usize = baseline.events[..middle]
            .iter()
            .map(|e| if copy { e.copy_bytes } else { e.work })
            .sum();
        let mut o = Observer::default();
        if copy {
            o.byte_cap = Some(cap)
        } else {
            o.work_cap = Some(cap)
        }
        let calls = o.calls.clone();
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let values = setup(&m, &mut s);
        assert_eq!(
            validate_dialect_node_observed(
                &m,
                &n,
                &values,
                Some(&r),
                BlockId::new(1),
                &mut s,
                site()
            ),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert!(calls.get() > begin);
        assert_eq!(
            s.first_refusal().unwrap().cause,
            if copy { "copy" } else { "work" }
        );
        let _ = values.retire_observed(&mut s, site());
        drop(s);
        assert!(if copy { o.bytes > cap } else { o.work > cap });
    }
}

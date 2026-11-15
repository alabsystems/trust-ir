// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    clippy::field_reassign_with_default,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
fn every(m: &Module, inst: &Inst) {
    let (_, baseline, begin, end) = run(m, inst);
    for cut in begin + 1..=end {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let (layouts, values) = setup(m, &mut s);
        assert_eq!(
            validate_make_aggregate_observed(
                &layouts,
                inst,
                &values,
                BlockId::new(1),
                &mut s,
                site()
            ),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(
            s.first_refusal().unwrap().cause,
            "original make-aggregate stop"
        );
        let _ = values.retire_observed(&mut s, site());
        drop(s);
        drop(layouts);
        assert_eq!(&o.events[..cut], &baseline.events[..cut]);
        assert!(
            o.events[cut..]
                .iter()
                .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
        );
    }
}
#[test]
fn every_actual_enum_assignment_layout_lane_diagnostic_and_publication_callback_refuses() {
    let m = fixture();
    for inst in [
        make(Ty::Struct(StructId::new(0)), None, &[1, 0]),
        make(Ty::Enum(EnumId::new(0)), Some(0), &[1, 0]),
        make(Ty::Enum(EnumId::new(0)), Some(2), &[]),
        make(Ty::Array(TyId::new(0), 2), None, &[1, 1]),
    ] {
        every(&m, &inst);
    }
}
#[test]
fn late_fallback_nominal_rows_are_observed_for_struct_record_and_enum() {
    let mut m = fixture();
    m.structs = (0..12)
        .map(|i| structure(i + 100, vec![Ty::Bool]))
        .collect();
    m.structs.push(structure(77, vec![Ty::Bool]));
    m.records = (0..12)
        .map(|i| RecordDef {
            id: RecordId::new(i + 100),
            name: "R".into(),
            fields: vec![],
        })
        .collect();
    m.records.push(RecordDef {
        id: RecordId::new(88),
        name: "late".into(),
        fields: vec![field(Ty::Bool)],
    });
    let final_enum = m.enums[0].clone();
    m.enums = (0..12)
        .map(|i| EnumDef::new(EnumId::new(i + 100), "unused", vec![]))
        .collect();
    m.enums.push(EnumDef {
        id: EnumId::new(99),
        ..final_enum
    });
    for inst in [
        make(Ty::Struct(StructId::new(77)), None, &[0]),
        make(Ty::Record(RecordId::new(88)), None, &[0]),
        make(Ty::Enum(EnumId::new(99)), Some(1), &[]),
    ] {
        assert!(run(&m, &inst).0.is_empty());
        every(&m, &inst);
    }
}
#[test]
fn actual_transitive_inhabitedness_graph_is_interruptible_before_uninhabited_diagnostic() {
    let mut m = fixture();
    m.structs = vec![
        structure(100, vec![Ty::Struct(StructId::new(101))]),
        structure(101, vec![Ty::Record(RecordId::new(200))]),
    ];
    m.records = vec![RecordDef {
        id: RecordId::new(200),
        name: "bottom".into(),
        fields: vec![field(Ty::Array(TyId::new(2), 1))],
    }];
    m.enums[0].variants[2].fields = vec![Ty::Struct(StructId::new(100))];
    let inst = make(Ty::Enum(EnumId::new(0)), Some(2), &[]);
    assert!(matches!(
        &run(&m, &inst).0[..],
        [ValidationError::UninhabitedVariantConstructed { .. }]
    ));
    every(&m, &inst);
}
#[test]
fn repeated_queries_share_both_original_cumulative_caps_without_renewal() {
    let m = fixture();
    let inst = make(Ty::Enum(EnumId::new(0)), Some(0), &[1, 0]);
    let (_, baseline, _, end) = run(&m, &inst);
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
        let (layouts, values) = setup(&m, &mut s);
        let out = validate_make_aggregate_observed(
            &layouts,
            &inst,
            &values,
            BlockId::new(1),
            &mut s,
            site(),
        )
        .unwrap();
        assert_eq!(
            validate_make_aggregate_observed(
                &layouts,
                &inst,
                &values,
                BlockId::new(1),
                &mut s,
                site()
            ),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(
            s.first_refusal().unwrap().cause,
            if copy { "copy" } else { "work" }
        );
        let _ = retire_validation_errors_observed(out, &mut s, site());
        let _ = values.retire_observed(&mut s, site());
    }
}
#[test]
fn zero_instruction_fuel_and_preexisting_stop_keep_original_owner_and_site() {
    let m = fixture();
    let inst = make(Ty::Enum(EnumId::new(0)), Some(1), &[]);
    let (_, _, begin, _) = run(&m, &inst);
    let mut o = Observer::default();
    let mut options = InterpretOptions::default();
    options.fuel = 0;
    let mut s = ObservedSession::new(options, &mut o);
    let (layouts, values) = setup(&m, &mut s);
    let out =
        validate_make_aggregate_observed(&layouts, &inst, &values, BlockId::new(1), &mut s, site())
            .unwrap();
    assert!(out.is_empty());
    assert_eq!(s.remaining_fuel(), 0);
    retire_validation_errors_observed(out, &mut s, site()).unwrap();
    values.retire_observed(&mut s, site()).unwrap();
    drop(s);
    drop(layouts);
    let mut o = Observer {
        stop: Some(begin + 1),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let (layouts, values) = setup(&m, &mut s);
    assert!(
        s.admit(ExecutionProgress {
            phase: ExecutionPhase::Validation,
            site: site(),
            work: 1,
            copy_bytes: 0
        })
        .is_err()
    );
    assert_eq!(
        validate_make_aggregate_observed(&layouts, &inst, &values, BlockId::new(1), &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    let _ = values.retire_observed(&mut s, site());
}
#[test]
fn impossible_array_arity_never_walks_or_copies_the_actual_element_payload() {
    let mut traces = Vec::new();
    for element in [
        Ty::Bool,
        Ty::Tuple(vec![Ty::handle("unused", "rt::unused"); 400]),
    ] {
        let mut m = fixture();
        m.types[0] = element;
        let inst = make(Ty::Array(TyId::new(0), u64::MAX), None, &[0]);
        let (_, o, begin, end) = run(&m, &inst);
        traces.push(o.events[begin..end].to_vec());
    }
    assert_eq!(traces[0], traces[1]);
}

// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn all_nine_indexed_reference_arms_keep_exact_kind_and_id_diagnostics() {
    let m = Module::new("");
    let r = registry();
    for (ty, kind) in references(u32::MAX).into_iter().zip([
        "struct",
        "enum",
        "record",
        "closure_type",
        "func_type",
        "ty",
        "ty",
        "ty",
        "ty",
    ]) {
        assert_eq!(
            run(&m, &r, &ty, "raw location").0.0,
            vec![ValidationError::DanglingTypeReference {
                location: "raw location".into(),
                kind,
                id: u32::MAX
            }]
        );
    }
}
#[test]
fn existing_indexed_targets_are_accepted_without_building_layout_or_recursing() {
    let m = targets();
    let r = registry();
    for ty in references(0) {
        assert!(run(&m, &r, &ty, "L").0.0.is_empty());
    }
}
#[test]
fn nominal_definition_id_mismatch_at_the_index_is_still_dangling() {
    let mut m = targets();
    m.structs[0].id = StructId::new(8);
    m.enums[0].id = EnumId::new(8);
    m.records[0].id = RecordId::new(8);
    let r = registry();
    for ty in [
        Ty::Struct(StructId::new(0)),
        Ty::Enum(EnumId::new(0)),
        Ty::Record(RecordId::new(0)),
    ] {
        assert_eq!(run(&m, &r, &ty, "L").0.0.len(), 1);
    }
}
#[test]
fn this_node_rule_does_not_accidentally_recurse_or_follow_refinement_references() {
    let m = Module::new("");
    let r = registry();
    for ty in [
        Ty::Ref(Box::new(invalid())),
        Ty::Tuple(vec![untrusted()]),
        Ty::Refine(TyId::new(u32::MAX), PredId::new(u32::MAX)),
        Ty::Vector(Box::new(Ty::Struct(StructId::new(u32::MAX))), 4),
    ] {
        assert_eq!(run(&m, &r, &ty, "L").0, (vec![], NominalCensus::default()));
    }
}
#[test]
fn invalid_nominal_errors_are_first_only_and_census_bits_still_set() {
    let m = Module::new("");
    let r = registry();
    for ty in [
        Ty::Dialect(Box::new(DialectTy::new("!", "!", 0))),
        Ty::Dialect(Box::new(DialectTy::new("ns", "!", 0))),
        Ty::Dialect(Box::new(DialectTy::new("ns", "name", 0))),
    ] {
        let (out, c) = run(&m, &r, &ty, "L").0;
        assert_eq!(out.len(), 1);
        assert!(matches!(
            &out[0],
            ValidationError::InvalidDialectType { .. }
        ));
        assert_eq!(
            c,
            NominalCensus {
                dialect: true,
                handle: false
            }
        );
    }
    for ty in [Ty::handle("!", "!"), Ty::handle("Name", "bad:::runtime")] {
        let (out, c) = run(&m, &r, &ty, "L").0;
        assert_eq!(out.len(), 1);
        assert!(matches!(&out[0], ValidationError::InvalidHandleType { .. }));
        assert_eq!(
            c,
            NominalCensus {
                dialect: false,
                handle: true
            }
        );
    }
}
#[test]
fn every_actual_pinned_identity_is_accepted_and_case_or_suffix_changes_are_untrusted() {
    let m = Module::new("");
    let r = registry();
    for pin in r.pins() {
        assert!(run(&m, &r, &pin.handle_ty(), "L").0.0.is_empty());
        let ty = Ty::handle(format!("{}_", pin.name), pin.runtime);
        assert!(matches!(
            run(&m, &r, &ty, "L").0.0.as_slice(),
            [ValidationError::UntrustedHandleRuntime { .. }]
        ));
        let ty = Ty::handle(pin.name, format!("{}::extra", pin.runtime));
        assert!(matches!(
            run(&m, &r, &ty, "L").0.0.as_slice(),
            [ValidationError::UntrustedHandleRuntime { .. }]
        ));
    }
}
#[test]
fn supplied_empty_registry_is_not_replaced_by_a_pinned_accepting_fallback() {
    let m = Module::new("");
    let empty = HandleRegistry { pins: vec![] };
    let pin = &TRUSTED_HANDLE_RUNTIMES[0];
    let (out, c) = run(&m, &empty, &pin.handle_ty(), "L").0;
    assert_eq!(
        out,
        vec![ValidationError::UntrustedHandleRuntime {
            location: "L".into(),
            name: pin.name.into(),
            runtime: pin.runtime.into()
        }]
    );
    assert!(c.handle);
}
#[test]
fn whole_raw_location_and_untrusted_identity_are_preserved_without_truncation() {
    let m = Module::new("");
    let r = registry();
    let loc = "raw λ\0尾\n".repeat(2000);
    let name = "A9_".repeat(2000);
    let runtime = format!("prefix::{}", "B8_".repeat(1800));
    let ty = Ty::handle(&name, &runtime);
    assert_eq!(
        run(&m, &r, &ty, &loc).0.0,
        vec![ValidationError::UntrustedHandleRuntime {
            location: loc,
            name,
            runtime
        }]
    );
}
#[test]
fn registry_scan_checks_full_actual_identity_but_does_not_read_entrypoint_payloads() {
    let name: &'static str = Box::leak("N".repeat(4096).into_boxed_str());
    let runtime: &'static str = Box::leak(("R".repeat(4096) + "::Tail").into_boxed_str());
    let pin = HandleRuntimePin {
        name,
        runtime,
        calling_conv: trust_ir::CallingConv::C,
        entry_points: &[],
    };
    let r = HandleRegistry { pins: vec![pin] };
    let m = Module::new("");
    assert!(run(&m, &r, &Ty::handle(name, runtime), "L").0.0.is_empty());
    let bad = format!("{}X", &runtime[..runtime.len() - 1]);
    assert_eq!(bad.len(), runtime.len());
    assert!(matches!(
        run(&m, &r, &Ty::handle(name, bad), "L").0.0.as_slice(),
        [ValidationError::UntrustedHandleRuntime { .. }]
    ));
}

// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn genuine_handle_and_declared_struct_have_exact_natural_alignment_and_stronger_alloca_align() {
    let m = fixture();
    for ty in [handle(), Ty::Struct(StructId::new(0))] {
        for align in [None, Some(8), Some(16), Some(1u64 << 63)] {
            assert_eq!(run(&m, &ty, false, align).0, Ok(8));
        }
    }
    for (triple, bytes) in [
        ("wasm32-unknown-unknown", 4),
        ("aarch64-unknown-linux-gnu", 8),
    ] {
        let mut m = fixture();
        target(&mut m, triple, bytes);
        assert_eq!(run(&m, &handle(), false, None).0, Ok(u64::from(bytes)));
    }
}
#[test]
fn dynamic_count_refuses_first_without_running_carrier_or_layout_work() {
    let m = fixture();
    for ty in [handle(), Ty::Ref(Box::new(handle())), tuple()] {
        assert!(
            run(&m, &ty, true, None)
                .0
                .unwrap_err()
                .starts_with("an `Alloca` with a dynamic count")
        );
    }
}
#[test]
fn non_sealable_shapes_and_declared_missing_structs_keep_complete_original_reasons() {
    let m = fixture();
    for ty in [
        Ty::Ref(Box::new(handle())),
        Ty::Array(TyId::new(0), 1),
        Ty::Struct(StructId::new(999)),
    ] {
        assert!(
            run(&m, &ty, false, None)
                .0
                .unwrap_err()
                .contains("not a sealable slot type")
        );
    }
}
#[test]
fn undeclared_nonempty_tuple_is_a_genuine_semantic_layout_error_not_a_success_fixture() {
    let m = fixture();
    assert!(
        run(&m, &tuple(), false, None)
            .0
            .unwrap_err()
            .contains("no computable layout")
    );
    let mut m = fixture();
    m.structs[0].size = None;
    assert!(
        run(&m, &Ty::Struct(StructId::new(0)), false, None)
            .0
            .unwrap_err()
            .contains("no computable layout")
    );
}
#[test]
fn zero_under_natural_non_power_of_two_and_full_u64_alignment_values_match() {
    let m = fixture();
    for align in [0, 1, 2, 4, 7, 9, 15, u64::MAX] {
        let reason = run(&m, &handle(), false, Some(align)).0.unwrap_err();
        assert!(reason.contains(&align.to_string()));
        assert!(reason.contains("not a power of two"));
    }
}
#[test]
fn private_projection_refuses_nonbyte_extent_and_unknown_bad_alignment_with_full_shape_text() {
    for (size, align) in [(7, Some(8)), (8, None), (8, Some(0)), (8, Some(7))] {
        let shape = TyLayoutShape {
            size_bits: size,
            align_bits: align,
            kind: TyLayoutKind::Struct {
                id: StructId::new(u32::MAX),
                fields: vec![field()],
            },
        };
        let expected = format!(
            "`{}` has no byte-exact size and alignment ({shape}), so its slot image is not a checkable memory cell",
            handle()
        );
        let mut state = State {
            shape: Some(Arc::new(shape)),
            ..State::default()
        };
        let mut o = Observer::default();
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let mut work = Work {
            session: &mut s,
            site: site(),
        };
        assert_eq!(state.project(&handle(), None, &mut work).unwrap(), None);
        assert_eq!(state.reason, expected);
        drain(&mut state, &mut work);
        assert!(empty(&state));
    }
}
#[test]
fn complete_shape_formatter_matches_every_kind_scalar_shape_and_pointer_metadata_display() {
    let mut kinds = kinds();
    kinds.extend(ty_shapes().into_iter().map(TyLayoutKind::Scalar));
    kinds.extend(
        [
            PointerMetadataShape::SliceLen {
                elem: TyId::new(u32::MAX),
            },
            PointerMetadataShape::StrLen,
            PointerMetadataShape::VTable { trait_id: u32::MAX },
            PointerMetadataShape::ContainerLen,
            PointerMetadataShape::ContainerVtable,
        ]
        .into_iter()
        .map(TyLayoutKind::FatPointer),
    );
    for kind in kinds {
        for align in [None, Some(u64::MAX)] {
            let shape = TyLayoutShape {
                size_bits: u64::MAX,
                align_bits: align,
                kind: kind.clone(),
            };
            let mut o = Observer::default();
            let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
            let mut work = Work {
                session: &mut s,
                site: site(),
            };
            let text = layout_text::shape(&shape, &mut work).unwrap();
            assert_eq!(text, shape.to_string());
            work.flat(text);
        }
    }
}
#[test]
fn shape_text_reads_only_counts_and_scalar_headers_not_owned_field_payloads() {
    let a = TyLayoutShape {
        size_bits: 7,
        align_bits: None,
        kind: TyLayoutKind::Struct {
            id: StructId::new(1),
            fields: vec![field()],
        },
    };
    let mut b = a.clone();
    if let TyLayoutKind::Struct { fields, .. } = &mut b.kind {
        fields[0].name = "x".repeat(1_000_000);
        fields[0].field = 0;
        fields[0].offset_bits = None;
        fields[0].ty_shape = TyShape::Bool;
    }
    let trace = |shape: &TyLayoutShape| {
        let mut o = Observer::default();
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let mut work = Work {
            session: &mut s,
            site: site(),
        };
        let text = layout_text::shape(shape, &mut work).unwrap();
        work.flat(text);
        drop(work);
        drop(s);
        o.events
    };
    assert_eq!(a.to_string(), b.to_string());
    assert_eq!(trace(&a), trace(&b));
}

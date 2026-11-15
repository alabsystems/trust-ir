// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;

#[test]
fn all_conventions_linkages_and_body_presence_match_the_original_ffi_boundary() {
    let mut module = fixture();
    for conv in CallingConv::ALL {
        for linkage in linkages() {
            for body in [false, true] {
                let function = function(0, "boundary", conv, linkage, body);
                module.functions = vec![function.clone()];
                let out = run(&module, &function, Rule::Ffi).0;
                let foreign = !body
                    && matches!(linkage, Linkage::External | Linkage::ExternalWeak)
                    && conv != CallingConv::Rust;
                assert_eq!(out.len(), if foreign { 3 } else { 0 });
            }
        }
    }
}
#[test]
fn physical_functions_then_parameters_then_returns_preserve_duplicates_and_names() {
    let module = fixture();
    let out = run(&module, &module.functions[0], Rule::Ffi).0;
    assert_eq!(out.len(), 6);
    let mut expected = Vec::new();
    for name in ["firstλ", "secondλ"] {
        for position in ["parameter", "parameter", "return"] {
            expected.push(ValidationError::FfiStructReprUnpinned {
                func_name: name.into(),
                struct_id: 1,
                position,
            });
        }
    }
    assert_eq!(out, expected);
}
#[test]
fn duplicate_struct_ids_use_the_last_physical_repr_in_both_directions() {
    let mut module = fixture();
    module.structs.push(strukt(1, StructRepr::C));
    assert!(run(&module, &module.functions[0], Rule::Ffi).0.is_empty());
    module.structs.push(strukt(1, StructRepr::Rust));
    assert_eq!(run(&module, &module.functions[0], Rule::Ffi).0.len(), 6);
    module.structs.reverse();
    assert_eq!(run(&module, &module.functions[0], Rule::Ffi).0.len(), 6);
}
#[test]
fn every_non_rust_repr_including_malformed_packed_values_is_not_tightened_here() {
    let mut module = fixture();
    for repr in [
        StructRepr::C,
        StructRepr::Transparent,
        StructRepr::Packed(0),
        StructRepr::Packed(u32::MAX),
    ] {
        module.structs[0].repr = repr;
        assert!(run(&module, &module.functions[0], Rule::Ffi).0.is_empty());
    }
}
#[test]
fn only_direct_struct_slots_are_checked_without_recursive_or_refinement_peeling() {
    let mut module = fixture();
    module.types = vec![Ty::Struct(StructId::new(1))];
    let inner = Ty::Struct(StructId::new(1));
    let slots = vec![
        Ty::Ref(Box::new(inner.clone())),
        Ty::RefMut(Box::new(inner.clone())),
        Ty::PtrConst(Box::new(inner.clone())),
        Ty::PtrMut(Box::new(inner.clone())),
        Ty::Array(TyId::new(0), 1),
        Ty::Tuple(vec![inner.clone()]),
        Ty::Vector(Box::new(inner), 2),
        Ty::Refine(TyId::new(0), PredId::new(0)),
    ];
    module.func_types[0] = trust_ir::FuncTy::unrecorded(slots.clone(), slots, true);
    assert!(run(&module, &module.functions[0], Rule::Ffi).0.is_empty());
}
#[test]
fn missing_struct_and_signature_slots_are_left_to_the_original_other_validators() {
    let mut module = fixture();
    module.structs.clear();
    assert!(run(&module, &module.functions[0], Rule::Ffi).0.is_empty());
    module.structs.push(strukt(1, StructRepr::Rust));
    module.func_types.clear();
    assert!(run(&module, &module.functions[0], Rule::Ffi).0.is_empty());
}
#[test]
fn repr_rows_are_all_collected_even_when_the_function_table_is_empty() {
    let mut module = fixture();
    let function = module.functions[0].clone();
    module.functions.clear();
    let (_, before) = run(&module, &function, Rule::Ffi);
    module
        .structs
        .extend((0..100).map(|id| strukt(id, StructRepr::Rust)));
    let (_, after) = run(&module, &function, Rule::Ffi);
    assert!(after.events.len() > before.events.len());
    assert!(after.work > before.work);
}
#[test]
fn ffi_names_are_copied_raw_and_full_while_unrelated_metadata_is_opaque() {
    let mut module = fixture();
    let name = "λ'\"\\\n".repeat(3000) + "TAIL";
    for function in &mut module.functions {
        function.name = name.clone();
    }
    let (out, before) = run(&module, &module.functions[0], Rule::Ffi);
    assert!(out.iter().all(|error|matches!(error,ValidationError::FfiStructReprUnpinned{func_name,..} if func_name==&name)));
    for row in &mut module.structs {
        row.name = "opaque".repeat(3000);
    }
    for function in &mut module.functions {
        function.display_path = Some("opaque".repeat(3000));
    }
    let (_, after) = run(&module, &module.functions[0], Rule::Ffi);
    assert_eq!(before.events, after.events);
}
#[test]
fn rust_varargs_apply_to_definitions_and_all_linkages_but_only_exact_rust_convention() {
    let module = fixture();
    for conv in CallingConv::ALL {
        for linkage in linkages() {
            for body in [false, true] {
                let function = function(87, "varargs", conv, linkage, body);
                assert_eq!(
                    run(&module, &function, Rule::Vararg).0.len(),
                    usize::from(conv == CallingConv::Rust)
                );
            }
        }
    }
}
#[test]
fn non_variadic_and_missing_signature_skip_without_function_membership_lookup() {
    let mut module = fixture();
    let function = function(
        99,
        "not-in-module",
        CallingConv::Rust,
        Linkage::Private,
        true,
    );
    assert_eq!(run(&module, &function, Rule::Vararg).0.len(), 1);
    module.func_types[0].is_vararg = false;
    assert!(run(&module, &function, Rule::Vararg).0.is_empty());
    module.func_types.clear();
    assert!(run(&module, &function, Rule::Vararg).0.is_empty());
}
#[test]
fn rust_vararg_detail_preserves_exact_debug_unicode_decimal_index_and_fixed_count() {
    let mut module = fixture();
    module.func_types = vec![trust_ir::FuncTy::unrecorded(vec![], vec![], false); 11];
    module.func_types[10] = trust_ir::FuncTy::unrecorded(vec![Ty::Unit; 1234], vec![], true);
    for name in [
        "",
        "'\"\\\n\r\t\0\u{7f}",
        "λ中😀\u{301}\u{200d}\u{2028}\u{10ffff}",
    ] {
        let mut function = function(u32::MAX, name, CallingConv::Rust, Linkage::External, false);
        function.ty = FuncTyId::new(10);
        let out = run(&module, &function, Rule::Vararg).0;
        assert_eq!(
            out,
            vec![ValidationError::RustAbiVararg {
                function: u32::MAX,
                detail: format!(
                    "{name:?} declares the Rust calling convention with variadic functy.10 (1234 fixed parameter(s))"
                )
            }]
        );
    }
}
#[test]
fn vararg_rule_uses_only_signature_header_and_full_name_tail_without_deep_type_walks() {
    let mut module = fixture();
    let function = function(
        123,
        &("λ".repeat(3000) + "TAIL"),
        CallingConv::Rust,
        Linkage::Private,
        true,
    );
    let (out, before) = run(&module, &function, Rule::Vararg);
    assert!(
        matches!(&out[0],ValidationError::RustAbiVararg{detail,..} if detail.contains("TAIL\" declares"))
    );
    for ty in &mut module.func_types[0].params {
        *ty = Ty::Tuple(vec![Ty::Error; 1000]);
    }
    module.func_types[0].returns = vec![Ty::Error; 10000];
    let (_, after) = run(&module, &function, Rule::Vararg);
    assert_eq!(before.events, after.events);
}
#[test]
fn actual_decimal_writer_preserves_zero_and_full_fixed_integer_extremes() {
    for number in [0, 1, u128::from(u32::MAX), usize::MAX as u128, u128::MAX] {
        let mut observer = Observer::default();
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        let mut work = Work {
            session: &mut session,
            site: site(),
        };
        let mut text = String::new();
        work.number(number, &mut text).unwrap();
        assert_eq!(text, number.to_string());
        work.retire_text(text);
    }
}

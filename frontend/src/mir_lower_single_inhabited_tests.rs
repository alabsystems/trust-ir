// Copyright 2026 Andrew Yates | Licensed under the Apache License, Version 2.0
//! Actual compiler layouts and MIR SetDiscriminant lowering, not a model of a
//! guessed Rust enum representation. This artifact-only lane is not codegen proof.
use super::*;
use rustc_driver::{Callbacks, Compilation};
use rustc_interface::interface::Compiler;
use rustc_middle::mono::MonoItem;
use std::path::Path;

struct ActualEnumChecks {
    checked: usize,
}

impl Callbacks for ActualEnumChecks {
    fn after_analysis(&mut self, _compiler: &Compiler, tcx: TyCtxt<'_>) -> Compilation {
        let mono = tcx.collect_and_partition_mono_items(());
        for cgu in mono.codegen_units {
            for (item, _) in cgu.items_in_deterministic_order(tcx) {
                let MonoItem::Fn(instance) = item else {
                    continue;
                };
                if !matches!(instance.def, ty::InstanceKind::Item(_))
                    || !instance.def_id().is_local()
                {
                    continue;
                }
                let name = tcx.item_name(instance.def_id());
                let body = tcx.instance_mir(instance.def);
                if name.as_str() == "set_single_discriminant" {
                    let writes = body
                        .basic_blocks
                        .iter()
                        .flat_map(|block| &block.statements)
                        .filter_map(|statement| match &statement.kind {
                            StatementKind::SetDiscriminant {
                                place,
                                variant_index,
                            } => Some((place, *variant_index)),
                            _ => None,
                        })
                        .collect::<Vec<_>>();
                    assert_eq!(
                        writes.len(),
                        1,
                        "{name}: actual MIR must retain SetDiscriminant"
                    );
                    let (place, selected) = writes[0];
                    let enum_ty = place.ty(&body.local_decls, tcx).ty;
                    let source = tcx
                        .layout_of(ty::TypingEnv::fully_monomorphized().as_query_input(enum_ty))
                        .unwrap();
                    assert!(
                        matches!(source.variants, Variants::Single { index } if index == selected),
                        "{name}: expected Single({selected:?}), actual {:?}, size {}, align {}",
                        source.variants,
                        source.size.bytes(),
                        source.align.bytes()
                    );
                    let (module, errors) = lower_module_for_emit(tcx, instance, body)
                        .expect("lower actual Single MIR");
                    assert!(errors.is_empty(), "{errors:?}");
                    let functions = module
                        .functions
                        .iter()
                        .filter(|function| !function.blocks.is_empty())
                        .collect::<Vec<_>>();
                    assert_eq!(functions.len(), 1);
                    let function = functions[0];
                    for value in [0_u32, 1, 0x11223344, u32::MAX] {
                        let input =
                            trust_ir::interpret::InterpretValue::int(TIRTy::U32, i128::from(value))
                                .unwrap();
                        let outcome = trust_ir::interpret::Interpreter::with_module(&module)
                            .execute_func(function.id, vec![input])
                            .unwrap();
                        assert_eq!(
                            outcome.returns[0].as_int().unwrap().as_unsigned(),
                            u128::from(value)
                        );
                    }
                    assert!(
                        !function.instructions().any(|node| matches!(
                            node.inst,
                            trust_ir::Inst::Store { ty: TIRTy::I8, .. }
                        )),
                        "a tagless SetDiscriminant must not overwrite a payload byte"
                    );
                    self.checked += 1;
                    continue;
                }
                let expected = match name.as_str() {
                    "make_result" => Some(Some(0)),
                    "make_second" => Some(Some(1)),
                    "make_nested" | "make_repr_c" | "make_two_live" => Some(None),
                    _ => None,
                };
                let Some(selected) = expected else { continue };
                let (cx, _, _) = classify_locals_and_ret_abi(tcx, instance, body, false).unwrap();
                let enum_ty = cx.local_concrete_ty(Local::from_u32(0));
                let source = tcx
                    .layout_of(ty::TypingEnv::fully_monomorphized().as_query_input(enum_ty))
                    .unwrap();
                let layout = mir_enum_layout(&cx, enum_ty).unwrap();
                assert_eq!(layout.variants.len(), 2);
                if let Some(selected) = selected {
                    assert!(
                        matches!(source.variants, Variants::Single { index } if index.as_usize() == selected),
                        "{name}: expected Single({selected}), actual {:?}, size {}, align {}",
                        source.variants,
                        source.size.bytes(),
                        source.align.bytes()
                    );
                    assert_eq!(
                        single_variant_discr(&cx, enum_ty).unwrap(),
                        selected as i128
                    );
                    assert!(!multi_variant_has_tag(&layout));
                    for (index, row) in layout.variants.iter().enumerate() {
                        if index == selected {
                            assert_eq!(row.1, [0]);
                        } else {
                            assert!(row.0.is_none() && row.1.is_empty());
                        }
                    }
                } else {
                    assert!(
                        matches!(
                            source.variants,
                            Variants::Multiple {
                                tag_encoding: TagEncoding::Direct,
                                ..
                            }
                        ),
                        "{name}: expected Direct control, actual {:?}, size {}, align {}",
                        source.variants,
                        source.size.bytes(),
                        source.align.bytes()
                    );
                    assert!(
                        multi_variant_has_tag(&layout),
                        "{name}: actual Direct controls keep their physical tags"
                    );
                }
                self.checked += 1;
            }
        }
        Compilation::Stop
    }
}

#[test]
fn actual_rust_single_inhabited_layouts_and_set_discriminant_preserve_payloads() {
    let fixture = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/single_inhabited_enum_corpus.rs");
    let mut args = vec![
        "trust_ir_mir".into(),
        fixture.display().to_string(),
        "--crate-type=lib".into(),
        "-Ztrust-verify=off".into(),
    ];
    trust_ir_frontend::append_matching_rustc_sysroot(&mut args)
        .expect("matching installed Trust compiler");
    let mut checks = ActualEnumChecks { checked: 0 };
    rustc_driver::run_compiler(&args, &mut checks);
    assert_eq!(
        checks.checked, 6,
        "every actual source layout/control and MIR consumer must run"
    );
}

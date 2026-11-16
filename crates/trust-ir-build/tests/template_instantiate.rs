// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// Amendment S (`docs/SPEC_RATIFICATIONS.md` §22, the amendment's §5):
// `instantiate`, step by step — every answer checked against its contract,
// the host's edits append-only, the drop rewrite (reviews R1, R2), one row per
// symbol (R8), the output validated, and the instance identified by its
// template and its output (R5).

#[path = "../../trust-ir-conformance/tests/generate/templates.rs"]
#[allow(dead_code)]
mod templates;

use templates::{HOST_STRUCT_BASE, instance, instances};
use trust_ir::template::{
    Destructor, HoleAnswer, InstArg, LinkAnswer, ScriptedAnswer, ScriptedHost,
};
use trust_ir::{
    Constant, EnumTagRepr, FieldDef, Inst, InterpretOptions, Interpreter, StructDef, StructId,
    StructRepr, Ty,
};
use trust_ir_build::template::{InstantiateError, Question, instantiate};
use trust_ir_build::validate::validate_module;

fn host_for(name: &str) -> (trust_ir::template::Template, ScriptedHost) {
    let i = instances()
        .expect("every instance golden builds")
        .into_iter()
        .find(|i| i.name == name)
        .unwrap_or_else(|| panic!("no instance {name}"));
    (i.template, i.host)
}

#[test]
fn every_corpus_instance_instantiates_and_validates() {
    for case in instances().expect("every instance golden builds") {
        let mut host = case.host.clone();
        let out =
            instantiate(&case.template, &mut host).unwrap_or_else(|e| panic!("{}: {e}", case.name));
        assert_eq!(validate_module(&out.module), vec![], "{}", case.name);
        assert!(
            out.module
                .functions
                .iter()
                .all(|f| !f.name.starts_with("!template")),
            "{}: no reserved name survives",
            case.name
        );
    }
}

#[test]
fn ident_at_u64_is_the_hand_written_level_r_twin() {
    let (template, mut host) = host_for("ident_param<u64>");
    let out = instantiate(&template, &mut host).expect("instantiates");
    let twin = templates::ident_at_u64_twin().expect("template fixture");
    assert_eq!(out.module, twin);
    assert_eq!(out.module.stable_digest(), twin.stable_digest());
    #[cfg(feature = "binary")]
    assert_eq!(
        trust_ir::binary::serialize_module(&out.module).expect("serialize_module: test fixture"),
        trust_ir::binary::serialize_module(&twin).expect("serialize_module: test fixture"),
        "byte equality with the hand-written twin"
    );
}

#[test]
fn thin_pointer_contract_refuses_other_representations_before_level_r_validation() {
    for answer in [
        Ty::I64,
        Ty::U64,
        Ty::FatPtr(trust_ir::FatPtrKind::Str),
        Ty::Tuple(vec![Ty::Ptr, Ty::U64]),
    ] {
        let (template, mut host) = host_for("thin_pointer_compare<0>");
        host.holes[0] = ScriptedAnswer::Answer(HoleAnswer::Type(answer.clone()));
        let error = instantiate(&template, &mut host).expect_err("wrong pointer representation");
        assert!(
            matches!(error, InstantiateError::AnswerContract { hole: 0, .. }),
            "{answer}: {error}"
        );
    }
}

#[test]
fn thin_pointer_equality_executes_without_a_runtime_host_model() {
    for (name, expected) in [
        ("thin_pointer_compare<0>", true),
        ("thin_pointer_compare<16>", false),
    ] {
        let case = instances()
            .unwrap()
            .into_iter()
            .find(|case| case.name == name)
            .unwrap();
        let mut host = case.host;
        let out = instantiate(&case.template, &mut host).unwrap();
        let (inputs, _) = case.run.unwrap();
        let got = Interpreter::with_module(&out.module)
            .execute_func(out.module.functions[0].id, inputs)
            .unwrap();
        assert_eq!(got.returns, vec![trust_ir::InterpretValue::bool(expected)]);
        assert_eq!(got.host_calls, 0);
    }
}

#[test]
fn instantiated_bodies_run_like_hand_monomorphized_twins() {
    let mut ran = 0;
    for case in instances().expect("every instance golden builds") {
        let Some((inputs, expected)) = case.run.clone() else {
            continue;
        };
        let mut host = case.host.clone();
        let out = instantiate(&case.template, &mut host).expect("instantiates");
        let interpreter =
            Interpreter::with_module(&out.module).with_options(InterpretOptions::default());
        let got = interpreter
            .execute_func(out.module.functions[0].id, inputs)
            .unwrap_or_else(|e| panic!("{}: {e:?}", case.name));
        assert_eq!(got.returns, expected, "{}", case.name);
        ran += 1;
    }
    assert!(ran >= 12, "the executed instances shrank to {ran}");
}

#[test]
fn struct_contract_answer_with_reordered_fields_is_refused() {
    let (template, mut host) = host_for("struct_contract_field_read<u32>");
    // Vec<u32> answered with its fields swapped: the right field types, the
    // wrong order.
    host.structs[1].fields.swap(0, 1);
    let error = instantiate(&template, &mut host).expect_err("refused");
    assert!(
        matches!(&error, InstantiateError::AnswerContract { hole: 0, .. }),
        "{error}"
    );
}

#[test]
fn enum_contract_answer_with_other_discriminants_is_refused() {
    let (template, mut host) = host_for("enum_contract_match<u32>");
    host.enums[0].discriminants = vec![Some(3), Some(4)];
    let error = instantiate(&template, &mut host).expect_err("refused");
    assert!(
        matches!(&error, InstantiateError::AnswerContract { hole: 0, why } if why.contains("discriminants")),
        "{error}"
    );
    let (template, mut host) = host_for("enum_contract_match<u32>");
    host.enums[0].repr = Some(EnumTagRepr::U32);
    let error = instantiate(&template, &mut host).expect_err("refused");
    assert!(
        matches!(&error, InstantiateError::AnswerContract { hole: 0, why } if why.contains("repr")),
        "{error}"
    );
}

#[test]
fn drop_at_param_is_erased_at_u32_and_kept_at_a_struct() {
    let (template, mut host) = host_for("drop_at_param<u32>");
    let out = instantiate(&template, &mut host).expect("instantiates");
    let body = &out.module.functions[0];
    assert!(
        body.blocks.iter().flat_map(|b| &b.body).all(|n| !matches!(
            n.inst,
            Inst::Drop { .. } | Inst::DropInvoke { .. } | Inst::LandingPad { .. }
        )),
        "the drop and its dead cleanup pad are gone"
    );
    assert_eq!(
        body.blocks.len(),
        2,
        "the unreachable pad block was deleted (review R2)"
    );

    let (template, mut host) = host_for("drop_at_param<Resource>");
    let out = instantiate(&template, &mut host).expect("instantiates");
    let body = &out.module.functions[0];
    assert!(
        body.blocks
            .iter()
            .flat_map(|b| &b.body)
            .any(|n| matches!(n.inst, Inst::DropInvoke { .. })),
        "a drop of a struct with glue is kept"
    );
    assert_eq!(out.module.drop_glue.len(), 1);
    let glue = out.module.drop_glue[0].glue;
    assert_eq!(
        out.module.function_by_id(glue).map(|f| f.name.as_str()),
        Some("drop_in_place_resource")
    );
    assert!(matches!(
        out.module
            .drop_glue_for(&Ty::Struct(StructId::new(HOST_STRUCT_BASE))),
        trust_ir::DropResolution::Resolved(_)
    ));
}

#[test]
fn a_struct_without_a_destructor_erases_the_drop() {
    // Review R1: `is_trivially_droppable` is false for every struct, so the
    // drafted rule kept this drop UNRESOLVED; the host's answer erases it.
    let (template, mut host) = host_for("drop_at_param<Point>");
    let out = instantiate(&template, &mut host).expect("instantiates");
    assert!(
        out.module.functions[0]
            .blocks
            .iter()
            .flat_map(|b| &b.body)
            .all(|n| !matches!(n.inst, Inst::Drop { .. } | Inst::DropInvoke { .. }))
    );
    assert_eq!(out.answers.destructors.len(), 1);
    assert_eq!(out.answers.destructors[0].1, Destructor::NoDestructor);
}

#[test]
fn drop_invoke_erasure_deletes_the_cleanup_it_leaves_unreachable() {
    let (template, mut host) = host_for("drop_at_param<u32>");
    let out = instantiate(&template, &mut host).expect("instantiates");
    let blocks = &out.module.functions[0].blocks;
    assert!(matches!(
        &blocks[0].body.last().map(|n| &n.inst),
        Some(Inst::Br { target, args }) if target.index() == 1 && args.is_empty()
    ));
    // R2: the cleanup block only the erased edge reached is deleted (a kept
    // landing pad no invoke reaches is `MisplacedLandingPad` at level R).
    assert_eq!(
        blocks
            .iter()
            .map(|block| block.id.index())
            .collect::<Vec<_>>(),
        [0, 1],
        "the unreachable cleanup is gone"
    );
    assert!(
        blocks
            .iter()
            .flat_map(|block| &block.body)
            .all(|n| !matches!(n.inst, Inst::LandingPad { .. } | Inst::Resume { .. }))
    );
}

#[test]
fn self_recursive_callee_binds_to_the_body() {
    let (template, mut host) = host_for("self_recursive_generic<u64>");
    let out = instantiate(&template, &mut host).expect("instantiates");
    assert_eq!(
        out.module.functions.len(),
        1,
        "the hole row merged into the body"
    );
    let body = &out.module.functions[0];
    assert!(
        body.blocks
            .iter()
            .flat_map(|b| &b.body)
            .any(|n| matches!(n.inst, Inst::Call { callee, .. } if callee == body.id))
    );
}

#[test]
fn two_holes_one_symbol_merge_when_signatures_agree_and_refuse_otherwise() {
    // The self-recursive case is one hole and the body; here a ground
    // declaration and a callee answer share a symbol.
    let (mut template, mut host) = host_for("callee_hole_trait_call<u64>");
    let ground_ty = template
        .module
        .add_func_type(trust_ir::FuncTyG {
            abi: None,
            params: vec![trust_ir::TyG::U64],
            returns: vec![trust_ir::TyG::U64],
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut ground = trust_ir::FunctionG::new(
        trust_ir::FuncId::new(2),
        "clone_u64",
        ground_ty,
        trust_ir::BlockId::new(0),
    );
    ground.calling_conv = trust_ir::CallingConv::Rust;
    template.module.functions.push(ground);
    let out = instantiate(&template, &mut host).expect("one row per symbol");
    assert_eq!(
        out.module
            .functions
            .iter()
            .filter(|f| f.name == "clone_u64")
            .count(),
        1
    );
    // Another signature under the same symbol is a conflict.
    let (mut template, mut host) = host_for("callee_hole_trait_call<u64>");
    let other_ty = template
        .module
        .add_func_type(trust_ir::FuncTyG {
            abi: None,
            params: vec![trust_ir::TyG::U8],
            returns: vec![trust_ir::TyG::U64],
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut ground = trust_ir::FunctionG::new(
        trust_ir::FuncId::new(2),
        "clone_u64",
        other_ty,
        trust_ir::BlockId::new(0),
    );
    ground.calling_conv = trust_ir::CallingConv::Rust;
    template.module.functions.push(ground);
    let error = instantiate(&template, &mut host).expect_err("refused");
    assert!(
        matches!(error, InstantiateError::AnswerConflict { .. }),
        "{error}"
    );
}

#[test]
fn host_refusal_names_the_hole() {
    let (template, mut host) = host_for("const_hole_size_of<u64>");
    host.holes = vec![ScriptedAnswer::Refuse("T is unsized".into())];
    assert_eq!(
        instantiate(&template, &mut host),
        Err(InstantiateError::HostRefused {
            question: Question::Hole(trust_ir::HoleId::new(0)),
            why: "T is unsized".into()
        })
    );
}

#[test]
fn a_host_that_edits_a_seed_row_is_refused() {
    let (template, mut host) = host_for("ident_param<u64>");
    host.tamper = true;
    let error = instantiate(&template, &mut host).expect_err("refused");
    assert!(
        matches!(
            &error,
            InstantiateError::HostRowsInvalid {
                question: Question::Arguments,
                ..
            }
        ),
        "{error}"
    );
}

#[test]
fn arity_and_argument_kinds_are_checked() {
    let (template, mut host) = host_for("ident_param<u64>");
    host.arguments.clear();
    assert_eq!(
        instantiate(&template, &mut host),
        Err(InstantiateError::ArityMismatch {
            expected: 1,
            got: 0
        })
    );
    let (template, mut host) = host_for("ident_param<u64>");
    host.arguments = vec![InstArg::Const(Constant::Int(1))];
    assert!(matches!(
        instantiate(&template, &mut host),
        Err(InstantiateError::ArgumentKind { param: 0, .. })
    ));
}

#[test]
fn output_failing_level_r_validation_returns_nothing() {
    // `size_of::<T>()` answered with a constant the host's `usize` cannot be:
    // the answer passes its own check only as a usize-range integer, so feed
    // a type answer the body cannot use instead — a struct return where the
    // signature says usize is a level-R type error.
    let (template, mut host) = host_for("ident_param<u64>");
    host.header = Some(instance("identity_u64"));
    host.structs = vec![StructDef {
        id: StructId::new(HOST_STRUCT_BASE),
        name: "Empty".into(),
        fields: vec![FieldDef {
            name: "x".into(),
            ty: Ty::Struct(StructId::new(HOST_STRUCT_BASE)),
            offset: None,
        }],
        size: None,
        align: None,
        repr: StructRepr::Rust,
        origin: None,
    }];
    host.arguments = vec![InstArg::Type(Ty::Struct(StructId::new(HOST_STRUCT_BASE)))];
    let error = instantiate(&template, &mut host).expect_err("refused");
    assert!(
        matches!(error, InstantiateError::OutputInvalid(_)),
        "{error}"
    );
}

#[test]
fn instance_digest_is_the_template_and_output_digest() {
    let (template, mut host) = host_for("ident_param<u64>");
    let out = instantiate(&template, &mut host).expect("instantiates");
    assert_eq!(out.template_digest, template.digest().unwrap());
    let mut preimage = out.template_digest.bytes.to_vec();
    preimage.extend_from_slice(&out.module.stable_digest().bytes);
    assert_eq!(
        out.instance_digest,
        trust_ir::proof::ProofDigest::sha256_domain("trust_ir.template.instance.v1", &preimage)
    );
    // Another argument is another output, so another instance.
    let (template, mut other) = host_for("ident_param<i32>");
    let other = instantiate(&template, &mut other).expect("instantiates");
    assert_ne!(other.instance_digest, out.instance_digest);
    // Another template with an equal output is another instance.
    let mut renamed = template.clone();
    renamed.header.identity.push_str("_twin");
    let (_, mut host) = host_for("ident_param<u64>");
    let twin = instantiate(&renamed, &mut host).expect("instantiates");
    assert_eq!(twin.module, out.module);
    assert_ne!(twin.instance_digest, out.instance_digest);
}

#[test]
fn instantiate_is_deterministic_across_runs() {
    for case in instances().expect("every instance golden builds") {
        let mut first_host = case.host.clone();
        let mut second_host = case.host.clone();
        let first = instantiate(&case.template, &mut first_host).expect("instantiates");
        let second = instantiate(&case.template, &mut second_host).expect("instantiates");
        assert_eq!(first, second, "{}", case.name);
        assert_eq!(
            first.module.stable_digest(),
            second.module.stable_digest(),
            "{}",
            case.name
        );
        #[cfg(feature = "binary")]
        assert_eq!(
            trust_ir::binary::serialize_module(&first.module)
                .expect("serialize_module: test fixture"),
            trust_ir::binary::serialize_module(&second.module)
                .expect("serialize_module: test fixture"),
            "{}",
            case.name
        );
    }
}

#[test]
fn a_kind_mismatched_answer_is_a_refusal() {
    let (template, mut host) = host_for("const_hole_size_of<u64>");
    host.holes = vec![ScriptedAnswer::Answer(HoleAnswer::Type(Ty::U64))];
    assert!(matches!(
        instantiate(&template, &mut host),
        Err(InstantiateError::HostRefused { .. })
    ));
    let _ = LinkAnswer::rust("unused");
}

mod retained_placements {
    use super::*;
    use trust_ir::template::{HoleKind, hole_row_name};
    use trust_ir::{FuncId, HoleId, ValueId};
    use trust_ir_build::template::instantiate_retained;
    use trust_ir_build::{MergePolicy, RetainedImage};

    fn repeated_target() -> (trust_ir::template::Template, ScriptedHost) {
        let (mut template, mut host) = host_for("callee_hole_trait_call<u64>");
        let mut declaration = template.module.functions[1].clone();
        declaration.id = FuncId::new(2);
        declaration.name = hole_row_name(HoleId::new(1));
        template.module.functions.push(declaration);
        let mut hole = template.header.holes[0].clone();
        hole.kind = HoleKind::Callee {
            decl: FuncId::new(2),
        };
        hole.key.bytes.extend_from_slice(b"-another-original-call");
        template.header.holes.push(hole);
        host.holes.push(host.holes[0].clone());
        let block = &mut template.module.functions[0].blocks[0];
        block.body.insert(
            1,
            trust_ir::InstrNodeG::new(trust_ir::InstG::Call {
                callee: FuncId::new(2),
                args: vec![ValueId::new(1)],
            })
            .with_result(ValueId::new(2)),
        );
        block.body[2].inst = trust_ir::InstG::Return {
            values: vec![ValueId::new(2)],
        };
        (template, host)
    }

    #[test]
    fn retained_output_preserves_every_original_corpus_instance() {
        for case in instances().unwrap() {
            let plain = instantiate(&case.template, &mut case.host.clone()).unwrap();
            let retained = instantiate_retained(&case.template, &mut case.host.clone()).unwrap();
            assert_eq!(retained.module(), &plain.module, "{}", case.name);
            assert_eq!(retained.template_digest(), plain.template_digest);
            assert_eq!(retained.instance_digest(), plain.instance_digest);
            assert_eq!(retained.answers(), &plain.answers);
            #[cfg(feature = "binary")]
            assert_eq!(
                trust_ir::binary::serialize_module(retained.module()).unwrap(),
                trust_ir::binary::serialize_module(&plain.module).unwrap(),
                "{}: legacy instantiated bytes",
                case.name,
            );
            for original in &case.template.module.functions {
                let mapped = retained.function_in(retained.image(), original.id).unwrap();
                assert!(retained.module().function_by_id(mapped).is_some());
            }
            assert_eq!(retained.into_instantiated(), plain);
        }
    }

    #[test]
    fn self_call_retains_original_declaration_and_hole_through_actual_placement() {
        let (template, mut host) = host_for("self_recursive_generic<u64>");
        let retained = instantiate_retained(&template, &mut host).unwrap();
        assert_eq!(retained.module().functions.len(), 1);
        assert_eq!(
            retained
                .function_in(retained.image(), FuncId::new(1))
                .unwrap(),
            FuncId::new(0)
        );
        assert_eq!(
            retained
                .callee_in(retained.image(), HoleId::new(0))
                .unwrap(),
            FuncId::new(0)
        );
        let output = Interpreter::with_module(retained.module())
            .execute_func(
                FuncId::new(0),
                vec![
                    trust_ir::InterpretValue::int(Ty::U64, 3).unwrap(),
                    trust_ir::InterpretValue::int(Ty::U64, 19).unwrap(),
                ],
            )
            .unwrap();
        assert_eq!(
            output.returns,
            vec![trust_ir::InterpretValue::int(Ty::U64, 19).unwrap()]
        );

        let (other, mut host) = host_for("ident_param<u64>");
        let destination =
            RetainedImage::new(instantiate(&other, &mut host).unwrap().module).unwrap();
        let (placed, map) = destination
            .merge(retained.image(), &MergePolicy::VERIFICATION_IMAGE)
            .unwrap();
        let expected = map.func(FuncId::new(0)).unwrap();
        assert_ne!(
            expected,
            FuncId::new(0),
            "the fixture must relocate the root"
        );
        assert_eq!(
            retained.function_in(&placed, FuncId::new(0)).unwrap(),
            expected
        );
        assert_eq!(
            retained.function_in(&placed, FuncId::new(1)).unwrap(),
            expected
        );
        assert_eq!(
            retained.callee_in(&placed, HoleId::new(0)).unwrap(),
            expected
        );
        let (again, _) = placed
            .merge(&retained.image().clone(), &MergePolicy::VERIFICATION_IMAGE)
            .unwrap();
        assert_eq!(
            retained.callee_in(&again, HoleId::new(0)).unwrap(),
            expected
        );
    }

    #[test]
    fn distinct_original_holes_keep_one_canonical_target_and_all_original_calls() {
        let (template, mut host) = repeated_target();
        let retained = instantiate_retained(&template, &mut host).unwrap();
        let image = retained.image();
        assert_eq!(image.module().functions.len(), 2);
        let first = retained.callee_in(image, HoleId::new(0)).unwrap();
        assert_eq!(first, FuncId::new(1));
        assert_eq!(retained.callee_in(image, HoleId::new(1)).unwrap(), first);
        assert_eq!(retained.function_in(image, FuncId::new(2)).unwrap(), first);
        let calls: Vec<_> = image.module().functions[0].blocks[0]
            .body
            .iter()
            .filter_map(|node| {
                if let Inst::Call { callee, .. } = node.inst {
                    Some(callee)
                } else {
                    None
                }
            })
            .collect();
        assert_eq!(calls, [first, first]);

        // A one-sided convention change must still fail the existing merger.
        let ScriptedAnswer::Answer(HoleAnswer::Callee(answer)) = &mut host.holes[1] else {
            panic!("callee fixture")
        };
        answer.calling_conv = trust_ir::CallingConv::C;
        assert!(matches!(
            instantiate_retained(&template, &mut host),
            Err(InstantiateError::AnswerConflict { .. })
        ));
    }

    #[test]
    fn equal_or_mutated_data_and_unrelated_remaps_cannot_restore_placement() {
        let (template, mut host) = repeated_target();
        let retained = instantiate_retained(&template, &mut host).unwrap();
        assert_eq!(
            retained
                .callee_in(retained.image(), HoleId::new(1))
                .unwrap(),
            FuncId::new(1)
        );
        let equal = RetainedImage::new(retained.module().clone()).unwrap();
        assert!(retained.callee_in(&equal, HoleId::new(1)).is_err());
        let mut mutated = retained.module().clone();
        mutated.functions[0].blocks[0].body[0].inst = Inst::Call {
            callee: FuncId::new(0),
            args: vec![ValueId::new(0)],
        };
        let mutated = RetainedImage::new(mutated).unwrap();
        assert!(retained.callee_in(&mutated, HoleId::new(1)).is_err());
        let (foreign, _) = equal
            .merge(&equal.clone(), &MergePolicy::VERIFICATION_IMAGE)
            .unwrap();
        assert!(retained.function_in(&foreign, FuncId::new(2)).is_err());
        assert!(
            retained
                .function_in(retained.image(), FuncId::new(99))
                .is_err()
        );
        assert!(
            retained
                .callee_in(retained.image(), HoleId::new(99))
                .is_err()
        );
    }
}

// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Focused canonical placement controls. Paths are debug data; only an actual
//! immutable retained input can follow its own earlier canonical placement.

use trust_ir::constant::Constant;
use trust_ir::inst::Inst;
use trust_ir::node::InstrNode;
use trust_ir::ty::{FuncTy, Ty};
use trust_ir::value::{BlockId, FuncId, ValueId};
use trust_ir::{Block, BodyGate, Function, Module, SourceSpan};
use trust_ir_build::{MergeError, MergePolicy, RetainedImage, merge_into, validate_module};

const POLICY: MergePolicy = MergePolicy::EXECUTION_IMAGE;

fn original(name: &str, path: Option<&str>) -> Module {
    let mut module = Module::new(name);
    let signature = module
        .add_func_type(FuncTy {
            abi: None,
            params: vec![],
            returns: vec![Ty::I32],
            is_vararg: false,
        })
        .unwrap();
    let mut function = Function::new(FuncId::new(0), name, signature, BlockId::new(0));
    function.body_gate = Some(BodyGate::Ungated);
    let mut block = Block::new(BlockId::new(0));
    block.body.push(
        InstrNode::new(Inst::Const {
            ty: Ty::I32,
            value: Constant::Int(1),
        })
        .with_result(ValueId::new(0)),
    );
    block.body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(0)],
    }));
    let file = path.map_or(0, |path| module.intern_file(path).unwrap());
    block.body[0].span = Some(SourceSpan {
        file,
        line: 3,
        col: 7,
    });
    function.blocks.push(block);
    module.try_add_function(function).unwrap();
    module
}

fn retained(name: &str) -> RetainedImage {
    RetainedImage::new(original(name, Some("one-source.rs"))).unwrap()
}

fn span(image: &RetainedImage, name: &str) -> SourceSpan {
    image.module().function_by_name(name).unwrap().blocks[0].body[0]
        .span
        .unwrap()
}

#[test]
fn retained_diamond_composes_actual_placements_without_dropping_spans() {
    let root = retained("root");
    let leaf = retained("leaf");
    let (root, _) = root.merge(&leaf, &POLICY).unwrap();
    let (chain, first) = retained("chain").merge(&root, &POLICY).unwrap();
    let root_file = first.file(0).unwrap();
    let (chain, repeated) = chain.merge(&root, &POLICY).unwrap();
    assert_eq!(repeated.file(0), Some(root_file));
    assert_eq!(chain.module().files.len(), 3);
    let (diamond, _) = retained("diamond").merge(&chain, &POLICY).unwrap();
    let before = span(&diamond, "root");
    let (diamond, direct) = diamond.merge(&root.clone(), &POLICY).unwrap();
    assert_eq!(direct.file(0), Some(before.file));
    assert_eq!(span(&diamond, "root"), before);
    assert_eq!((before.line, before.col), (3, 7));
    assert_eq!(diamond.module().files.len(), 4);
    assert_eq!(diamond.module().functions.len(), 4);
    assert!(validate_module(diamond.module()).is_empty());
}

#[test]
fn ordinary_diamond_is_red_with_full_block_comparison() {
    let root = original("root", Some("one-source.rs"));
    let mut chain = original("chain", Some("one-source.rs"));
    merge_into(&mut chain, &root, &POLICY).unwrap();
    let mut diamond = original("diamond", Some("one-source.rs"));
    merge_into(&mut diamond, &chain, &POLICY).unwrap();
    let before = diamond.clone();
    assert!(matches!(
        merge_into(&mut diamond, &root, &POLICY),
        Err(MergeError::ConflictingDefinition {
            field: "blocks",
            ..
        })
    ));
    assert_eq!(diamond, before, "failed merge is transactional");
}

#[test]
fn independent_equal_input_and_raw_roundtrip_never_recover_origin() {
    let root = retained("root");
    let (chain, _) = retained("chain").merge(&root, &POLICY).unwrap();
    let equal = RetainedImage::new(root.module().clone()).unwrap();
    let roundtrip = RetainedImage::new(root.clone().into_module()).unwrap();
    for independent in [&equal, &roundtrip] {
        assert_eq!(
            root.module().stable_digest(),
            independent.module().stable_digest()
        );
        assert!(matches!(
            chain.merge(independent, &POLICY),
            Err(MergeError::ConflictingDefinition {
                field: "blocks",
                ..
            })
        ));
    }
}

#[test]
fn raw_body_span_and_license_mutations_remain_conflicts() {
    let root = retained("root");
    let (chain, _) = retained("chain").merge(&root, &POLICY).unwrap();
    for change in 0..5 {
        let mut raw = chain.module().clone();
        let function = raw.functions.iter_mut().find(|f| f.name == "root").unwrap();
        match change {
            0 => function.blocks[0].body[0].span.as_mut().unwrap().line += 1,
            1 => function.blocks[0].body[0].span.as_mut().unwrap().col += 1,
            2 => {
                function.blocks[0].body[0].inst = Inst::Const {
                    ty: Ty::I32,
                    value: Constant::Int(2),
                }
            }
            3 => function.body_gate = None,
            4 => function.attrs.cold = !function.attrs.cold,
            _ => unreachable!(),
        }
        let independently_edited = RetainedImage::new(raw).unwrap();
        assert!(matches!(
            chain.merge(&independently_edited, &POLICY),
            Err(MergeError::ConflictingDefinition { .. })
        ));
    }
}

#[test]
fn distinct_paths_and_equal_paths_have_the_same_structural_mapping() {
    let dst = retained("dst");
    let mut digests = Vec::new();
    for path in ["one-source.rs", "different.rs"] {
        let src = RetainedImage::new(original("src", Some(path))).unwrap();
        let (result, remap) = dst.merge(&src, &POLICY).unwrap();
        assert_eq!(remap.file(0), Some(1));
        assert_eq!(result.module().files.len(), 2);
        digests.push(result.module().stable_digest());
    }
    assert_eq!(digests[0], digests[1]);
}

#[test]
fn fileless_inputs_do_not_gain_origin_from_placeholder_rows() {
    let unknown = RetainedImage::new(original("unknown", None)).unwrap();
    let (once, _) = retained("dst").merge(&unknown, &POLICY).unwrap();
    assert_eq!(once.module().files.len(), 2);
    assert_eq!(span(&once, "unknown").file, 1);
    assert!(matches!(
        once.merge(&unknown, &POLICY),
        Err(MergeError::ConflictingDefinition {
            field: "blocks",
            ..
        })
    ));
}

#[test]
fn actual_function_placements_follow_source_destination_and_repeated_merge_receipts() {
    let source = retained("source");
    let id = FuncId::new(0);
    assert_eq!(source.function_from(&source.clone(), id).unwrap(), id);
    let (once, first) = retained("host").merge(&source, &POLICY).unwrap();
    let first_id = first.func(id).unwrap();
    assert_ne!(first_id, id, "the source must actually relocate");
    assert_eq!(once.function_from(&source, id).unwrap(), first_id);
    let (outer, second) = retained("outer").merge(&once, &POLICY).unwrap();
    let outer_id = second.func(first_id).unwrap();
    assert_eq!(outer.function_from(&source, id).unwrap(), outer_id);
    assert_eq!(outer.function_from(&once, first_id).unwrap(), outer_id);
    let (repeated, third) = outer.merge(&once, &POLICY).unwrap();
    assert_eq!(third.func(first_id), Some(outer_id));
    assert_eq!(repeated.function_from(&once, first_id).unwrap(), outer_id);
    assert_eq!(repeated.function_from(&source, id).unwrap(), outer_id);
}

#[test]
fn copied_modules_and_foreign_function_remaps_cannot_restore_actual_placement() {
    let source = retained("source");
    let (placed, actual) = retained("host").merge(&source, &POLICY).unwrap();
    let id = FuncId::new(0);
    assert_eq!(
        placed.function_from(&source, id).unwrap(),
        actual.func(id).unwrap()
    );
    let independent = RetainedImage::new(source.module().clone()).unwrap();
    assert!(placed.function_from(&independent, id).is_err());
    let (foreign, copied_shape) = retained("host").merge(&independent, &POLICY).unwrap();
    assert_eq!(
        copied_shape.func(id),
        actual.func(id),
        "equal copied remap numbers do not prove origin"
    );
    assert!(foreign.function_from(&source, id).is_err());
    assert!(
        source
            .function_from(&placed, actual.func(id).unwrap())
            .is_err()
    );
    assert!(placed.function_from(&source, FuncId::new(99)).is_err());
    let mut changed = source.module().clone();
    changed.functions[0].id = FuncId::new(7);
    let changed = RetainedImage::new(changed).unwrap();
    assert!(placed.function_from(&changed, FuncId::new(7)).is_err());
}

#[test]
fn intermediate_actual_images_survive_complete_original_input_deduplication() {
    let a = retained("a");
    let id = FuncId::new(0);
    let (b, _) = a.merge(&a, &POLICY).unwrap();
    let (c, _) = b.merge(&b, &POLICY).unwrap();
    // Matching controls establish the intermediate source and both direct
    // ancestors before the original failing destination-first composition.
    assert_eq!(c.function_from(&b, id).unwrap(), id);
    let (reversed, _) = c.merge(&a, &POLICY).unwrap();
    assert_eq!(reversed.function_from(&b, id).unwrap(), id);
    let (out, _) = a.merge(&c, &POLICY).unwrap();
    assert_eq!(out.function_from(&a, id).unwrap(), id);
    assert_eq!(out.function_from(&c, id).unwrap(), id);
    assert_eq!(out.function_from(&b, id).unwrap(), id);
    assert_eq!(out.module().files, a.module().files);
    assert_eq!(out.module().functions, a.module().functions);

    // Repeated genuine joins must agree along every preserved route, without
    // acquiring origin from an independent equal intermediate image.
    let (again, _) = out.merge(&reversed, &POLICY).unwrap();
    for actual in [&a, &b, &c, &out, &reversed] {
        assert_eq!(again.function_from(actual, id).unwrap(), id);
    }
    let independent = RetainedImage::new(b.module().clone()).unwrap();
    assert!(again.function_from(&independent, id).is_err());
}

#[test]
fn contradictory_actual_routes_refuse_even_for_malformed_data_only_images() {
    // RetainedImage is intentionally data custody, not full IR validation.
    // A malformed duplicate-name destination can retain its row 1 while the
    // canonical source map sends that same actual row to the first row 0.
    let mut module = Module::new("duplicate-declarations");
    let ty = module
        .add_func_type(FuncTy::unrecorded(vec![], vec![], false))
        .unwrap();
    for id in [FuncId::new(0), FuncId::new(1)] {
        let mut declaration = Function::new(id, "f", ty, BlockId::new(0));
        declaration.linkage = trust_ir::Linkage::External;
        module.functions.push(declaration);
    }
    let input = RetainedImage::new(module).unwrap();
    assert_eq!(
        input.function_from(&input, FuncId::new(1)).unwrap(),
        FuncId::new(1)
    );
    for policy in [
        MergePolicy::EXECUTION_IMAGE,
        MergePolicy::VERIFICATION_IMAGE,
    ] {
        let (output, remap) = input.merge(&input, &policy).unwrap();
        assert_eq!(remap.func(FuncId::new(0)), Some(FuncId::new(0)));
        assert_eq!(remap.func(FuncId::new(1)), Some(FuncId::new(0)));
        assert_eq!(
            output.function_from(&input, FuncId::new(0)).unwrap(),
            FuncId::new(0)
        );
        assert!(matches!(
            output.function_from(&input, FuncId::new(1)),
            Err(MergeError::Malformed {
                table: "retained function placement",
                ..
            })
        ));
    }
}

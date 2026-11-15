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

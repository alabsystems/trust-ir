// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

mod common;

use common::{build_valid_module, trust_ir_cmd};
use std::fs;
use trust_ir::{BlockId, FuncId, Function, Inst, InstrNode, ModuleCompleteness, UnloweredRow};

#[test]
fn census_reads_binary_without_claiming_validation_or_rewriting_it() {
    let dir = tempfile::tempdir().expect("tempdir");
    let path = dir.path().join("input.trust-ir.bin");
    let mut module = build_valid_module();
    module.functions[0].id = FuncId(91);
    let bytes =
        trust_ir::binary::serialize_module(&module).expect("serialize_module: test fixture");
    fs::write(&path, &bytes).expect("write");
    let output = trust_ir_cmd()
        .args(["dependencies", "--root", "91"])
        .arg(&path)
        .output()
        .expect("run");
    assert!(output.status.success(), "{output:?}");
    let text = String::from_utf8(output.stdout).expect("utf8");
    assert!(text.contains("root=91"), "{text}");
    assert!(text.contains("node Function(FuncId(91))"), "{text}");
    assert!(
        text.contains("validation=not-run source_refinement=unproved proof_authority=none"),
        "{text}"
    );
    assert!(text.contains("refusals=0"), "{text}");
    assert_eq!(fs::read(path).expect("read"), bytes);
}

#[test]
fn missing_root_is_not_resolved_by_vector_position() {
    let dir = tempfile::tempdir().expect("tempdir");
    let path = dir.path().join("input.json");
    let mut module = build_valid_module();
    module.functions[0].id = FuncId(91);
    fs::write(&path, serde_json::to_vec(&module).expect("json")).expect("write");
    let output = trust_ir_cmd()
        .args(["dependencies", "--root", "0"])
        .arg(path)
        .output()
        .expect("run");
    assert_eq!(output.status.code(), Some(1), "{output:?}");
    assert!(String::from_utf8_lossy(&output.stdout).contains("Missing(Function(FuncId(0)))"));
}

#[test]
fn bodyless_reachable_callee_refuses_while_partial_claim_stays_disclosed() {
    let dir = tempfile::tempdir().expect("tempdir");
    let path = dir.path().join("input.json");
    let mut module = build_valid_module();
    module.functions[0].blocks[0].body.insert(
        0,
        InstrNode::new(Inst::Call {
            callee: FuncId(71),
            args: vec![],
        }),
    );
    module.functions.push(Function::new(
        FuncId(71),
        "external",
        module.functions[0].ty,
        BlockId(0),
    ));
    module.completeness = Some(ModuleCompleteness::Partial(vec![UnloweredRow {
        symbol: "external".into(),
        display_path: None,
        reason: "not lowered".into(),
    }]));
    let bytes = serde_json::to_vec(&module).expect("json");
    fs::write(&path, &bytes).expect("write");
    let output = trust_ir_cmd()
        .args(["dependencies", "--root", "0"])
        .arg(&path)
        .output()
        .expect("run");
    assert_eq!(output.status.code(), Some(1), "{output:?}");
    let text = String::from_utf8(output.stdout).expect("utf8");
    assert!(text.contains("BodylessFunction(FuncId(71))"), "{text}");
    assert!(text.contains("completeness=Some(Partial"), "{text}");
    assert!(text.contains("functions=2"), "{text}");
    assert_eq!(fs::read(path).expect("read"), bytes);
}

#[test]
fn a_drop_is_refused_because_its_destructor_names_no_function() {
    let dir = tempfile::tempdir().expect("tempdir");
    let path = dir.path().join("input.json");
    let mut module = build_valid_module();
    let pointer = module.functions[0].blocks[0].params[0].0;
    module.functions[0].blocks[0].body.insert(
        0,
        InstrNode::new(Inst::Drop {
            ty: trust_ir::Ty::I64,
            ptr: pointer,
        }),
    );
    fs::write(&path, serde_json::to_vec(&module).expect("json")).expect("write");
    let output = trust_ir_cmd()
        .args(["dependencies", "--root", "0"])
        .arg(&path)
        .output()
        .expect("run");
    assert_eq!(output.status.code(), Some(1), "{output:?}");
    let text = String::from_utf8(output.stdout).expect("utf8");
    assert!(text.contains("ImplicitDestructor(I64)"), "{text}");
    assert!(text.contains("destructors are refused"), "{text}");
}

/// Amendment D (§20): with a drop-glue row, the same drop is a call edge to
/// its glue, which the census then walks like any callee.
#[test]
fn a_drop_reaches_its_glue_in_the_dependency_census() {
    let dir = tempfile::tempdir().expect("tempdir");
    let path = dir.path().join("input.json");
    let mut module = build_valid_module();
    let dropped = trust_ir::Ty::Struct(trust_ir::StructId(0));
    module.add_struct(trust_ir::StructDef {
        id: trust_ir::StructId(0),
        name: "Owned".into(),
        fields: vec![],
        size: None,
        align: None,
        repr: Default::default(),
        origin: None,
    });
    let pointer = module.functions[0].blocks[0].params[0].0;
    module.functions[0].blocks[0].body.insert(
        0,
        InstrNode::new(Inst::Drop {
            ty: dropped.clone(),
            ptr: pointer,
        }),
    );
    let mut glue = Function::new(FuncId(7), "drop_owned", module.functions[0].ty, BlockId(0));
    let mut block = trust_ir::Block::new(BlockId(0));
    block
        .body
        .push(InstrNode::new(Inst::Return { values: vec![] }));
    glue.blocks.push(block);
    module.functions.push(glue);
    module.set_drop_glue(dropped, FuncId(7)).expect("one row");
    fs::write(&path, serde_json::to_vec(&module).expect("json")).expect("write");
    let output = trust_ir_cmd()
        .args(["dependencies", "--root", "0"])
        .arg(&path)
        .output()
        .expect("run");
    let text = String::from_utf8(output.stdout).expect("utf8");
    assert!(text.contains("node Function(FuncId(7))"), "{text}");
    assert!(!text.contains("ImplicitDestructor"), "{text}");
}

#[test]
fn malformed_input_is_an_io_parse_error_not_a_census_pass() {
    let dir = tempfile::tempdir().expect("tempdir");
    let path = dir.path().join("input.json");
    fs::write(&path, b"{bad-json").expect("write");
    let output = trust_ir_cmd()
        .args(["dependencies", "--root", "0"])
        .arg(path)
        .output()
        .expect("run");
    assert_eq!(output.status.code(), Some(2), "{output:?}");
    assert!(!String::from_utf8_lossy(&output.stdout).contains("refusals=0"));
}

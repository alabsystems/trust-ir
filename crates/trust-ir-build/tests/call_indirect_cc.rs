// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// CallIndirect.calling_conv: the indirect-call ABI declaration (a direct Call's
// convention is the callee Function's calling_conv; an indirect call has no
// statically-known callee, so it declares the expected ABI). Round-trips
// through binary; the conformance corpus (inst_control) covers all formats.

#![cfg(feature = "binary")]

use trust_ir::inst::Inst;
use trust_ir::{CallingConv, Ty};
use trust_ir_build::ModuleBuilder;

/// Back-compat: a serde blob produced before `calling_conv` existed (pre-v12)
/// has no such key/element. The field carries `#[serde(default)]`, so it must
/// deserialize to `CallingConv::C` rather than failing with "missing field".
#[cfg(feature = "serde")]
#[test]
fn call_indirect_missing_calling_conv_deserializes_as_c() {
    use trust_ir::value::{FuncTyId, ValueId};
    let inst = Inst::CallIndirect {
        callee: ValueId::new(0),
        sig: FuncTyId::new(0),
        args: vec![ValueId::new(1)],
        calling_conv: CallingConv::Swift,
    };
    // Round-trip to JSON, then strip the key to emulate a legacy blob.
    let mut json = serde_json::to_value(&inst).expect("serialize");
    let removed = json["CallIndirect"]
        .as_object_mut()
        .expect("CallIndirect object")
        .remove("calling_conv");
    assert!(
        removed.is_some(),
        "fixture must have had a calling_conv key"
    );
    let back: Inst =
        serde_json::from_value(json).expect("legacy CallIndirect without calling_conv must parse");
    match back {
        Inst::CallIndirect { calling_conv, .. } => assert_eq!(calling_conv, CallingConv::C),
        other => panic!("expected CallIndirect, got {other:?}"),
    }
}

#[test]
fn call_indirect_cc_round_trips_binary() {
    let mut mb = ModuleBuilder::new("cc");
    // helper signature: (i32) -> i32
    let helper = mb.add_func_type(vec![Ty::I32], vec![Ty::I32]);
    let ft = mb.add_func_type(vec![Ty::Ptr, Ty::I32], vec![Ty::I32]);
    {
        let mut fb = mb.function("f", ft);
        let entry = fb.create_block();
        let fptr = fb.add_block_param(entry, Ty::Ptr);
        let x = fb.add_block_param(entry, Ty::I32);
        fb.switch_to_block(entry);
        let r = fb.call_indirect_cc(fptr, helper, vec![x], CallingConv::Swift);
        fb.ret(vec![r]);
        fb.build();
    }
    let m = mb.build().expect("ModuleBuilder::build: test fixture");

    // The builder recorded the declared ABI.
    match &m.functions[0].blocks[0].body[0].inst {
        Inst::CallIndirect { calling_conv, .. } => assert_eq!(*calling_conv, CallingConv::Swift),
        other => panic!("expected CallIndirect, got {other:?}"),
    }

    let bytes = trust_ir::binary::serialize_module(&m).expect("serialize_module: test fixture");
    let back = trust_ir::binary::deserialize_module(&bytes).expect("binary round trip");
    match &back.functions[0].blocks[0].body[0].inst {
        Inst::CallIndirect { calling_conv, .. } => assert_eq!(*calling_conv, CallingConv::Swift),
        other => panic!("expected CallIndirect, got {other:?}"),
    }

    // The default builder method keeps the C convention.
    let mut mb2 = ModuleBuilder::new("cc2");
    let helper2 = mb2.add_func_type(vec![], vec![]);
    let ft2 = mb2.add_func_type(vec![Ty::Ptr], vec![]);
    {
        let mut fb = mb2.function("g", ft2);
        let entry = fb.create_block();
        let fptr = fb.add_block_param(entry, Ty::Ptr);
        fb.switch_to_block(entry);
        fb.call_indirect_void(fptr, helper2, vec![]);
        fb.ret(vec![]);
        fb.build();
    }
    let m2 = mb2.build().expect("ModuleBuilder::build: test fixture");
    match &m2.functions[0].blocks[0].body[0].inst {
        Inst::CallIndirect { calling_conv, .. } => assert_eq!(*calling_conv, CallingConv::C),
        other => panic!("expected CallIndirect, got {other:?}"),
    }
}

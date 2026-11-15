// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
pub(super) fn strukt(id: u32, repr: StructRepr) -> trust_ir::StructDef {
    trust_ir::StructDef {
        id: StructId::new(id),
        name: format!("s{id}"),
        fields: vec![],
        size: None,
        align: None,
        repr,
        origin: None,
    }
}
pub(super) fn function(
    id: u32,
    name: &str,
    conv: CallingConv,
    linkage: Linkage,
    body: bool,
) -> Function {
    let mut function = Function::new(FuncId::new(id), name, FuncTyId::new(0), BlockId::new(0));
    function.calling_conv = conv;
    function.linkage = linkage;
    if body {
        function.blocks.push(Block::new(BlockId::new(0)));
    }
    function
}
pub(super) fn fixture() -> Module {
    let mut module = Module::new("ABI");
    module.structs = vec![strukt(1, StructRepr::Rust), strukt(2, StructRepr::C)];
    module.func_types = vec![trust_ir::FuncTy::unrecorded(
        vec![
            Ty::Struct(StructId::new(1)),
            Ty::Struct(StructId::new(99)),
            Ty::Ref(Box::new(Ty::Struct(StructId::new(1)))),
            Ty::Struct(StructId::new(1)),
        ],
        vec![
            Ty::Struct(StructId::new(1)),
            Ty::Tuple(vec![Ty::Struct(StructId::new(1))]),
        ],
        true,
    )];
    module.functions = vec![
        function(7, "firstλ", CallingConv::C, Linkage::External, false),
        function(
            7,
            "secondλ",
            CallingConv::CUnwind,
            Linkage::ExternalWeak,
            false,
        ),
    ];
    module
}
pub(super) fn linkages() -> [Linkage; 9] {
    [
        Linkage::External,
        Linkage::Internal,
        Linkage::Private,
        Linkage::Weak,
        Linkage::LinkOnce,
        Linkage::AvailableExternally,
        Linkage::ExternalWeak,
        Linkage::WeakOdr,
        Linkage::LinkOnceOdr,
    ]
}

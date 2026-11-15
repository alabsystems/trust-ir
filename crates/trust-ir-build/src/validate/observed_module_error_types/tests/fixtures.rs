// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
pub(super) fn global(name: &str, ty: Ty, align: Option<u32>) -> Global {
    Global {
        name: name.into(),
        ty,
        mutable: false,
        initializer: None,
        linkage: Linkage::Internal,
        tls: None,
        align,
        section: None,
        visibility: Default::default(),
        retained: false,
    }
}
pub(super) fn field(name: &str, ty: Ty) -> FieldDef {
    FieldDef {
        name: name.into(),
        ty,
        offset: None,
    }
}
pub(super) fn function(
    name: &str,
    params: Vec<(ValueId, Ty)>,
    instructions: Vec<Inst>,
) -> Function {
    let mut f = Function::new(FuncId::new(119), name, FuncTyId::new(0), BlockId::new(42));
    let mut block = Block::new(BlockId::new(42));
    block.params = params;
    block.body = instructions.into_iter().map(InstrNode::new).collect();
    f.blocks.push(block);
    f
}
pub(super) fn fixture() -> Module {
    let mut module = Module::new("poison");
    module
        .types
        .push(Ty::Tuple(vec![Ty::Error, Ty::Ref(Box::new(Ty::Error))]));
    module.func_types.push(FuncTy {
        params: vec![Ty::Error],
        returns: vec![Ty::Tuple(vec![Ty::Error; 2])],
        abi: None,
        is_vararg: false,
    });
    module.drop_glue.push(DropGlueEntry {
        glue: FuncId::new(1),
        ty: Ty::Error,
    });
    module
        .globals
        .push(global("G", Ty::Tuple(vec![Ty::Error; 2]), Some(3)));
    module.structs.push(StructDef {
        id: StructId::new(0),
        name: "S".into(),
        fields: vec![field("sf", Ty::Error)],
        size: None,
        align: None,
        repr: StructRepr::Rust,
        origin: None,
    });
    module.records.push(RecordDef {
        id: RecordId::new(0),
        name: "R".into(),
        fields: vec![field("rf", Ty::Error)],
    });
    module.enums.push(EnumDef::new(
        EnumId::new(0),
        "E",
        vec![EnumVariant {
            name: "V".into(),
            fields: vec![Ty::Tuple(vec![Ty::Error; 2])],
            field_names: vec![],
        }],
    ));
    module.closure_types.push(ClosureTy {
        func: FuncTyId::new(0),
        captures: vec![Ty::Error],
    });
    let mut dialect = trust_ir::dialect::DialectInst::new("poison", "types");
    dialect.result_tys.push(Ty::Error);
    dialect.attrs.push(trust_ir::dialect::AttrEntry {
        name: "at".into(),
        value: trust_ir::dialect::AttrValue::Ty(Ty::Tuple(vec![Ty::Error; 2])),
    });
    module.functions.push(function(
        "F",
        vec![(ValueId::new(99), Ty::Error)],
        vec![
            Inst::Cast {
                op: CastOp::Bitcast,
                src_ty: Ty::Error,
                dst_ty: Ty::Tuple(vec![Ty::Error; 2]),
                operand: ValueId::new(0),
            },
            Inst::DialectOp(Box::new(dialect)),
        ],
    ));
    module
}

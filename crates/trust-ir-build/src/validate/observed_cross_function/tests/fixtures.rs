// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
use trust_ir::DialectTy;
use trust_ir::ty::{EnumDef, EnumTagRepr, EnumVariant};
use trust_ir::value::EnumId;
pub(super) fn fixture() -> Module {
    let mut m = Module::new("");
    m.types = vec![Ty::Bool, Ty::U8];
    m.func_types = vec![
        FuncTy::unrecorded(vec![Ty::Bool, Ty::U64, Ty::Ptr], vec![Ty::Bool], false),
        FuncTy::unrecorded(vec![Ty::U64], vec![Ty::U64], false),
    ];
    let mut f = Function::new(
        FuncId::new(6301),
        "caller",
        FuncTyId::new(0),
        BlockId::new(1),
    );
    let mut b = Block::new(f.entry);
    b.params = vec![(v(0), Ty::Bool), (v(1), Ty::U64), (v(2), Ty::Ptr)];
    b.body = vec![InstrNode::new(Inst::Return { values: vec![v(0)] })];
    f.blocks.push(b);
    m.functions = vec![
        f,
        Function::new(FuncId::new(9), "target", FuncTyId::new(1), BlockId::new(0)),
    ];
    m
}
pub(super) fn replace(m: &mut Module, nodes: Vec<Inst>) {
    m.functions[0].blocks[0].body = nodes.into_iter().map(InstrNode::new).collect();
}
pub(super) fn indirect(family: u8, callee: u32, sig: u32, args: Vec<ValueId>) -> Inst {
    match family {
        0 => Inst::CallIndirect {
            callee: v(callee),
            sig: FuncTyId::new(sig),
            args,
            calling_conv: CallingConv::C,
        },
        1 => Inst::CallIndirectCannotUnwind {
            callee: v(callee),
            sig: FuncTyId::new(sig),
            args,
            calling_conv: CallingConv::C,
        },
        _ => Inst::InvokeIndirect {
            callee: v(callee),
            sig: FuncTyId::new(sig),
            args,
            calling_conv: CallingConv::C,
            normal_dest: BlockId::new(2),
            normal_args: vec![],
            unwind_dest: BlockId::new(3),
        },
    }
}
pub(super) fn broad() -> Module {
    let mut m = fixture();
    m.functions[0].attrs.readnone = true;
    m.func_types[0].params = vec![];
    replace(
        &mut m,
        vec![
            Inst::Store {
                ty: Ty::Bool,
                ptr: v(2),
                value: v(0),
                volatile: false,
                align: None,
            },
            Inst::Drop {
                ptr: v(0),
                ty: Ty::Bool,
            },
            Inst::Call {
                callee: FuncId::new(9),
                args: vec![v(0), v(2)],
            },
            Inst::CallCannotUnwind {
                callee: FuncId::new(999),
                args: vec![],
            },
            Inst::Invoke {
                callee: FuncId::new(9),
                args: vec![v(0)],
                normal_dest: BlockId::new(2),
                normal_args: vec![],
                unwind_dest: BlockId::new(3),
            },
            Inst::SeqMap {
                ty: Ty::Bool,
                seq: v(0),
                fwd: FuncId::new(9),
            },
            indirect(0, 2, 1, vec![v(0), v(2)]),
            Inst::ExtractField {
                ty: Ty::Bool,
                aggregate: v(1),
                field: 9,
            },
            Inst::InsertField {
                ty: Ty::Bool,
                aggregate: v(1),
                field: 9,
                value: v(0),
            },
            Inst::MakeAggregate {
                ty: Ty::Bool,
                variant: None,
                fields: vec![v(0)],
            },
            Inst::ArraySplat {
                ty: Ty::Array(TyId::new(0), 0),
                value: v(1),
            },
            Inst::DialectOp(Box::new(DialectInst::new("gpu", "not_an_op"))),
            Inst::Return { values: vec![v(1)] },
        ],
    );
    m
}
fn variant(name: &str, fields: Vec<Ty>) -> EnumVariant {
    EnumVariant {
        name: name.into(),
        fields,
        field_names: vec![],
    }
}
fn switch(value: u32, values: Vec<Constant>) -> InstrNode {
    InstrNode::new(Inst::Switch {
        value: v(value),
        default: BlockId::new(9),
        default_args: vec![],
        cases: values
            .into_iter()
            .map(|value| trust_ir::inst::SwitchCase {
                value,
                target: BlockId::new(9),
                args: vec![],
            })
            .collect(),
        exhaustive_enum_unreachable: true,
    })
}
fn cast(op: CastOp, src: Ty, dst: Ty, operand: u32, result: u32) -> InstrNode {
    InstrNode::new(Inst::Cast {
        op,
        src_ty: src,
        dst_ty: dst,
        operand: v(operand),
    })
    .with_result(v(result))
}
pub(super) fn enum_fixture() -> Module {
    let mut m = Module::new("");
    m.enums.push(EnumDef::new(
        EnumId::new(7),
        "E",
        vec![variant("Zero", vec![]), variant("One", vec![])],
    ));
    m.func_types.push(FuncTy::unrecorded(
        vec![Ty::Enum(EnumId::new(7))],
        vec![],
        false,
    ));
    let mut f = Function::new(
        FuncId::new(6101),
        "caller",
        FuncTyId::new(0),
        BlockId::new(1),
    );
    let mut b = Block::new(f.entry);
    b.params = vec![(v(0), Ty::Enum(EnumId::new(7)))];
    b.body = vec![
        InstrNode::new(Inst::ExtractField {
            ty: Ty::U8,
            aggregate: v(0),
            field: 0,
        })
        .with_result(v(1)),
        switch(1, vec![Constant::Int(0)]),
    ];
    f.blocks.push(b);
    let mut end = Block::new(BlockId::new(9));
    end.body.push(InstrNode::new(Inst::Unreachable));
    f.blocks.push(end);
    m.functions.push(f);
    m
}
pub(super) fn signed_enum() -> Module {
    let mut m = enum_fixture();
    m.enums[0].discriminants = vec![Some(-1), Some(0)];
    m.enums[0].repr = Some(EnumTagRepr::I8);
    m.functions[0].blocks[0].body = vec![
        InstrNode::new(Inst::ExtractField {
            ty: Ty::I8,
            aggregate: v(0),
            field: 0,
        })
        .with_result(v(1)),
        cast(CastOp::SExt, Ty::I8, Ty::I16, 1, 2),
        cast(CastOp::SExt, Ty::I16, Ty::I32, 2, 3),
        switch(3, vec![Constant::Int(-1), Constant::Int(0)]),
    ];
    m
}
fn handle() -> Ty {
    Ty::handle("Name", "rt::Name")
}
fn dialect() -> Ty {
    Ty::Dialect(Box::new(DialectTy::new("ns", "Name", 1)))
}
fn mixed() -> Ty {
    Ty::Tuple(vec![handle(), dialect()])
}
pub(super) fn nominal_fixture() -> Module {
    let mut m = Module::new("");
    m.func_types = vec![
        FuncTy::unrecorded(vec![], vec![], false),
        FuncTy::unrecorded(vec![handle()], vec![handle()], false),
        FuncTy::unrecorded(vec![dialect()], vec![dialect()], false),
        FuncTy::unrecorded(vec![dialect()], vec![Ty::Bool], false),
        FuncTy::unrecorded(vec![handle()], vec![Ty::Bool], false),
    ];
    let mut f = Function::new(FuncId::new(1101), "F", FuncTyId::new(0), BlockId::new(1));
    let mut b = Block::new(f.entry);
    b.params = vec![
        (v(0), Ty::Bool),
        (v(1), handle()),
        (v(2), dialect()),
        (v(3), mixed()),
        (v(4), Ty::Ptr),
        (v(5), Ty::Func(FuncTyId::new(1))),
        (v(6), Ty::U8),
        (v(7), Ty::Func(FuncTyId::new(2))),
        (v(8), Ty::Func(FuncTyId::new(99))),
    ];
    b.body = vec![
        InstrNode::new(Inst::Alloca {
            ty: handle(),
            count: None,
            align: None,
        })
        .with_result(v(10)),
        InstrNode::new(Inst::Store {
            ty: handle(),
            ptr: v(10),
            value: v(1),
            volatile: false,
            align: None,
        }),
        InstrNode::new(Inst::Load {
            ty: handle(),
            ptr: v(10),
            volatile: false,
            align: None,
        })
        .with_result(v(11)),
        InstrNode::new(Inst::Return { values: vec![] }),
    ];
    f.blocks.push(b);
    m.functions.push(f);
    m
}

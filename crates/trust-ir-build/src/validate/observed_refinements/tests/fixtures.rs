// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
pub(super) fn v(i: u32) -> ValueId {
    ValueId::new(i)
}
pub(super) fn b(i: u32) -> BlockId {
    BlockId::new(i)
}
pub(super) fn r(p: u32) -> Ty {
    Ty::Refine(TyId::new(0), PredId::new(p))
}
pub(super) fn sig(params: Vec<Ty>, returns: Vec<Ty>) -> FuncTy {
    FuncTy {
        params,
        returns,
        abi: None,
        is_vararg: false,
    }
}
pub(super) fn node(inst: Inst, results: &[u32]) -> InstrNode {
    InstrNode::new(inst).with_results(results.iter().copied().map(v))
}
pub(super) fn function(
    id: u32,
    signature: u32,
    params: Vec<(ValueId, Ty)>,
    body: Vec<InstrNode>,
) -> Function {
    let mut f = Function::new(
        FuncId::new(id),
        format!("fn λ'{id}\0"),
        FuncTyId::new(signature),
        b(0),
    );
    let mut block = Block::new(b(0));
    block.params = params;
    block.body = body;
    f.blocks.push(block);
    f
}
pub(super) fn module() -> Module {
    let mut m = Module::new("full refinement λ\0");
    m.types = vec![Ty::I32, Ty::Ptr, Ty::F32];
    m.universes = vec![
        Universe::IntRange { lo: 1, hi: 3 },
        Universe::Members(vec![Constant::Int(1), Constant::Int(2), Constant::Int(3)]),
    ];
    m.predicates = vec![
        Pred::Top,
        Pred::Interval { lo: 1, hi: 9 },
        Pred::Interval { lo: 5, hi: 9 },
        Pred::NonZero,
        Pred::Bottom,
        Pred::FiniteSet(vec![Constant::Int(1), Constant::Int(3)]),
        Pred::InUniverse(UnivId::new(0), Space::Member),
        Pred::InUniverse(UnivId::new(0), Space::Index),
        Pred::Conj(vec![PredId::new(1), PredId::new(3)]),
        Pred::Disj(vec![PredId::new(0), PredId::new(1)]),
    ];
    m.func_types = vec![sig(vec![Ty::I32], vec![r(2)]), sig(vec![r(2)], vec![])];
    m
}
pub(super) fn small() -> Module {
    let mut m = module();
    m.functions.push(function(
        10,
        0,
        vec![(v(0), Ty::I32)],
        vec![node(Inst::Return { values: vec![v(0)] }, &[])],
    ));
    m
}
pub(super) fn calls() -> Module {
    let mut m = module();
    let mut f = function(
        10,
        0,
        vec![(v(0), Ty::I32), (v(90), Ty::Ptr)],
        vec![
            node(
                Inst::Call {
                    callee: FuncId::new(20),
                    args: vec![v(0)],
                },
                &[],
            ),
            node(
                Inst::CallCannotUnwind {
                    callee: FuncId::new(20),
                    args: vec![v(0)],
                },
                &[],
            ),
            node(
                Inst::Invoke {
                    callee: FuncId::new(20),
                    args: vec![v(0)],
                    normal_dest: b(1),
                    normal_args: vec![v(0)],
                    unwind_dest: b(2),
                },
                &[],
            ),
            node(
                Inst::CallIndirect {
                    callee: v(90),
                    sig: FuncTyId::new(1),
                    args: vec![v(0)],
                    calling_conv: CallingConv::Rust,
                },
                &[],
            ),
            node(
                Inst::CallIndirectCannotUnwind {
                    callee: v(90),
                    sig: FuncTyId::new(1),
                    args: vec![v(0)],
                    calling_conv: CallingConv::Rust,
                },
                &[],
            ),
            node(
                Inst::InvokeIndirect {
                    callee: v(90),
                    sig: FuncTyId::new(1),
                    args: vec![v(0)],
                    calling_conv: CallingConv::Rust,
                    normal_dest: b(1),
                    normal_args: vec![v(0)],
                    unwind_dest: b(2),
                },
                &[],
            ),
            node(Inst::Return { values: vec![v(0)] }, &[]),
        ],
    );
    let mut join = Block::new(b(1));
    join.params = vec![(v(11), r(2))];
    join.body = vec![node(
        Inst::Return {
            values: vec![v(11)],
        },
        &[],
    )];
    f.blocks.push(join);
    f.blocks.push(Block::new(b(2)));
    m.functions = vec![f, function(20, 1, vec![], vec![])];
    m
}
pub(super) fn strukt(id: u32, ty: Ty) -> StructDef {
    StructDef {
        id: StructId::new(id),
        name: format!("S{id}λ"),
        fields: vec![FieldDef {
            name: "field'\0λ".into(),
            ty,
            offset: None,
        }],
        size: None,
        align: None,
        repr: StructRepr::Rust,
        origin: None,
    }
}
pub(super) fn enumeration(fields: Vec<Ty>) -> EnumDef {
    EnumDef::new(
        EnumId::new(17),
        "enum λ'",
        fields
            .into_iter()
            .enumerate()
            .map(|(i, ty)| EnumVariant {
                name: format!("variant {i}λ'"),
                fields: vec![ty],
                field_names: vec![],
            })
            .collect(),
    )
}
pub(super) fn aggregates() -> Module {
    let mut m = module();
    m.types.push(r(2));
    m.structs = vec![strukt(31, r(2))];
    m.records = vec![RecordDef {
        id: RecordId::new(9),
        name: "record λ".into(),
        fields: vec![FieldDef {
            name: "field".into(),
            ty: r(2),
            offset: None,
        }],
    }];
    m.enums = vec![enumeration(vec![r(2), r(1)])];
    let mut body = Vec::new();
    let types = [
        Ty::Struct(StructId::new(31)),
        Ty::Record(RecordId::new(9)),
        Ty::Tuple(vec![r(2)]),
        Ty::Array(TyId::new(3), 2),
        Ty::Vector(Box::new(r(2)), 2),
        Ty::Sequence(TyId::new(3)),
        Ty::Enum(EnumId::new(17)),
    ];
    let mut params = vec![(v(0), Ty::I32)];
    for (i, ty) in types.iter().enumerate() {
        let id = 100 + i as u32;
        params.push((v(id), ty.clone()));
        body.push(node(
            Inst::InsertField {
                ty: ty.clone(),
                aggregate: v(id),
                field: if matches!(ty, Ty::Enum(_)) { 1 } else { 0 },
                value: v(0),
            },
            &[],
        ));
        body.push(node(
            Inst::ExtractField {
                ty: r(6),
                aggregate: v(id),
                field: if matches!(ty, Ty::Enum(_)) { 1 } else { 0 },
            },
            &[],
        ));
        body.push(node(
            Inst::InsertElement {
                ty: ty.clone(),
                array: v(id),
                index: v(0),
                value: v(0),
            },
            &[],
        ));
        body.push(node(
            Inst::ExtractElement {
                ty: r(6),
                array: v(id),
                index: v(0),
            },
            &[],
        ));
        body.push(node(
            Inst::MakeAggregate {
                ty: ty.clone(),
                variant: matches!(ty, Ty::Enum(_)).then_some(0),
                fields: vec![v(0), v(0)],
            },
            &[],
        ));
        body.push(node(
            Inst::ArraySplat {
                ty: ty.clone(),
                value: v(0),
            },
            &[],
        ));
    }
    m.functions.push(function(10, 0, params, body));
    m
}

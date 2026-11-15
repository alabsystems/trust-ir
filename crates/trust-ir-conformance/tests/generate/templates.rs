// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// The level-S template corpus (amendment S, `docs/SPEC_RATIFICATIONS.md` §22):
// one template per feature, golden in four formats under
// `tests/fixtures/templates/`, each with the scripted hosts that instantiate it
// at chosen arguments and the hand-monomorphized level-R twin an instance must
// behave like. Names are features, never versions.
//
// Every template here passes `validate_template`, and every scripted host's
// instance passes `validate_module`.

use trust_ir::template::{
    Destructor, GlobalAnswer, HoleAnswer, InstArg, InstanceHeader, LinkAnswer, ScriptedAnswer,
    ScriptedHost,
};
use trust_ir::template::{
    HoleDef, HoleKind, HostKey, TEMPLATE_BODY_NAME, Template, TemplateArg, TemplateHeader,
    TemplateParam, TypeContract, hole_row_name,
};
use trust_ir::{
    BlockG, BlockId, BodyGate, CallingConv, Constant, ConstantG, Endianness, EnumDef, EnumTagRepr,
    EnumVariant, FieldDef, FuncId, FuncTy, FuncTyG, FunctionG, GlobalG, HoleId, InstG, InstrNodeG,
    Linkage, ModuleG, ParamId, StructDef, StructId, StructRepr, TargetInfo, TemplateRef, Ty, TyG,
    ValueId, Visibility,
};

type T = TemplateRef;

use trust_ir::{IdSpaceExhausted, InterpretError};

/// Why the template corpus could not be built: a full module table (no
/// fixture here adds more than two rows to a fresh module, but the door's
/// refusal is typed, never assumed away) or an argument or result value out
/// of its type's range. The test that calls [`instances`] decides; this file
/// is compiled into the library the verified survey examines.
#[derive(Debug, Clone, PartialEq)]
pub enum TemplateFixtureError {
    /// A module table door refused.
    Table(IdSpaceExhausted),
    /// A golden value is out of its type's range.
    Value(InterpretError),
}

impl From<IdSpaceExhausted> for TemplateFixtureError {
    fn from(exhausted: IdSpaceExhausted) -> Self {
        Self::Table(exhausted)
    }
}

impl From<InterpretError> for TemplateFixtureError {
    fn from(error: InterpretError) -> Self {
        Self::Value(error)
    }
}

impl std::fmt::Display for TemplateFixtureError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Table(exhausted) => write!(f, "{exhausted}"),
            Self::Value(error) => write!(f, "{error}"),
        }
    }
}

impl std::error::Error for TemplateFixtureError {}

fn v(n: u32) -> ValueId {
    ValueId::new(n)
}
fn b(n: u32) -> BlockId {
    BlockId::new(n)
}
/// A type parameter.
pub fn param(n: u32) -> TyG<T> {
    TyG::Ext(TemplateRef::Param(ParamId::new(n)))
}
/// A type hole.
pub fn hole(n: u32) -> TyG<T> {
    TyG::Ext(TemplateRef::Hole(HoleId::new(n)))
}
fn key(item: &str) -> HostKey {
    HostKey::new("rust", item.as_bytes().to_vec())
}
fn node(inst: InstG<T>) -> InstrNodeG<T> {
    InstrNodeG::new(inst)
}
fn result(inst: InstG<T>, value: u32) -> InstrNodeG<T> {
    InstrNodeG::new(inst).with_result(v(value))
}

/// The target every corpus template is built for.
pub fn target() -> TargetInfo {
    TargetInfo {
        triple: "aarch64-apple-darwin".into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: None,
        struct_passing: Default::default(),
    }
}

fn module(name: &str) -> ModuleG<T> {
    let mut m = ModuleG::new(name);
    m.target_info = Some(target());
    m
}

fn body(
    m: &mut ModuleG<T>,
    params: Vec<TyG<T>>,
    returns: Vec<TyG<T>>,
) -> Result<FunctionG<T>, IdSpaceExhausted> {
    let ty = m.add_func_type(FuncTyG {
        abi: None,
        params,
        returns,
        is_vararg: false,
    })?;
    Ok(FunctionG::new(FuncId::new(0), TEMPLATE_BODY_NAME, ty, b(0)))
}

fn header(identity: &str, params: Vec<TemplateParam>, holes: Vec<HoleDef>) -> TemplateHeader {
    TemplateHeader {
        identity: identity.into(),
        params,
        holes,
    }
}

fn type_hole(contract: TypeContract, item: &str, args: Vec<TemplateArg>) -> HoleDef {
    HoleDef {
        kind: HoleKind::Type { contract },
        key: key(item),
        args,
    }
}

/// An instance header the scripted hosts answer with.
pub fn instance(symbol: &str) -> InstanceHeader {
    InstanceHeader {
        symbol: symbol.into(),
        linkage: Linkage::Internal,
        visibility: Visibility::Default,
        calling_conv: CallingConv::Rust,
        attrs: Default::default(),
        display_path: Some(symbol.replace('_', "::")),
        body_gate: BodyGate::Ungated,
    }
}

fn struct_def(id: u32, name: &str, fields: Vec<(Ty, u64)>, size: u64, align: u64) -> StructDef {
    StructDef {
        id: StructId::new(id),
        name: name.into(),
        fields: fields
            .into_iter()
            .enumerate()
            .map(|(i, (ty, offset))| FieldDef {
                name: format!("f{i}"),
                ty,
                offset: Some(offset),
            })
            .collect(),
        size: Some(size),
        align: Some(align),
        repr: StructRepr::Rust,
        origin: None,
    }
}

// ---------------------------------------------------------------------------
// The templates
// ---------------------------------------------------------------------------

/// `fn identity<T>(x: T) -> T { x }`.
pub fn ident_param() -> Result<Template, IdSpaceExhausted> {
    let mut m = module("core");
    let mut f = body(&mut m, vec![param(0)], vec![param(0)])?;
    let mut entry = BlockG::new(b(0)).with_param(v(0), param(0));
    entry.body.push(node(InstG::Return { values: vec![v(0)] }));
    f.blocks.push(entry);
    m.functions.push(f);
    Ok(Template {
        header: header("core::convert::identity", vec![TemplateParam::Type], vec![]),
        module: m,
    })
}

/// Compare two values whose actual host type must be a thin pointer.
/// This contract supplies no memory access or source-language authority.
pub fn thin_pointer_compare() -> Result<Template, IdSpaceExhausted> {
    let mut m = module("pointer_contract");
    let mut f = body(&mut m, vec![hole(0), hole(0)], vec![TyG::Bool])?;
    let mut entry = BlockG::new(b(0))
        .with_param(v(0), hole(0))
        .with_param(v(1), hole(0));
    entry.body.push(result(
        InstG::ICmp {
            op: trust_ir::ICmpOp::Eq,
            ty: hole(0),
            lhs: v(0),
            rhs: v(1),
        },
        2,
    ));
    entry.body.push(node(InstG::Return { values: vec![v(2)] }));
    f.blocks.push(entry);
    m.functions.push(f);
    Ok(Template {
        header: header(
            "source_pointer_equality",
            vec![TemplateParam::Type],
            vec![type_hole(
                TypeContract::ThinPointer,
                "source_pointer_representation",
                vec![TemplateArg::Type(param(0))],
            )],
        ),
        module: m,
    })
}

/// `fn len<T>(v: &Vec<T>) -> usize { v.len }`: a struct contract whose first
/// field names a LATER hole (review R6) and an opaque hole.
pub fn struct_contract_field_read() -> Result<Template, IdSpaceExhausted> {
    let mut m = module("alloc");
    let mut f = body(&mut m, vec![TyG::Ptr], vec![TyG::Usize])?;
    let mut entry = BlockG::new(b(0)).with_param(v(0), TyG::Ptr);
    entry.body.push(result(
        InstG::Load {
            ty: hole(0),
            ptr: v(0),
            volatile: false,
            align: None,
        },
        1,
    ));
    entry.body.push(result(
        InstG::ExtractField {
            ty: TyG::Usize,
            aggregate: v(1),
            field: 1,
        },
        2,
    ));
    entry.body.push(node(InstG::Return { values: vec![v(2)] }));
    f.blocks.push(entry);
    m.functions.push(f);
    Ok(Template {
        header: header(
            "alloc::vec::Vec::<T>::len",
            vec![TemplateParam::Type],
            vec![
                type_hole(
                    TypeContract::Struct {
                        fields: vec![hole(1), TyG::Usize],
                    },
                    "alloc::vec::Vec",
                    vec![TemplateArg::Type(param(0))],
                ),
                type_hole(
                    TypeContract::Opaque,
                    "alloc::raw_vec::RawVec",
                    vec![TemplateArg::Type(param(0))],
                ),
            ],
        ),
        module: m,
    })
}

/// `fn tag<T>(x: T) -> u8 { Some(x) as tag }`: an enum contract that pins the
/// declared discriminants and repr the body's tag read depends on (review R3).
pub fn enum_contract_match() -> Result<Template, IdSpaceExhausted> {
    let mut m = module("core");
    let mut f = body(&mut m, vec![param(0)], vec![TyG::U8])?;
    let mut entry = BlockG::new(b(0)).with_param(v(0), param(0));
    entry.body.push(result(
        InstG::MakeAggregate {
            ty: hole(0),
            variant: Some(1),
            fields: vec![v(0)],
        },
        1,
    ));
    entry.body.push(result(
        InstG::ExtractField {
            ty: TyG::U8,
            aggregate: v(1),
            field: 0,
        },
        2,
    ));
    entry.body.push(node(InstG::Return { values: vec![v(2)] }));
    f.blocks.push(entry);
    m.functions.push(f);
    Ok(Template {
        header: header(
            "core::option::tag_of_some::<T>",
            vec![TemplateParam::Type],
            vec![type_hole(
                TypeContract::Enum {
                    variants: vec![vec![], vec![param(0)]],
                    discriminants: vec![None, None],
                    repr: Some(EnumTagRepr::U8),
                },
                "core::option::Option",
                vec![TemplateArg::Type(param(0))],
            )],
        ),
        module: m,
    })
}

/// `fn dup<T: Clone>(x: T) -> T { x.clone() }`: a trait call through a bound
/// is a callee hole.
pub fn callee_hole_trait_call() -> Result<Template, IdSpaceExhausted> {
    let mut m = module("core");
    let mut f = body(&mut m, vec![param(0)], vec![param(0)])?;
    let callee_ty = m.add_func_type(FuncTyG {
        abi: None,
        params: vec![param(0)],
        returns: vec![param(0)],
        is_vararg: false,
    })?;
    let mut entry = BlockG::new(b(0)).with_param(v(0), param(0));
    entry.body.push(result(
        InstG::Call {
            callee: FuncId::new(1),
            args: vec![v(0)],
        },
        1,
    ));
    entry.body.push(node(InstG::Return { values: vec![v(1)] }));
    f.blocks.push(entry);
    m.functions.push(f);
    m.functions.push(FunctionG::new(
        FuncId::new(1),
        hole_row_name(HoleId::new(0)),
        callee_ty,
        b(0),
    ));
    Ok(Template {
        header: header(
            "core::clone::dup::<T>",
            vec![TemplateParam::Type],
            vec![HoleDef {
                kind: HoleKind::Callee {
                    decl: FuncId::new(1),
                },
                key: key("core::clone::Clone::clone"),
                args: vec![TemplateArg::Type(param(0))],
            }],
        ),
        module: m,
    })
}

/// `fn size<T>() -> usize { size_of::<T>() }`: a const hole.
pub fn const_hole_size_of() -> Result<Template, IdSpaceExhausted> {
    let mut m = module("core");
    let mut f = body(&mut m, vec![], vec![TyG::Usize])?;
    let mut entry = BlockG::new(b(0));
    entry.body.push(result(
        InstG::Const {
            ty: TyG::Usize,
            value: ConstantG::Ext(TemplateRef::Hole(HoleId::new(0))),
        },
        0,
    ));
    entry.body.push(node(InstG::Return { values: vec![v(0)] }));
    f.blocks.push(entry);
    m.functions.push(f);
    Ok(Template {
        header: header(
            "core::mem::size_of::<T>",
            vec![TemplateParam::Type],
            vec![HoleDef {
                kind: HoleKind::Const { ty: Ty::Usize },
                key: key("core::mem::SizedTypeProperties::SIZE"),
                args: vec![TemplateArg::Type(param(0))],
            }],
        ),
        module: m,
    })
}

/// `fn consume<T>(x: T) { drop(x) }`, its drop the unwinding twin into a
/// cleanup pad: erased at a trivially droppable `T` and at a struct the host
/// says has no destructor (review R1), its dead pad deleted (R2); kept and
/// resolved at a struct with glue.
pub fn drop_at_param() -> Result<Template, IdSpaceExhausted> {
    let mut m = module("core");
    let mut f = body(&mut m, vec![param(0)], vec![])?;
    let mut entry = BlockG::new(b(0)).with_param(v(0), param(0));
    entry.body.push(result(
        InstG::Alloca {
            ty: param(0),
            count: None,
            align: None,
        },
        1,
    ));
    entry.body.push(node(InstG::Store {
        ty: param(0),
        ptr: v(1),
        value: v(0),
        volatile: false,
        align: None,
    }));
    entry.body.push(node(InstG::DropInvoke {
        ty: param(0),
        ptr: v(1),
        normal_dest: b(1),
        normal_args: vec![],
        unwind_dest: b(2),
    }));
    let mut done = BlockG::new(b(1));
    done.body.push(node(InstG::Return { values: vec![] }));
    let mut cleanup = BlockG::new(b(2));
    cleanup.body.push(
        InstrNodeG::new(InstG::LandingPad {
            is_cleanup: true,
            catch_type_indices: vec![],
        })
        .with_results([v(2), v(3)]),
    );
    cleanup.body.push(node(InstG::Resume { exn: v(2) }));
    f.blocks.extend([entry, done, cleanup]);
    m.functions.push(f);
    Ok(Template {
        header: header("core::mem::drop::<T>", vec![TemplateParam::Type], vec![]),
        module: m,
    })
}

/// `fn countdown<T>(n: u64, x: T) -> T { if n == 0 { x } else { countdown::<T>(n - 1, x) } }`:
/// a callee hole the host answers with the instance's own symbol, so the
/// call binds to the body (a self edge, never a duplicate symbol).
pub fn self_recursive_generic() -> Result<Template, IdSpaceExhausted> {
    let mut m = module("core");
    let mut f = body(&mut m, vec![TyG::U64, param(0)], vec![param(0)])?;
    let callee_ty = m.add_func_type(FuncTyG {
        abi: None,
        params: vec![TyG::U64, param(0)],
        returns: vec![param(0)],
        is_vararg: false,
    })?;
    let mut entry = BlockG::new(b(0))
        .with_param(v(0), TyG::U64)
        .with_param(v(1), param(0));
    entry.body.push(result(
        InstG::Const {
            ty: TyG::U64,
            value: ConstantG::Int(0),
        },
        2,
    ));
    entry.body.push(result(
        InstG::ICmp {
            op: trust_ir::ICmpOp::Eq,
            ty: TyG::U64,
            lhs: v(0),
            rhs: v(2),
        },
        3,
    ));
    entry.body.push(node(InstG::CondBr {
        cond: v(3),
        then_target: b(1),
        then_args: vec![],
        else_target: b(2),
        else_args: vec![],
    }));
    let mut base = BlockG::new(b(1));
    base.body.push(node(InstG::Return { values: vec![v(1)] }));
    let mut step = BlockG::new(b(2));
    step.body.push(result(
        InstG::Const {
            ty: TyG::U64,
            value: ConstantG::Int(1),
        },
        4,
    ));
    step.body.push(result(
        InstG::BinOp {
            op: trust_ir::BinOp::Sub,
            ty: TyG::U64,
            lhs: v(0),
            rhs: v(4),
        },
        5,
    ));
    step.body.push(result(
        InstG::Call {
            callee: FuncId::new(1),
            args: vec![v(5), v(1)],
        },
        6,
    ));
    step.body.push(node(InstG::Return { values: vec![v(6)] }));
    f.blocks.extend([entry, base, step]);
    m.functions.push(f);
    m.functions.push(FunctionG::new(
        FuncId::new(1),
        hole_row_name(HoleId::new(0)),
        callee_ty,
        b(0),
    ));
    Ok(Template {
        header: header(
            "core::countdown::<T>",
            vec![TemplateParam::Type],
            vec![HoleDef {
                kind: HoleKind::Callee {
                    decl: FuncId::new(1),
                },
                key: key("core::countdown"),
                args: vec![TemplateArg::Type(param(0))],
            }],
        ),
        module: m,
    })
}

/// `fn n<const N: usize>() -> usize { N + *&N }`: a const parameter in a value
/// position, and a parameter-dependent promoted (`&N`), a global hole the
/// host defines with its ground initializer.
pub fn const_param_value() -> Result<Template, IdSpaceExhausted> {
    let mut m = module("core");
    let mut f = body(&mut m, vec![], vec![TyG::Usize])?;
    let mut entry = BlockG::new(b(0));
    entry.body.push(result(
        InstG::Const {
            ty: TyG::Usize,
            value: ConstantG::Ext(TemplateRef::Param(ParamId::new(0))),
        },
        0,
    ));
    entry.body.push(result(
        InstG::GlobalAddr {
            global: trust_ir::value::GlobalId::new(0),
        },
        1,
    ));
    entry.body.push(result(
        InstG::Load {
            ty: TyG::Usize,
            ptr: v(1),
            volatile: false,
            align: None,
        },
        2,
    ));
    entry.body.push(result(
        InstG::BinOp {
            op: trust_ir::BinOp::Add,
            ty: TyG::Usize,
            lhs: v(0),
            rhs: v(2),
        },
        3,
    ));
    entry.body.push(node(InstG::Return { values: vec![v(3)] }));
    f.blocks.push(entry);
    m.functions.push(f);
    m.globals.push(GlobalG {
        name: hole_row_name(HoleId::new(0)),
        ty: TyG::Usize,
        mutable: false,
        initializer: None,
        linkage: Linkage::default(),
        tls: None,
        align: None,
        section: None,
        visibility: Visibility::default(),
        retained: false,
    });
    Ok(Template {
        header: header(
            "core::n::<N>",
            vec![TemplateParam::Const { ty: Ty::Usize }],
            vec![HoleDef {
                kind: HoleKind::Global {
                    decl: trust_ir::value::GlobalId::new(0),
                },
                key: key("core::n::promoted[0]"),
                args: vec![TemplateArg::Const {
                    value: ConstantG::Ext(TemplateRef::Param(ParamId::new(0))),
                    ty: Ty::Usize,
                }],
            }],
        ),
        module: m,
    })
}

/// `fn pass<T: ?Sized>(x: &T) -> &T { x }`: `T` has no level-R value
/// spelling, so it is a host parameter, and `&T` (thin or fat by `T`) is an
/// opaque type hole over it (review R9).
pub fn host_param_ref() -> Result<Template, IdSpaceExhausted> {
    let mut m = module("core");
    let mut f = body(&mut m, vec![hole(0)], vec![hole(0)])?;
    let mut entry = BlockG::new(b(0)).with_param(v(0), hole(0));
    entry.body.push(node(InstG::Return { values: vec![v(0)] }));
    f.blocks.push(entry);
    m.functions.push(f);
    Ok(Template {
        header: header(
            "core::pass::<T>",
            vec![TemplateParam::Host],
            vec![type_hole(
                TypeContract::Opaque,
                "&T",
                vec![TemplateArg::Host(ParamId::new(0))],
            )],
        ),
        module: m,
    })
}

/// The golden corpus, by feature name.
pub fn corpus() -> Result<Vec<(&'static str, Template)>, IdSpaceExhausted> {
    Ok(vec![
        ("ident_param", ident_param()?),
        ("thin_pointer_compare", thin_pointer_compare()?),
        ("struct_contract_field_read", struct_contract_field_read()?),
        ("enum_contract_match", enum_contract_match()?),
        ("callee_hole_trait_call", callee_hole_trait_call()?),
        ("const_hole_size_of", const_hole_size_of()?),
        ("drop_at_param", drop_at_param()?),
        ("self_recursive_generic", self_recursive_generic()?),
        ("const_param_value", const_param_value()?),
        ("host_param_ref", host_param_ref()?),
    ])
}

// ---------------------------------------------------------------------------
// Scripted hosts: each golden at chosen arguments
// ---------------------------------------------------------------------------

/// The first struct id a scripted host appends: above every template row.
pub const HOST_STRUCT_BASE: u32 = 100;

fn ty_answer(ty: Ty) -> ScriptedAnswer {
    ScriptedAnswer::Answer(HoleAnswer::Type(ty))
}
fn const_answer(value: Constant) -> ScriptedAnswer {
    ScriptedAnswer::Answer(HoleAnswer::Const(value))
}
fn callee_answer(answer: LinkAnswer) -> ScriptedAnswer {
    ScriptedAnswer::Answer(HoleAnswer::Callee(answer))
}
fn global_answer(answer: GlobalAnswer) -> ScriptedAnswer {
    ScriptedAnswer::Answer(HoleAnswer::Global(answer))
}

fn host(symbol: &str) -> ScriptedHost {
    ScriptedHost {
        header: Some(instance(symbol)),
        ..ScriptedHost::default()
    }
}

/// One instantiation of a golden: its host, and what calling the instance's
/// body with `inputs` must return (`None`: not executed in-format, e.g. a
/// bodyless callee).
pub struct Instance {
    pub name: String,
    pub template: Template,
    pub host: ScriptedHost,
    pub run: Option<(Vec<trust_ir::InterpretValue>, Vec<trust_ir::InterpretValue>)>,
}

/// An integer argument or result. `InterpretValue::int` validates the value
/// against the type's range; an out-of-range golden is the builder's refusal,
/// returned to the test that calls [`instances`], never a panic here (this file
/// is compiled into the library the verified survey examines).
fn int(ty: Ty, value: i128) -> trust_ir::InterpretResult<trust_ir::InterpretValue> {
    trust_ir::InterpretValue::int(ty, value)
}

/// Every golden at up to three argument sets, or the refusal of an argument
/// or result value that is out of its type's range.
pub fn instances() -> Result<Vec<Instance>, TemplateFixtureError> {
    let mut out = Vec::new();
    for (right, expected) in [(0, true), (16, false)] {
        let pointer = |address| trust_ir::InterpretValue {
            ty: Ty::Ptr,
            kind: if address == 0 {
                trust_ir::InterpretValueKind::NullPtr
            } else {
                trust_ir::InterpretValueKind::DanglingPtr(address)
            },
        };
        out.push(Instance {
            name: format!("thin_pointer_compare<{right}>"),
            template: thin_pointer_compare()?,
            host: ScriptedHost {
                arguments: vec![InstArg::Type(Ty::U64)],
                holes: vec![ty_answer(Ty::Ptr)],
                ..host(&format!("pointer_compare_{right}"))
            },
            run: Some((
                vec![pointer(0), pointer(right)],
                vec![trust_ir::InterpretValue::bool(expected)],
            )),
        });
    }
    for (ty, value) in [(Ty::U64, 7), (Ty::I32, -3), (Ty::U8, 200)] {
        out.push(Instance {
            name: format!("ident_param<{ty}>"),
            template: ident_param()?,
            host: ScriptedHost {
                arguments: vec![InstArg::Type(ty.clone())],
                ..host(&format!("identity_{ty}"))
            },
            run: Some((vec![int(ty.clone(), value)?], vec![int(ty, value)?])),
        });
    }
    // Vec<u32>::len.
    {
        let mut h = host("vec_len_u32");
        h.structs = vec![
            struct_def(
                HOST_STRUCT_BASE,
                "RawVec<u32>",
                vec![(Ty::Ptr, 0), (Ty::Usize, 8)],
                16,
                8,
            ),
            struct_def(
                HOST_STRUCT_BASE + 1,
                "Vec<u32>",
                vec![
                    (Ty::Struct(StructId::new(HOST_STRUCT_BASE)), 0),
                    (Ty::Usize, 16),
                ],
                24,
                8,
            ),
        ];
        h.arguments = vec![InstArg::Type(Ty::U32)];
        h.holes = vec![
            ty_answer(Ty::Struct(StructId::new(HOST_STRUCT_BASE + 1))),
            ty_answer(Ty::Struct(StructId::new(HOST_STRUCT_BASE))),
        ];
        out.push(Instance {
            name: "struct_contract_field_read<u32>".into(),
            template: struct_contract_field_read()?,
            host: h,
            run: None,
        });
    }
    for ty in [Ty::U32, Ty::I64] {
        let mut h = host(&format!("tag_of_some_{ty}"));
        h.enums = vec![
            EnumDef::new(
                trust_ir::EnumId::new(HOST_STRUCT_BASE),
                format!("Option<{ty}>"),
                vec![
                    EnumVariant {
                        name: "None".into(),
                        fields: vec![],
                        field_names: vec![],
                    },
                    EnumVariant {
                        name: "Some".into(),
                        fields: vec![ty.clone()],
                        field_names: vec![],
                    },
                ],
            )
            .with_discriminants(vec![None, None])
            .with_repr(EnumTagRepr::U8),
        ];
        h.arguments = vec![InstArg::Type(ty.clone())];
        h.holes = vec![ty_answer(Ty::Enum(trust_ir::EnumId::new(HOST_STRUCT_BASE)))];
        out.push(Instance {
            name: format!("enum_contract_match<{ty}>"),
            template: enum_contract_match()?,
            host: h,
            run: Some((vec![int(ty, 5)?], vec![int(Ty::U8, 1)?])),
        });
    }
    {
        let mut h = host("dup_u64");
        h.arguments = vec![InstArg::Type(Ty::U64)];
        h.holes = vec![callee_answer(LinkAnswer {
            symbol: "clone_u64".into(),
            calling_conv: CallingConv::Rust,
            attrs: Default::default(),
            linkage: Linkage::External,
        })];
        out.push(Instance {
            name: "callee_hole_trait_call<u64>".into(),
            template: callee_hole_trait_call()?,
            host: h,
            run: None,
        });
    }
    for (ty, size) in [(Ty::U64, 8), (Ty::U8, 1), (Ty::Unit, 0)] {
        let mut h = host(&format!("size_of_{ty}"));
        h.arguments = vec![InstArg::Type(ty.clone())];
        h.holes = vec![const_answer(Constant::Int(size))];
        out.push(Instance {
            name: format!("const_hole_size_of<{ty}>"),
            template: const_hole_size_of()?,
            host: h,
            run: Some((vec![], vec![int(Ty::Usize, size)?])),
        });
    }
    // drop at u32 (trivially droppable), at a destructor-less struct, and at
    // a struct with glue.
    {
        let mut h = host("drop_u32");
        h.arguments = vec![InstArg::Type(Ty::U32)];
        out.push(Instance {
            name: "drop_at_param<u32>".into(),
            template: drop_at_param()?,
            host: h,
            run: Some((vec![int(Ty::U32, 9)?], vec![])),
        });
        let point = Ty::Struct(StructId::new(HOST_STRUCT_BASE));
        let mut h = host("drop_point");
        h.structs = vec![struct_def(
            HOST_STRUCT_BASE,
            "Point",
            vec![(Ty::U64, 0), (Ty::U64, 8)],
            16,
            8,
        )];
        h.arguments = vec![InstArg::Type(point.clone())];
        h.destructors = vec![(point, Destructor::NoDestructor)];
        out.push(Instance {
            name: "drop_at_param<Point>".into(),
            template: drop_at_param()?,
            host: h,
            run: None,
        });
        let resource = Ty::Struct(StructId::new(HOST_STRUCT_BASE));
        let mut h = host("drop_resource");
        h.structs = vec![struct_def(
            HOST_STRUCT_BASE,
            "Resource",
            vec![(Ty::Ptr, 0)],
            8,
            8,
        )];
        h.arguments = vec![InstArg::Type(resource.clone())];
        h.destructors = vec![(
            resource,
            Destructor::Glue(LinkAnswer {
                symbol: "drop_in_place_resource".into(),
                calling_conv: CallingConv::Rust,
                attrs: Default::default(),
                linkage: Linkage::External,
            }),
        )];
        out.push(Instance {
            name: "drop_at_param<Resource>".into(),
            template: drop_at_param()?,
            host: h,
            run: None,
        });
    }
    for (ty, value) in [(Ty::U64, 7), (Ty::I8, -2)] {
        let symbol = format!("countdown_{ty}");
        let mut h = host(&symbol);
        h.arguments = vec![InstArg::Type(ty.clone())];
        h.holes = vec![callee_answer(LinkAnswer {
            symbol,
            calling_conv: CallingConv::Rust,
            attrs: Default::default(),
            linkage: Linkage::Internal,
        })];
        out.push(Instance {
            name: format!("self_recursive_generic<{ty}>"),
            template: self_recursive_generic()?,
            host: h,
            run: Some((
                vec![int(Ty::U64, 3)?, int(ty.clone(), value)?],
                vec![int(ty, value)?],
            )),
        });
    }
    for n in [5, 0, 40] {
        let mut h = host(&format!("n_{n}"));
        h.arguments = vec![InstArg::Const(Constant::Int(n))];
        h.holes = vec![global_answer(GlobalAnswer {
            symbol: format!("n_{n}_promoted"),
            linkage: Linkage::Internal,
            visibility: Visibility::Default,
            initializer: Some(Constant::Int(n)),
            align: None,
        })];
        out.push(Instance {
            name: format!("const_param_value<{n}>"),
            template: const_param_value()?,
            host: h,
            run: Some((vec![], vec![int(Ty::Usize, 2 * n)?])),
        });
    }
    for (rust, ty) in [
        ("str", Ty::FatPtr(trust_ir::FatPtrKind::Str)),
        ("u8", Ty::Ptr),
    ] {
        let mut h = host(&format!("pass_{rust}"));
        h.arguments = vec![InstArg::Host(HostKey::new(
            "rust",
            rust.as_bytes().to_vec(),
        ))];
        h.holes = vec![ty_answer(ty)];
        out.push(Instance {
            name: format!("host_param_ref<{rust}>"),
            template: host_param_ref()?,
            host: h,
            run: None,
        });
    }
    Ok(out)
}

/// The hand-monomorphized twin of `identity::<u64>`: the byte-identical
/// output `instantiate` must produce for `ident_param` at `u64`.
pub fn ident_at_u64_twin() -> Result<trust_ir::Module, IdSpaceExhausted> {
    let mut m = trust_ir::Module::new("core");
    m.target_info = Some(target());
    let ty = m.add_func_type(FuncTy {
        abi: None,
        params: vec![Ty::U64],
        returns: vec![Ty::U64],
        is_vararg: false,
    })?;
    let mut f = trust_ir::Function::new(FuncId::new(0), "identity_u64", ty, b(0));
    let header = instance("identity_u64");
    f.linkage = header.linkage;
    f.visibility = header.visibility;
    f.calling_conv = header.calling_conv;
    f.display_path = header.display_path;
    f.body_gate = Some(header.body_gate);
    let mut entry = trust_ir::Block::new(b(0)).with_param(v(0), Ty::U64);
    entry
        .body
        .push(trust_ir::InstrNode::new(trust_ir::Inst::Return {
            values: vec![v(0)],
        }));
    f.blocks.push(entry);
    m.functions.push(f);
    Ok(m)
}

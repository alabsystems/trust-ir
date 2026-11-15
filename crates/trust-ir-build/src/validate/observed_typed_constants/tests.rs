// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Authored UNRUN; entire actual ordinary typedconstant result is the oracle.
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::super::constant_values::{ConstantSymbols, validate_constant_against_ty};
use super::*;
use std::{cell::Cell, rc::Rc};
use trust_ir::interpret::InterpretOptions;
use trust_ir::ty::{ClosureTy, EnumVariant};
use trust_ir::value::ClosureTyId;
use trust_ir::{Global, Linkage, SetRepr, StructRepr, TlsModel, Visibility};
mod custody;
mod parity;
mod pointers;
mod stops;
#[derive(Default)]
struct Observer {
    events: Vec<ExecutionProgress>,
    calls: Rc<Cell<usize>>,
    stop: Option<usize>,
    work: usize,
    bytes: usize,
    work_cap: Option<usize>,
    byte_cap: Option<usize>,
    cleanup: Option<Rc<Cell<bool>>>,
}
impl ExecutionObserver for Observer {
    type Refusal = &'static str;
    fn admit(&mut self, e: ExecutionProgress) -> Result<(), Self::Refusal> {
        self.events.push(e);
        self.calls.set(self.events.len());
        if self.stop == Some(self.events.len()) {
            return Err("original typedconstant stop");
        }
        if self.cleanup.as_ref().is_some_and(|a| a.get())
            && e.phase == ExecutionPhase::ScratchRetirement
        {
            return Err("cleanup");
        }
        self.work = self.work.checked_add(e.work).ok_or("overflow")?;
        self.bytes = self.bytes.checked_add(e.copy_bytes).ok_or("overflow")?;
        if self.work_cap.is_some_and(|n| self.work > n) {
            return Err("work");
        }
        if self.byte_cap.is_some_and(|n| self.bytes > n) {
            return Err("copy");
        }
        Ok(())
    }
}
fn site() -> ExecutionSite {
    ExecutionSite::Entry(FuncId::new(3781))
}
fn field(name: &str, ty: Ty) -> FieldDef {
    FieldDef {
        name: name.into(),
        ty,
        offset: None,
    }
}
fn structure(id: u32, name: &str, fields: Vec<FieldDef>) -> StructDef {
    StructDef {
        id: StructId::new(id),
        name: name.into(),
        fields,
        size: None,
        align: None,
        repr: StructRepr::Rust,
        origin: None,
    }
}
fn global(name: &str, ty: Ty, initializer: Option<Constant>) -> Global {
    Global {
        name: name.into(),
        ty,
        mutable: false,
        initializer,
        linkage: Linkage::Internal,
        tls: None,
        align: None,
        section: None,
        visibility: Visibility::Default,
        retained: false,
    }
}
fn fixture() -> Module {
    let mut m = Module::new("");
    m.types = vec![Ty::U8, Ty::Bool, Ty::U16, Ty::Unit];
    m.target_info = Some(trust_ir::TargetInfo {
        triple: "aarch64-unknown-linux-gnu".into(),
        pointer_size: 8,
        endianness: trust_ir::Endianness::Little,
        abi: None,
        struct_passing: trust_ir::StructPassingPolicy::NativeC,
    });
    m.structs = vec![structure(
        0,
        "S",
        vec![field("flag", Ty::Bool), field("byte", Ty::U8)],
    )];
    m.records = vec![RecordDef {
        id: RecordId::new(0),
        name: "R".into(),
        fields: vec![field("flag", Ty::Bool), field("byte", Ty::U8)],
    }];
    m.enums = vec![EnumDef::new(
        EnumId::new(0),
        "E",
        vec![
            EnumVariant {
                name: "A".into(),
                fields: vec![Ty::Bool],
                field_names: vec![],
            },
            EnumVariant {
                name: "Empty".into(),
                fields: vec![],
                field_names: vec![],
            },
            EnumVariant {
                name: "Void".into(),
                fields: vec![Ty::Never],
                field_names: vec![],
            },
        ],
    )];
    m.closure_types = vec![ClosureTy {
        func: FuncTyId::new(0),
        captures: vec![Ty::Bool, Ty::U8],
    }];
    m.func_types = vec![
        FuncTy::unrecorded(vec![], vec![], false),
        FuncTy::unrecorded(vec![Ty::Bool], vec![], false),
    ];
    m.functions = vec![
        Function::new(
            FuncId::new(9),
            "function",
            FuncTyId::new(0),
            BlockId::new(0),
        ),
        Function::new(FuncId::new(12), "weak", FuncTyId::new(0), BlockId::new(0)),
    ];
    m.functions[1].linkage = Linkage::ExternalWeak;
    m.globals = vec![
        global("G", Ty::Bool, Some(Constant::Bool(true))),
        global(
            "bytes",
            Ty::Array(TyId::new(0), 4),
            Some(Constant::Bytes {
                data: "éab".as_bytes().to_vec(),
                utf8: true,
            }),
        ),
        global(
            "u16",
            Ty::Array(TyId::new(2), 4),
            Some(Constant::Splat {
                elem: Box::new(Constant::Int(7)),
                len: 4,
            }),
        ),
        global(
            "zst",
            Ty::Array(TyId::new(3), 3),
            Some(Constant::Splat {
                elem: Box::new(Constant::Aggregate(vec![])),
                len: 3,
            }),
        ),
    ];
    m
}
fn sym(name: &str, addend: i64) -> Constant {
    Constant::SymbolAddr {
        symbol: name.into(),
        addend,
    }
}
fn fat(name: &str, addend: i64, length: Constant) -> Constant {
    Constant::Aggregate(vec![sym(name, addend), length])
}
fn original(m: &Module, c: &Constant, ty: &Ty, base: &str) -> Vec<ValidationError> {
    let functions = ModuleFunctionCatalog::new(m);
    let layouts = m.layout_table();
    let symbols = ConstantSymbols::new(&layouts);
    let mut errors = Vec::new();
    let good = validate_constant_against_ty(m, &functions, &symbols, c, ty, base, &mut errors);
    assert_eq!(good, errors.is_empty());
    errors
}
fn run_at(
    m: &Module,
    c: &Constant,
    ty: &Ty,
    base: &str,
) -> (Vec<ValidationError>, Observer, usize, usize) {
    let expected = original(m, c, ty, base);
    let layouts = m.layout_table();
    let functions = ModuleFunctionCatalog::new(m);
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let ctx = ObservedConstantSymbols::new_observed(&layouts, &functions, &mut s, site()).unwrap();
    let begin = calls.get();
    let out = validate_constant_against_ty_observed(&ctx, c, ty, base, &mut s, site()).unwrap();
    let end = calls.get();
    assert_eq!(out, expected);
    retire_validation_errors_observed(out, &mut s, site()).unwrap();
    ctx.retire_observed(&mut s, site()).unwrap();
    assert!(s.first_refusal().is_none());
    assert_eq!(s.remaining_fuel(), InterpretOptions::default().fuel);
    drop(s);
    assert!(o.events.iter().all(|e| e.site == site()));
    (expected, o, begin, end)
}
fn run(m: &Module, c: &Constant, ty: &Ty) -> (Vec<ValidationError>, Observer, usize, usize) {
    run_at(m, c, ty, "constant.root")
}
fn empty(s: &State<'_>) {
    assert!(
        s.current.is_none()
            && s.children.is_none()
            && s.uniform.is_none()
            && s.discriminants.is_none()
            && s.layout.is_none()
            && s.layout_error.is_none()
            && s.reason.is_none()
    );
    assert_eq!(
        s.pending.capacity()
            + s.path.capacity()
            + s.location.capacity()
            + s.expected.capacity()
            + s.actual.capacity()
            + s.render.capacity()
            + s.spelling.capacity()
            + s.symbol.capacity()
            + s.tytext.capacity()
            + s.enum_name.capacity()
            + s.variant_name.capacity()
            + s.errors.capacity(),
        0
    );
}
fn drain<O: ExecutionObserver>(s: &mut State<'_>, w: &mut Work<'_, '_, O>) {
    s.retire(w);
    let _ = retire_validation_errors_observed(take(&mut s.errors), w.session, w.site);
}
fn nested() -> (Constant, Ty) {
    (
        Constant::Aggregate(vec![
            Constant::Array(vec![Constant::Int(300), Constant::Bool(true)]),
            Constant::Record(vec![
                ("wrong".into(), Constant::FnDef(FuncId::new(12))),
                ("byte".into(), Constant::Int(999)),
            ]),
        ]),
        Ty::Tuple(vec![
            Ty::Array(TyId::new(0), 2),
            Ty::Record(RecordId::new(0)),
        ]),
    )
}

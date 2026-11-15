// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Authored UNRUN: original full source inventory, real child work and custody.
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use std::{cell::Cell, rc::Rc};
use trust_ir::dialect::{AttrEntry, AttrValue, DialectInst};
use trust_ir::inst::{BindingFrameDef, BindingSlot};
use trust_ir::interpret::InterpretOptions;
use trust_ir::ty::{
    ClosureTy, DialectTy, EnumDef, EnumVariant, FieldDef, RecordDef, StructDef, StructRepr,
};
use trust_ir::value::{BindingFrameId, EnumId, FuncTyId, RecordId, StructId, TyId};
use trust_ir::{Block, CastOp, DropGlueEntry, Global, InstrNode, Linkage, Visibility};
mod custody;
mod parity;
mod stops;
#[derive(Default)]
struct Observer {
    events: Vec<ExecutionProgress>,
    calls: Rc<Cell<usize>>,
    stop: Option<usize>,
    cleanup_after: Option<usize>,
    work: usize,
    bytes: usize,
    work_cap: Option<usize>,
    byte_cap: Option<usize>,
}
impl ExecutionObserver for Observer {
    type Refusal = &'static str;
    fn admit(&mut self, e: ExecutionProgress) -> Result<(), Self::Refusal> {
        self.events.push(e);
        self.calls.set(self.events.len());
        if self.stop == Some(self.events.len()) {
            return Err("original type inventory stop");
        }
        if e.phase == ExecutionPhase::ScratchRetirement
            && self.cleanup_after.is_some_and(|n| self.events.len() > n)
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
    ExecutionSite::Entry(FuncId::new(521))
}
fn registry() -> HandleRegistry {
    HandleRegistry {
        pins: TRUSTED_HANDLE_RUNTIMES.to_vec(),
    }
}
fn d() -> Ty {
    Ty::Struct(StructId::new(99))
}
fn invalid() -> Ty {
    Ty::Dialect(Box::new(DialectTy::new("bad namespace", "name", 1)))
}
fn field(name: &str, ty: Ty) -> FieldDef {
    FieldDef {
        name: name.into(),
        ty,
        offset: None,
    }
}
fn strukt(name: &str, fields: Vec<FieldDef>) -> StructDef {
    StructDef {
        id: StructId::new(0),
        name: name.into(),
        fields,
        size: None,
        align: None,
        repr: StructRepr::Rust,
        origin: None,
    }
}
fn function(name: &str, body: Vec<Inst>, params: Vec<Ty>) -> Function {
    let mut f = Function::new(FuncId::new(7), name, FuncTyId::new(0), BlockId::new(0));
    let mut b = Block::new(BlockId::new(0));
    b.params = params
        .into_iter()
        .enumerate()
        .map(|(i, ty)| (ValueId::new(u32::try_from(i).unwrap()), ty))
        .collect();
    b.body = body.into_iter().map(InstrNode::new).collect();
    f.blocks.push(b);
    f
}
fn cast() -> Inst {
    Inst::Cast {
        op: CastOp::Bitcast,
        src_ty: Ty::Tuple(vec![d(), d()]),
        dst_ty: d(),
        operand: ValueId::new(3),
    }
}
fn fixture() -> Module {
    let mut m = Module::new("");
    m.types.push(Ty::Tuple(vec![d(), invalid()]));
    m.structs
        .push(strukt("S", vec![field("a", d()), field("b", d())]));
    m.records.push(RecordDef {
        id: RecordId::new(0),
        name: "R".into(),
        fields: vec![field("r", d())],
    });
    m.enums.push(EnumDef::new(
        EnumId::new(0),
        "E",
        vec![EnumVariant {
            name: "V".into(),
            fields: vec![d(), d()],
            field_names: vec![],
        }],
    ));
    m.closure_types.push(ClosureTy {
        func: FuncTyId::new(99),
        captures: vec![d(), d()],
    });
    m.func_types
        .push(FuncTy::unrecorded(vec![d(), d()], vec![d()], false));
    m.globals.push(Global {
        name: "G".into(),
        ty: d(),
        mutable: false,
        initializer: None,
        linkage: Linkage::External,
        tls: None,
        align: None,
        section: None,
        visibility: Visibility::Default,
        retained: false,
    });
    m.drop_glue.push(DropGlueEntry {
        ty: d(),
        glue: FuncId::new(7),
    });
    let frame = Inst::OpenFrame {
        def: BindingFrameDef::new(
            BindingFrameId::new(0),
            "unused",
            vec![BindingSlot::new("unused", d())],
        ),
    };
    let mut op = DialectInst::new("unread", "unread");
    op.result_tys.push(d());
    op.attrs = vec![
        AttrEntry {
            name: "not-type".into(),
            value: AttrValue::Str("ignored".into()),
        },
        AttrEntry {
            name: "type".into(),
            value: AttrValue::Ty(Ty::handle("NotPinned", "untrusted::NotPinned")),
        },
    ];
    m.functions.push(function(
        "f",
        vec![cast(), frame, Inst::DialectOp(Box::new(op))],
        vec![d()],
    ));
    m
}
fn run(m: &Module) -> ((Vec<ValidationError>, NominalCensus), Observer, usize) {
    let r = registry();
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let out = validate_type_table_references_observed(m, &r, &mut s, site()).unwrap();
    assert_eq!(out, super::super::validate_type_table_references(m, &r));
    let saved = out.clone();
    let bound = calls.get();
    retire_validation_errors_observed(out.0, &mut s, site()).unwrap();
    assert!(s.first_refusal().is_none());
    assert_eq!(s.remaining_fuel(), InterpretOptions::default().fuel);
    drop(s);
    assert!(o.events.iter().all(|e| e.site == site()));
    assert_eq!(o.events[bound - 1].phase, ExecutionPhase::Publication);
    (saved, o, bound)
}
fn prior() -> ValidationError {
    ValidationError::InvalidDialectType {
        location: "prior λ\0FULL".into(),
        detail: "prior 尾\0FULL".into(),
    }
}
fn drain<O: ExecutionObserver>(s: &mut State<'_>, w: &mut Work<'_, '_, O>) {
    s.retire_scratch(w);
    let _ = retire_validation_errors_observed(take(&mut s.errors), w.session, w.site);
}
fn empty(s: &State<'_>) -> bool {
    s.location.capacity() == 0
        && s.frames.capacity() == 0
        && s.roots.capacity() == 0
        && s.errors.capacity() == 0
        && s.batch.capacity() == 0
        && s.row.is_none()
}
fn error_location(error: &ValidationError) -> &str {
    match error {
        ValidationError::DanglingTypeReference { location, .. }
        | ValidationError::InvalidDialectType { location, .. }
        | ValidationError::InvalidHandleType { location, .. }
        | ValidationError::UntrustedHandleRuntime { location, .. } => location,
        _ => panic!("wrong diagnostic"),
    }
}

// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Authored UNRUN original parity/interior stop/custody controls.
use super::*;
use std::{cell::Cell, rc::Rc};
use trust_ir::interpret::InterpretOptions;
use trust_ir::value::{EnumId, StructId};
mod parity;
mod stops;
#[derive(Default)]
struct Observer {
    events: Vec<ExecutionProgress>,
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
        if self.stop == Some(self.events.len()) {
            return Err("original origin stop");
        }
        if self.cleanup.as_ref().is_some_and(|arm| arm.get())
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
            return Err("bytes");
        }
        Ok(())
    }
}
fn site() -> ExecutionSite {
    ExecutionSite::Entry(FuncId::new(129))
}
fn digest(algorithm: ProofDigestAlgorithm, tail: u8) -> ProofDigest {
    let mut bytes = [0; 32];
    bytes[31] = tail;
    ProofDigest { algorithm, bytes }
}
fn rust() -> TypeOrigin {
    TypeOrigin::Rust {
        stable_crate_id: 0x9a,
        def_path_hash: [0xcd; 16],
        args_digest: digest(ProofDigestAlgorithm::Sha256, 7),
    }
}
fn clean() -> TypeOrigin {
    TypeOrigin::Clean {
        decl: "Name'\"λ\n".into(),
        env_digest: digest(ProofDigestAlgorithm::TrustIrStableV1, 9),
    }
}
fn strukt(id: u32, name: &str, origin: Option<TypeOrigin>) -> trust_ir::ty::StructDef {
    trust_ir::ty::StructDef {
        id: StructId::new(id),
        name: name.into(),
        fields: vec![],
        size: None,
        align: None,
        repr: trust_ir::StructRepr::Rust,
        origin,
    }
}
fn enm(id: u32, name: &str, origin: Option<TypeOrigin>) -> trust_ir::ty::EnumDef {
    let mut e = trust_ir::ty::EnumDef::new(EnumId::new(id), name, vec![]);
    e.origin = origin;
    e
}
fn fixture() -> Module {
    let mut m = Module::new("nominal");
    m.structs = vec![
        strukt(9, "first", Some(rust())),
        strukt(9, "later", Some(rust())),
        strukt(4, "clean-first", Some(clean())),
        strukt(5, "unkeyed", None),
    ];
    m.enums = vec![
        enm(3, "cross-table", Some(rust())),
        enm(4, "clean-later", Some(clean())),
    ];
    m
}
fn run(m: &Module) -> (Vec<ValidationError>, Observer) {
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let out = validate_module_type_origins_observed(m, &mut s, site()).unwrap();
    assert_eq!(out, validate_type_origins_unique(m));
    assert!(s.first_refusal().is_none());
    assert_eq!(
        s.remaining_fuel(),
        trust_ir::interpret::InterpretOptions::default().fuel
    );
    assert!(o.events.iter().all(|e| e.site == site()));
    (out, o)
}
fn spelling(origin: &TypeOrigin) -> (String, Observer) {
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut work = Work {
        session: &mut s,
        site: site(),
    };
    let mut out = String::new();
    origin::write(origin, &mut work, &mut out).unwrap();
    assert_eq!(out, origin.to_string());
    (out, o)
}
fn equality(a: &TypeOrigin, b: &TypeOrigin) -> (bool, Observer) {
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut work = Work {
        session: &mut s,
        site: site(),
    };
    let out = origin::equal(a, b, &mut work).unwrap();
    assert_eq!(out, a == b);
    (out, o)
}
fn drain(state: &mut State<'_>, work: &mut Work<'_, '_, impl ExecutionObserver>) {
    state.retire_scratch(work);
    let _ = retire_validation_errors_observed(take(&mut state.errors), work.session, work.site);
}
fn empty(state: &State<'_>) -> bool {
    state.keys.capacity() == 0
        && state.seen.capacity() == 0
        && state.origin.capacity() == 0
        && state.first.capacity() == 0
        && state.second.capacity() == 0
        && state.errors.capacity() == 0
}

// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! WS1.14 (F-013): a DEFINED function's `FunctionSummary.effects` against its
//! body.
//!
//! The summary is an upper bound a separately compiled caller relies on to keep
//! facts about memory across a call (the frame). So the check is a
//! conservative, SOUND over-approximation of what the body can do, kept
//! syntactic because it is trusted code: every refusal names the instruction
//! and the effect it needs. A tighter analysis may admit more; this one never
//! admits a body that can touch caller-visible memory its summary does not
//! list.
//!
//! # The address trace
//!
//! A memory access is attributed by tracing its address back through the
//! ADDRESS-PRESERVING definitions only — `GEP` (its base), `PtrData`, `Copy`,
//! `Select` (BOTH arms: every root must be covered), a `PtrToPtr` cast, and a
//! `Borrow` / `BorrowMut` (address identities; the interpreter passes the
//! address through). The trace ends at a ROOT:
//!
//! * an `Alloca` of this function — local, invisible to the caller, needs no
//!   coverage;
//! * a parameter of the ENTRY block, when no edge enters the entry block —
//!   formal parameter `i`, so [`EffectPlace::ParamPointee`]` { index: i }`;
//! * a `GlobalAddr` — [`EffectPlace::Global`];
//! * anything else — a `Load` result, an `IntToPtr` / `PtrFromParts` / other
//!   cast, a call result, a heap allocation, a constant, the parameter of any
//!   other block (or of an entry block some edge re-enters), a value with no
//!   definition, a cycle — is UNTRACEABLE, and forces `Everything` on the side
//!   it reaches.
//!
//! # Per instruction (the match is exhaustive: a new instruction must be
//! classified here, never slip through a wildcard as effect-free)
//!
//! * reads: `Load`, `AtomicLoad`, the read half of `AtomicRMW` / `CmpXchg`, a
//!   `MemCopy` source, `Retain` / `Release` / `IsUnique` (the object header);
//! * writes: `Store`, `AtomicStore`, `AtomicRMW`, `CmpXchg`, `CoroSuspend`
//!   (defined as a store into the frame), a `MemCopy` / `MemSet` destination,
//!   `Retain` / `Release`;
//! * `HeapAlloc` ⇒ `allocates`; `Dealloc` and `Release` ⇒ `frees`; `Invoke`,
//!   `AssertInvoke` and `Resume` ⇒ `may_unwind`;
//! * a `Call` / `CallCannotUnwind` / `Invoke` (and `SeqMap`'s element
//!   function) contributes the callee's ADMISSIBLE summary mapped through the
//!   call: callee `ParamPointee { i }` becomes the trace of argument `i` (so it
//!   may itself force `Everything`); a callee `Global` stays that global. A
//!   callee with no admissible summary contributes the TOP summary —
//!   `Everything` on both sides and every flag, `io` included (it may reach a
//!   body-less declaration). `SeqMap` hands its element function an internal
//!   element slot, which this trace does not model, so that argument is
//!   untraceable. `CallCannotUnwind`'s boundary keeps an unwind from
//!   crossing the call, but the callee's `may_unwind` is still propagated:
//!   an over-approximation, never a claim the boundary is enforced;
//! * a SITED check (`Assert` with a panic site, every `AssertInvoke`;
//!   amendment P) calls its site's entry when it fails, with the kind's
//!   operands then the location (`entry(kind operands.., location)`), so it
//!   contributes that entry's admissible summary mapped through those
//!   arguments — a `Global` location is that global's place. An unsited
//!   `Assert` traps and touches nothing;
//! * `CallIndirect` / `CallIndirectCannotUnwind` / `InvokeIndirect`, an opaque
//!   `DialectOp`, and `Drop` / `DropInvoke` (a destructor runs arbitrary code)
//!   contribute the top summary;
//! * `Fence` touches no memory location (it orders, it does not write).
//!
//! # Which summaries are admissible at a call
//!
//! A DEFINITION's summary: its own body is checked by this same pass in the
//! same run, so a call may rely on it (for a recursive call this is the usual
//! inductive argument over call depth) — unless its linkage is interposable
//! (`Weak` / `LinkOnce` / `ExternalWeak`), when the linker may bind another
//! body and the call is havoc. A body-less DECLARATION's summary is a
//! claim with no body to check: it is admissible only when the module is
//! validated under `validate_linked_module` and the declaration's `backed_by`
//! citation AUTHENTICATED — whose restatement rule then requires the far
//! effects restated exactly and naming no global. Otherwise the caller treats
//! it as `None`: havoc, the same "`None` is never a wildcard" rule `proved`
//! follows.

use super::ImportPolicy;
use super::ValidationError;
use super::claims::{Def, DefTable};
use std::collections::{BTreeMap, BTreeSet};
use trust_ir::inst::{AssertKind, CastOp, Inst, PanicLocation, PanicSite};
use trust_ir::value::{FuncId, ValueId};
use trust_ir::{EffectPlace, EffectSet, EffectSummary, Function, Linkage, Module};

mod observed_analysis;
mod observed_context;
mod observed_need;
mod observed_roots;
pub(crate) use observed_analysis::validate_effect_summary_observed;

/// One argument of a call edge, as the trace sees it.
#[derive(Clone, Copy, Debug)]
enum Arg {
    /// An SSA operand: its address roots are traced.
    Value(ValueId),
    /// A module global passed by address (a sited check's `Global`
    /// location): exactly that global's place.
    Global(trust_ir::value::GlobalId),
    /// A slot this trace does not model: untraceable.
    Untraceable,
}

/// One root of an address trace.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Root {
    /// An `Alloca` of this function: invisible to the caller.
    Local,
    /// A caller-visible place.
    Place(EffectPlace),
    /// Anything else: forces `Everything` on the side it reaches.
    Untraceable,
}

/// The accumulated need of one side (`reads` or `writes`): the first reason
/// it must be `Everything`, and the first reason for each named place.
#[derive(Default)]
struct Side {
    everything: Option<(u32, String)>,
    places: BTreeMap<EffectPlace, (u32, String)>,
}

impl Side {
    fn force_everything(&mut self, block: u32, why: impl FnOnce() -> String) {
        if self.everything.is_none() {
            self.everything = Some((block, why()));
        }
    }

    fn need(&mut self, place: EffectPlace, block: u32, why: impl FnOnce() -> String) {
        self.places.entry(place).or_insert_with(|| (block, why()));
    }
}

/// What the body needs its summary to admit.
#[derive(Default)]
struct Need {
    reads: Side,
    writes: Side,
    allocates: Option<(u32, String)>,
    frees: Option<(u32, String)>,
    may_unwind: Option<(u32, String)>,
    io: Option<(u32, String)>,
}

fn flag(slot: &mut Option<(u32, String)>, block: u32, why: impl FnOnce() -> String) {
    if slot.is_none() {
        *slot = Some((block, why()));
    }
}

/// The body analysis for one function.
struct Body<'f> {
    defs: DefTable<'f>,
    /// Whether an entry-block parameter IS formal parameter `index`: true only
    /// when exactly one block carries the entry id and no edge enters it.
    entry_params_are_formals: bool,
    entry: u32,
}

impl<'f> Body<'f> {
    fn new(func: &'f Function) -> Self {
        let entry = func.entry.index();
        let entry_blocks = func
            .blocks
            .iter()
            .filter(|block| block.id.index() == entry)
            .count();
        let entry_reentered = func.blocks.iter().any(|block| {
            block
                .body
                .iter()
                .any(|node| branch_targets(&node.inst).contains(&entry))
        });
        Self {
            defs: DefTable::new(func),
            entry_params_are_formals: entry_blocks == 1 && !entry_reentered,
            entry,
        }
    }

    /// Every root `address` may have. Depth-first with an on-path set, so a
    /// shared operand (`select %c, %a, %a`) is visited once and a genuine
    /// cycle through address-preserving definitions reads as UNTRACEABLE.
    fn roots(&self, address: ValueId) -> BTreeSet<Root> {
        #[derive(Clone, Copy, PartialEq, Eq)]
        enum Mark {
            OnPath,
            Done,
        }
        enum Step {
            Enter(ValueId),
            Exit(ValueId),
        }
        let mut roots = BTreeSet::new();
        let mut marks: BTreeMap<ValueId, Mark> = BTreeMap::new();
        let mut stack = vec![Step::Enter(address)];
        while let Some(step) = stack.pop() {
            let current = match step {
                Step::Exit(value) => {
                    marks.insert(value, Mark::Done);
                    continue;
                }
                Step::Enter(value) => value,
            };
            match marks.get(&current) {
                Some(Mark::OnPath) => {
                    roots.insert(Root::Untraceable);
                    continue;
                }
                Some(Mark::Done) => continue,
                None => {}
            }
            marks.insert(current, Mark::OnPath);
            stack.push(Step::Exit(current));
            let defs = self.defs.defs(current);
            if defs.is_empty() {
                roots.insert(Root::Untraceable);
            }
            for def in defs {
                match def {
                    Def::Node(Inst::GEP { base, .. }) => stack.push(Step::Enter(*base)),
                    Def::Node(Inst::PtrData { ptr, .. })
                    | Def::Node(Inst::Borrow { ptr })
                    | Def::Node(Inst::BorrowMut { ptr }) => stack.push(Step::Enter(*ptr)),
                    Def::Node(Inst::Copy { operand, .. })
                    | Def::Node(Inst::Cast {
                        op: CastOp::PtrToPtr,
                        operand,
                        ..
                    }) => stack.push(Step::Enter(*operand)),
                    Def::Node(Inst::Select {
                        then_val, else_val, ..
                    }) => {
                        stack.push(Step::Enter(*then_val));
                        stack.push(Step::Enter(*else_val));
                    }
                    Def::Node(Inst::Alloca { .. }) => {
                        roots.insert(Root::Local);
                    }
                    Def::Node(Inst::GlobalAddr { global }) => {
                        roots.insert(Root::Place(EffectPlace::Global(*global)));
                    }
                    Def::Param { block, index }
                        if *block == self.entry && self.entry_params_are_formals =>
                    {
                        match u32::try_from(*index) {
                            Ok(index) => {
                                roots.insert(Root::Place(EffectPlace::ParamPointee { index }));
                            }
                            Err(_) => {
                                roots.insert(Root::Untraceable);
                            }
                        }
                    }
                    Def::Param { .. } | Def::Node(_) => {
                        roots.insert(Root::Untraceable);
                    }
                }
            }
        }
        roots
    }
}

/// Every block a (terminator) instruction can transfer control to, normal
/// and unwind edges alike.
///
/// The entry block's parameters are read as the formal parameters only when
/// NO edge re-enters it, so this reads `trust_ir`'s own exhaustive successor
/// table ([`Inst::successor_edges`]) rather than a second list here: a new
/// branching instruction (the invoke family of amendments P and D included)
/// is classified there once, and can never slip through as branch-free.
fn branch_targets(inst: &Inst) -> Vec<u32> {
    inst.successor_edges()
        .iter()
        .map(|edge| edge.target.index())
        .collect()
}

fn root_label(place: &EffectPlace, module: &Module) -> String {
    match place {
        EffectPlace::ParamPointee { index } => format!("*param{index}"),
        EffectPlace::Global(global) => match module.globals.get(global.as_usize()) {
            Some(g) => format!("@{}", g.name),
            None => format!("global #{}", global.index()),
        },
    }
}

/// The summary a call to `callee` may rely on, or `None` (havoc). See the
/// module docs: a definition's own summary, or an authenticated declaration's.
fn admissible_effects<'m>(
    module: &'m Module,
    callee: FuncId,
    import_policy: ImportPolicy<'_>,
) -> Option<&'m EffectSummary> {
    let target = module.function_by_id(callee)?;
    let effects = target.summary.as_ref()?.effects.as_ref()?;
    // The linker may bind a DIFFERENT body for an interposable symbol, so its
    // summary describes a body the call may never reach.
    if interposable(target.linkage) {
        return None;
    }
    if !target.is_declaration() {
        return Some(effects);
    }
    match import_policy {
        ImportPolicy::Authenticated(authenticated) => matches!(
            authenticated.backed_by_outcome(callee),
            Some(crate::linked::SiteOutcome::Authenticated)
        )
        .then_some(effects),
        ImportPolicy::Structural | ImportPolicy::Refuse => None,
    }
}

/// Whether the linker may bind a different definition than this module's,
/// or none: `Weak`, `LinkOnce` and `ExternalWeak` — the rule
/// `trust_ir::imports` applies to a far site, spelled exhaustively here so a
/// later linkage must be classified. `WeakOdr` / `LinkOnceOdr` /
/// `AvailableExternally` are admitted under the disclosed one-definition-rule
/// premise, as there.
fn interposable(linkage: Linkage) -> bool {
    match linkage {
        Linkage::Weak | Linkage::LinkOnce | Linkage::ExternalWeak => true,
        Linkage::External
        | Linkage::Internal
        | Linkage::Private
        | Linkage::AvailableExternally
        | Linkage::WeakOdr
        | Linkage::LinkOnceOdr => false,
    }
}

struct Analysis<'a, 'f> {
    module: &'a Module,
    body: Body<'f>,
    import_policy: ImportPolicy<'a>,
    need: Need,
}

impl Analysis<'_, '_> {
    /// Attribute an access through `address` to `side`.
    fn access(&mut self, write: bool, address: ValueId, block: u32, what: &str) {
        let roots = self.body.roots(address);
        let side = if write {
            &mut self.need.writes
        } else {
            &mut self.need.reads
        };
        for root in roots {
            match root {
                Root::Local => {}
                Root::Place(place) => {
                    let label = root_label(&place, self.module);
                    side.need(place, block, || format!("{what} through {label}"));
                }
                Root::Untraceable => side.force_everything(block, || {
                    format!(
                        "{what} through an address that does not trace to a parameter, a global \
                         or a local alloca"
                    )
                }),
            }
        }
    }

    /// The top summary: every side `Everything`, every flag.
    fn top(&mut self, block: u32, why: &str) {
        self.need.reads.force_everything(block, || why.to_string());
        self.need.writes.force_everything(block, || why.to_string());
        flag(&mut self.need.allocates, block, || why.to_string());
        flag(&mut self.need.frees, block, || why.to_string());
        flag(&mut self.need.may_unwind, block, || why.to_string());
        flag(&mut self.need.io, block, || why.to_string());
    }

    /// A direct call edge to `callee` with `args` (an argument slot past the
    /// end, like [`Arg::Untraceable`], is untraceable).
    fn call(&mut self, callee: FuncId, args: &[Arg], block: u32, what: &str) {
        let Some(effects) = admissible_effects(self.module, callee, self.import_policy) else {
            let name = self.module.function_by_id(callee).map_or_else(
                || format!("#{}", callee.index()),
                |f| format!("@{}", f.name),
            );
            self.top(
                block,
                &format!("{what} to {name}, which has no admissible effect summary (havoc)"),
            );
            return;
        };
        let callee_is_declaration = self
            .module
            .function_by_id(callee)
            .is_some_and(Function::is_declaration);
        for write in [false, true] {
            let set = if write {
                &effects.writes
            } else {
                &effects.reads
            };
            let side_name = if write { "writes" } else { "reads" };
            match set {
                EffectSet::Nothing => {}
                EffectSet::Everything => {
                    let side = if write {
                        &mut self.need.writes
                    } else {
                        &mut self.need.reads
                    };
                    side.force_everything(block, || {
                        format!("{what}, whose callee {side_name} Everything")
                    });
                }
                EffectSet::Places(places) => {
                    for place in places {
                        match place {
                            EffectPlace::ParamPointee { index } => {
                                match args.get(*index as usize).copied() {
                                    Some(Arg::Value(arg)) => self.access(
                                        write,
                                        arg,
                                        block,
                                        &format!("{what} (callee {side_name} *param{index})"),
                                    ),
                                    Some(Arg::Global(global)) => {
                                        let place = EffectPlace::Global(global);
                                        let label = root_label(&place, self.module);
                                        let side = if write {
                                            &mut self.need.writes
                                        } else {
                                            &mut self.need.reads
                                        };
                                        side.need(place, block, || {
                                            format!(
                                                "{what} (callee {side_name} *param{index}, \
                                                 which is {label})"
                                            )
                                        });
                                    }
                                    Some(Arg::Untraceable) | None => {
                                        let side = if write {
                                            &mut self.need.writes
                                        } else {
                                            &mut self.need.reads
                                        };
                                        side.force_everything(block, || {
                                            format!(
                                                "{what} (callee {side_name} *param{index}, an \
                                                 argument this trace cannot follow)"
                                            )
                                        });
                                    }
                                }
                            }
                            // A declaration's global is a FAR module's id; it
                            // names nothing here (the restatement rule refuses
                            // one, so this is defence in depth).
                            EffectPlace::Global(_) if callee_is_declaration => {
                                let side = if write {
                                    &mut self.need.writes
                                } else {
                                    &mut self.need.reads
                                };
                                side.force_everything(block, || {
                                    format!(
                                        "{what}, whose declaration's summary names a global of \
                                         another module"
                                    )
                                });
                            }
                            EffectPlace::Global(global) => {
                                let place = EffectPlace::Global(*global);
                                let label = root_label(&place, self.module);
                                let side = if write {
                                    &mut self.need.writes
                                } else {
                                    &mut self.need.reads
                                };
                                side.need(place, block, || {
                                    format!("{what} (callee {side_name} {label})")
                                });
                            }
                        }
                    }
                }
            }
        }
        let callee_flags = [
            (&mut self.need.allocates, effects.allocates, "allocates"),
            (&mut self.need.frees, effects.frees, "frees"),
            (&mut self.need.may_unwind, effects.may_unwind, "may unwind"),
            (&mut self.need.io, effects.io, "performs I/O"),
        ];
        for (slot, set, word) in callee_flags {
            if set {
                flag(slot, block, || format!("{what}, whose callee {word}"));
            }
        }
    }

    /// A failed sited check's call: `site.entry(kind operands.., location)`.
    fn panic_call(&mut self, kind: &AssertKind, site: &PanicSite, block: u32, what: &str) {
        let mut args: Vec<Arg> = kind
            .operands()
            .map_or_else(Vec::new, |operands| operands.map(Arg::Value).to_vec());
        args.push(match site.location {
            PanicLocation::Global(global) => Arg::Global(global),
            PanicLocation::Value(value) => Arg::Value(value),
        });
        self.call(
            site.entry,
            &args,
            block,
            &format!("{what} (its failure's panic call)"),
        );
    }

    fn instruction(&mut self, inst: &Inst, block: u32) {
        let mnemonic = super::instruction_kind(inst);
        match inst {
            Inst::BinOp { .. }
            | Inst::UnOp { .. }
            | Inst::Overflow { .. }
            | Inst::ICmp { .. }
            | Inst::FCmp { .. }
            | Inst::Cast { .. }
            | Inst::Alloca { .. }
            | Inst::GEP { .. }
            | Inst::PtrData { .. }
            | Inst::PtrMetadata { .. }
            | Inst::PtrFromParts { .. }
            | Inst::Br { .. }
            | Inst::CondBr { .. }
            | Inst::Switch { .. }
            | Inst::Return { .. }
            | Inst::ExtractField { .. }
            | Inst::InsertField { .. }
            | Inst::MakeAggregate { .. }
            | Inst::MakeClosure { .. }
            // v50: a constant-size uniform array VALUE; no memory.
            | Inst::ArraySplat { .. }
            // The tensor region: a fresh tensor VALUE; no memory, no call.
            | Inst::TensorContract { .. }
            | Inst::TensorMap { .. }
            | Inst::TensorReduce { .. }
            | Inst::TensorView { .. }
            | Inst::TensorGather { .. }
            | Inst::TensorScatter { .. }
            | Inst::ExtractElement { .. }
            | Inst::InsertElement { .. }
            | Inst::Const { .. }
            | Inst::NullPtr
            | Inst::GlobalAddr { .. }
            | Inst::Undef { .. }
            | Inst::Assume { .. }
            // An unsited check traps on failure: it calls nothing.
            | Inst::Assert { site: None, .. }
            | Inst::Unreachable
            | Inst::Copy { .. }
            | Inst::Select { .. }
            | Inst::SeqMapAddK { .. }
            | Inst::SeqMapNot { .. }
            | Inst::Borrow { .. }
            | Inst::BorrowMut { .. }
            | Inst::EndBorrow { .. }
            // Binding frames are typed slots of the executing frame; a landing
            // pad reads the unwinder's registers.
            | Inst::OpenFrame { .. }
            | Inst::BindSlot { .. }
            | Inst::LoadSlot { .. }
            | Inst::CloseFrame { .. }
            | Inst::LandingPad { .. }
            // A fence orders memory; it reads and writes no location.
            | Inst::Fence { .. } => {}
            // Dereferenceable is a memory-dependent statement at this exact
            // program point. Record a read so a pure/no-read summary cannot
            // authorize movement across deallocation.
            Inst::BoxDeref { operand, .. } => self.access(false, *operand, block, mnemonic),
            Inst::Load { ptr, .. } | Inst::AtomicLoad { ptr, .. } => {
                self.access(false, *ptr, block, mnemonic);
            }
            Inst::Store { ptr, .. } | Inst::AtomicStore { ptr, .. } => {
                self.access(true, *ptr, block, mnemonic);
            }
            Inst::AtomicRMW { ptr, .. } | Inst::CmpXchg { ptr, .. } => {
                self.access(false, *ptr, block, mnemonic);
                self.access(true, *ptr, block, mnemonic);
            }
            // DEFINED as GEP + Store + Return into the frame.
            Inst::CoroSuspend { frame, .. } => self.access(true, *frame, block, mnemonic),
            Inst::MemCopy { dst, src, .. } => {
                self.access(false, *src, block, mnemonic);
                self.access(true, *dst, block, mnemonic);
            }
            Inst::MemSet { dst, .. } => self.access(true, *dst, block, mnemonic),
            Inst::HeapAlloc { .. } => flag(&mut self.need.allocates, block, || {
                "heapalloc".to_string()
            }),
            Inst::Dealloc { .. } => flag(&mut self.need.frees, block, || "dealloc".to_string()),
            // Reference counting reads and writes the object header; a
            // release may free the object.
            Inst::Retain { ptr } => {
                self.access(false, *ptr, block, mnemonic);
                self.access(true, *ptr, block, mnemonic);
            }
            Inst::Release { ptr } => {
                self.access(false, *ptr, block, mnemonic);
                self.access(true, *ptr, block, mnemonic);
                flag(&mut self.need.frees, block, || "release".to_string());
            }
            Inst::IsUnique { ptr } => self.access(false, *ptr, block, mnemonic),
            Inst::Drop { .. } => self.top(
                block,
                "drop (a destructor frees and can run arbitrary user code)",
            ),
            Inst::DropInvoke { .. } => self.top(
                block,
                "drop_invoke (a destructor frees and can run arbitrary user code)",
            ),
            Inst::CallIndirect { .. }
            | Inst::CallIndirectCannotUnwind { .. }
            | Inst::InvokeIndirect { .. } => self.top(
                block,
                &format!("{mnemonic} (an indirect callee's effects are unknowable)"),
            ),
            Inst::DialectOp(_) => self.top(
                block,
                "an opaque dialect op (its memory effects are unknown)",
            ),
            Inst::Resume { .. } => flag(&mut self.need.may_unwind, block, || {
                "resume".to_string()
            }),
            // The boundary keeps an unwind from crossing; the callee's
            // `may_unwind` is still propagated (an over-approximation).
            Inst::Call { callee, args } | Inst::CallCannotUnwind { callee, args } => {
                let args: Vec<Arg> = args.iter().copied().map(Arg::Value).collect();
                self.call(*callee, &args, block, mnemonic);
            }
            Inst::Invoke { callee, args, .. } => {
                flag(&mut self.need.may_unwind, block, || "invoke".to_string());
                let args: Vec<Arg> = args.iter().copied().map(Arg::Value).collect();
                self.call(*callee, &args, block, mnemonic);
            }
            // A sited check: on failure it calls `entry(kind operands..,
            // location)` (amendment P), so the entry's effects are the
            // check's. `AssertInvoke`'s failure may also enter its pad.
            Inst::Assert {
                kind,
                site: Some(site),
                ..
            } => self.panic_call(kind, site, block, mnemonic),
            Inst::AssertInvoke { kind, site, .. } => {
                flag(&mut self.need.may_unwind, block, || {
                    "assert_invoke".to_string()
                });
                self.panic_call(kind, site, block, mnemonic);
            }
            // The element function is handed an internal element slot this
            // trace does not model: its parameter 0 is untraceable.
            Inst::SeqMap { fwd, .. } => self.call(*fwd, &[Arg::Untraceable], block, mnemonic),
        }
    }
}

/// Check `func`'s declared `effects` against its body. A declaration, or a
/// function with no recorded effects, is not checked here (its shape is
/// checked with the rest of the summary).
pub(super) fn validate_effect_summary(
    module: &Module,
    func: &Function,
    import_policy: ImportPolicy<'_>,
) -> Vec<ValidationError> {
    let Some(declared) = func.summary.as_ref().and_then(|s| s.effects.as_ref()) else {
        return Vec::new();
    };
    if func.is_declaration() {
        return Vec::new();
    }
    let mut analysis = Analysis {
        module,
        body: Body::new(func),
        import_policy,
        need: Need::default(),
    };
    for block in &func.blocks {
        for node in &block.body {
            analysis.instruction(&node.inst, block.id.index());
        }
    }
    let need = analysis.need;
    let mut errors = Vec::new();
    let mut violated = |effect: &'static str, (block, inst): (u32, String)| {
        errors.push(ValidationError::EffectSummaryViolated {
            function: func.name.clone(),
            effect,
            block,
            inst,
        });
    };
    for (effect, side, declared_set) in [
        ("reads", need.reads, &declared.reads),
        ("writes", need.writes, &declared.writes),
    ] {
        if let Some((block, why)) = side.everything {
            if *declared_set != EffectSet::Everything {
                violated(
                    effect,
                    (block, format!("{why}, which needs {effect}: Everything")),
                );
            }
            continue;
        }
        for (place, (block, why)) in side.places {
            if !declared_set.covers(&EffectSet::Places(vec![place])) {
                violated(effect, (block, why));
            }
        }
    }
    for (effect, needed, allowed) in [
        ("allocates", need.allocates, declared.allocates),
        ("frees", need.frees, declared.frees),
        ("may_unwind", need.may_unwind, declared.may_unwind),
        ("io", need.io, declared.io),
    ] {
        if let Some(reason) = needed
            && !allowed
        {
            violated(effect, reason);
        }
    }
    errors
}

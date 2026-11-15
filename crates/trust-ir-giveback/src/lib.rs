// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
#![forbid(unsafe_code)]

//! # trust-ir-giveback — the give-back elaborator (M1)
//!
//! An **untrusted oracle** that recovers an Aeneas-style "give-back" view of a
//! `&mut`-using [`Function`]: a forward function `f_fwd` and one backward
//! ("give-back") function `f_back_'a` per `&mut` region. See
//! `designs/2026-06-28-trust-ir-giveback.md`.
//!
//! ## Soundness posture (read this first — and note the OPEN GAP)
//!
//! This crate emits only `Pending` obligations; it never stamps `Certified`. The
//! intended future invariant is that it is *outside the trusted computing base*:
//! a buggy elaborator can only **fail to produce** a checkable obligation, never
//! make a false one pass. The current downstream validator goes further and
//! refuses every give-back `Certified` claim because no obligation-bound ground
//! refinement certificate exists yet.
//!
//! **HONEST STATUS.** The downstream re-checker (`trust_ir_build::validate`)
//! confirms cited library theorems with Clean's rooted kernel audit and requires
//! an owning [`FuncId`]. It also reruns this elaborator and compares the exact
//! `(anchor, theorem-set)`, which prevents producer-side mis-citation. That
//! recomputation does not magically make this crate untrusted, however: when
//! used as the validator's relevance checker, its synthesis and shape→theorem
//! map are part of the TCB. The long-term authority path must instead construct
//! a ground proposition from an independently re-derived, typed denotation and
//! have the kernel check the exact instantiated proof.
//!
//! **The precise REMAINING gap (do not overstate past this):** the obligation
//! still carries no separately kernel-expressible goal `formula`; the
//! function↔theorem link is established by recomputation+match, not by a
//! definitional compare of a stored goal. In particular, the existing scalar
//! arithmetic laws are over unbounded `Nat`, while TrustIR's I*/U* `BinOp::Add`
//! semantics wrap at the machine width. Rechecking a true Nat law therefore
//! cannot certify a fixed-width program. Every synthesized shape containing
//! machine arithmetic (including aggregate/nested/conditional/SeqMap forms) is
//! now authority-blocked by [`give_back_recheck_directive_in`] until an exact
//! width-aware ground statement is wired. Law-library rechecks remain useful as
//! theorem assurance but do not mint `Certified`. The explicitly enabled
//! experimental lane exercises those library rechecks and structural candidate
//! reports only; it carries no certification authority for arithmetic or
//! non-arithmetic give-backs.
//!
//! ## M1 scope: the decidable subset
//!
//! M1 handles the **non-nested, single-region `&mut`** fragment only. The
//! [`elaborate_give_back`] gate is a *whitelist* (not a blacklist) and **fails
//! closed**: it [`Declined`](GiveBackOutcome::Declined)s
//!
//! * any reference-typed parameter that is a raw pointer (`PtrConst`/`PtrMut`),
//!   `Rc`, or a bare opaque `Ptr`;
//! * more than one `&mut` ([`BorrowMut`](trust_ir::Inst::BorrowMut)) region;
//! * any nested mutable borrow (a `BorrowMut` of a value that is itself a borrow
//!   handle, or a `&mut`-of-a-reference parameter type);
//! * any back-edge / loop in the control-flow graph;
//! * any instruction the analysis does not explicitly understand.
//!
//! Declining is always safe — the caller routes declined functions to the
//! existing permission/heap verdict path.
//!
//! ## What ACCEPT does (and does not) produce
//!
//! On accept we identify the single `&mut` region and its borrowed value and
//! build a [`GiveBackView`] recording the region, the borrowed place, and the
//! **synthesized** forward-result and backward (give-back) bodies. The bodies are
//! real first-order [`GiveBackExpr`]s over the borrowed input `x_in`, produced by
//! symbolic execution of the borrow region ([`synthesize_give_back`]): e.g. for
//! `*x += 1` the backward body synthesizes to `BinOp(Add, BorrowedInput, Const(1))`.
//! Where synthesis meets an input it does not model, it records
//! [`GiveBackExpr::Opaque`] rather than faking a body.

use std::collections::{HashMap, HashSet};

use trust_ir::proof::{
    CleanCicKernelRecheck, KERNEL_ANCHOR_GIVEBACK_AGGREGATE, KERNEL_ANCHOR_GIVEBACK_COND,
    KERNEL_ANCHOR_GIVEBACK_LOOP, KERNEL_ANCHOR_GIVEBACK_NESTED, KERNEL_ANCHOR_GIVEBACK_REFINEMENT,
};
use trust_ir::{
    BinOp, BlockId, Constant, FuncId, Function, Inst, InstrNode, Module, ObligationKind, ProofId,
    ProofObligation, ProofStatus, Ty, ValueId,
};

/// The outcome of running the give-back elaborator over a [`Function`].
#[derive(Debug, Clone, PartialEq)]
pub enum GiveBackOutcome {
    /// The function is in the M1 decidable subset; a [`GiveBackView`] was built.
    Accepted(GiveBackView),
    /// The function is outside the supported fragment (fail-closed). The
    /// [`DeclineReason`] records *why* so the caller can report it (no silent
    /// drops, per the design).
    Declined(DeclineReason),
}

/// Why the elaborator declined a function. Every variant is a *safe* decline:
/// the caller falls back to the existing permission/heap path.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DeclineReason {
    /// The function is a body-less declaration (nothing to elaborate).
    NoBody,
    /// A parameter is a raw pointer (`PtrConst`/`PtrMut`), `Rc`, or a bare
    /// opaque `Ptr` — outside the safe-sequential-`&mut` fragment.
    RawPointerOrRc(&'static str),
    /// A `&mut`-of-a-reference parameter, or a `BorrowMut` of an existing borrow
    /// handle: nested mutable borrows are deferred past M1.
    NestedMutableBorrow,
    /// There is no `&mut` region to give back. The conservative, documented M1
    /// choice is to DECLINE (rather than accept with no obligation): there is
    /// nothing for the give-back view to certify, so it must not manufacture an
    /// obligation.
    NoMutableBorrow,
    /// More than one `&mut` ([`BorrowMut`](trust_ir::Inst::BorrowMut)) region;
    /// M1 is single-region only. Carries the observed region count.
    MultipleMutRegions(usize),
    /// The control-flow graph contains a back-edge / loop.
    LoopOrBackEdge,
    /// The control flow is neither straight-line NOR a recognized `&mut` *diamond*
    /// (entry `CondBr` → two straight-line branches → a single common join). The
    /// accepted diamond is synthesized PATH-SENSITIVELY (each path independently,
    /// combined with [`GiveBackExpr::Cond`] — see [`recognize_cond_diamond`]), which
    /// is sound; but anything else (a `Switch`, a second `CondBr`, branches that do
    /// not reconverge, block-argument passing on the branch edges) is declined
    /// fail-closed, since path-insensitive synthesis of it could give back a mutation
    /// as if it were unconditional. Wider control flow (nested/multi-way) is future
    /// work atop the proven `KERNEL_ANCHOR_GIVEBACK_COND` laws.
    ConditionalControlFlow,
    /// An instruction the whitelist does not understand. Carries the variant
    /// name for diagnostics.
    UnsupportedInstruction(&'static str),
    /// A `SeqMap` whose element function cannot be soundly elaborated:
    /// missing from the module (or no module context — the legacy
    /// [`elaborate_give_back`] shim), or itself containing a `SeqMap`
    /// (the recursive elaboration must strictly descend — design
    /// `2026-06-30-general-seqmap-instruction.md` §3 step 5). Fail-closed.
    SeqMapFwdOutsideFragment(&'static str),
}

/// The give-back view of a single-region `&mut` [`Function`].
///
/// Records the region, the borrowed place/value, and the **synthesized** forward
/// result and backward (give-back) value expressions — real [`GiveBackExpr`]
/// bodies produced by symbolic execution of the borrow region, not placeholders.
#[derive(Debug, Clone, PartialEq)]
pub struct GiveBackView {
    /// The single `&mut` region recovered from the body.
    pub region: BorrowRegion,
    /// Forward function descriptor (`f_fwd`).
    pub forward: ForwardFn,
    /// Backward / give-back function descriptor (`f_back_'a`).
    pub backward: BackwardFn,
}

/// The single `&mut` region: its borrow handle and the place it borrows.
#[derive(Debug, Clone, PartialEq)]
pub struct BorrowRegion {
    /// SSA value produced by the [`BorrowMut`](trust_ir::Inst::BorrowMut)
    /// instruction — the borrow handle that the matching
    /// [`EndBorrow`](trust_ir::Inst::EndBorrow) closes.
    pub handle: ValueId,
    /// The borrowed place/value: the `ptr` operand of the `BorrowMut`.
    pub borrowed: ValueId,
    /// Pointee type of the `&mut` region, when it is recoverable from the
    /// matching `RefMut(T)` parameter type. `None` if the borrowed value is not
    /// a directly-typed parameter (region/lifetime info is erased on the spine).
    pub pointee: Option<Ty>,
}

/// A **synthesized** give-back function body: a pure first-order expression over
/// the borrowed input value `x_in` and constants, produced by symbolic execution
/// of the borrow region (no placeholder). This is the Aeneas give-back value made
/// concrete — e.g. for `*x += 1` the backward body is
/// `BinOp(Add, BorrowedInput, Const(1))`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum GiveBackExpr {
    /// The initial value at the borrowed place when the `&mut` began (`x_in`).
    BorrowedInput,
    /// A compile-time integer constant.
    Const(i128),
    /// A trust-ir binary operation on two sub-expressions.
    BinOp(BinOp, Box<GiveBackExpr>, Box<GiveBackExpr>),
    /// The element-wise increment of a sequence sub-expression (`Inst::SeqMapAddK`) —
    /// Aeneas's `loopFwd`, the value the borrowed sequence holds after
    /// `for x in &mut l { *x += 1 }`. `SeqMapIncr(BorrowedInput)` is the loop give-back
    /// shape; its backward function `loopBack` (map `pred`) inverts it, certified by the
    /// kernel `loop_roundTrip` structural-induction law.
    SeqMapIncr(Box<GiveBackExpr>),
    /// The element-wise boolean flip of a sequence sub-expression (`Inst::SeqMapNot`) —
    /// `loopFwd` for `for b in &mut l { *b = !*b }`. `Bool.not` is self-inverse, so the
    /// backward function is `map not`, certified by the kernel `boolNotLoop_roundTrip`
    /// theorem — a SECOND element op proving the loop give-back is not `+k`-locked.
    SeqMapNot(Box<GiveBackExpr>),
    /// The element-wise map of a sequence sub-expression by a FIRST-CLASS element
    /// function (`Inst::SeqMap`) — `loopFwd` for `for x in &mut l { *x = fwd(x) }`
    /// with an arbitrary (but separately certified) element operation. The loop
    /// backward function is `map (giveback fwd)`; its round-trip is ONE application
    /// of the universe-polymorphic kernel law `listMapT_roundTrip` to `fwd`'s own
    /// (recursively elaborated + certified) scalar round-trip — no new metatheory.
    /// See `designs/2026-06-30-general-seqmap-instruction.md` §3.
    SeqMapGen {
        /// The element operation: a single-`&mut` function `fn(&mut elem)`.
        fwd: FuncId,
        /// The mapped sequence sub-expression (must be the borrowed input for
        /// the loop shape to certify).
        inner: Box<GiveBackExpr>,
    },
    /// Projection of one `field` out of an aggregate sub-expression
    /// (`ExtractField`): `aggregate.field`. For a `&mut (A, B)` borrow,
    /// `Field(BorrowedInput, 0)` is the give-back analog of Aeneas's `aggFstFwd`
    /// (read field 0 of the pair the borrow began with).
    Field(Box<GiveBackExpr>, u32),
    /// An aggregate with one `field` replaced by `value`, all other fields framed
    /// (`InsertField`): `{ base with .field = value }`. For a `&mut p.0` borrow,
    /// `WithField { base: BorrowedInput, field: 0, .. }` is exactly Aeneas's
    /// backward function `aggFstBack p v' = Prod.mk v' p.snd`.
    WithField {
        /// The aggregate being updated (`x_in` for a top-level `&mut Struct`).
        base: Box<GiveBackExpr>,
        /// The field index that is overwritten.
        field: u32,
        /// The new value placed at `field`.
        value: Box<GiveBackExpr>,
    },
    /// A PATH-SENSITIVE conditional give-back: `if cond then then_val else else_val`.
    /// Synthesized from a recognized `&mut` *diamond* (entry `CondBr` → two
    /// straight-line branches → a common join). Each branch's give-back is computed
    /// by genuine PER-PATH symbolic execution of the linearized path
    /// (`entry-prefix ++ branch ++ join`) and the two are combined here — they are
    /// never merged path-insensitively (that is the unsoundness the straight-line
    /// gate guards against). Models Aeneas's `condSet c old v` combinator
    /// (`Bool.rec` on the runtime flag): on `true` the place gives back `then_val`,
    /// on `false` `else_val`.
    Cond {
        /// The branch condition (the `CondBr` flag's expression; typically opaque,
        /// since the certifying laws hold for ALL flag values by case analysis).
        cond: Box<GiveBackExpr>,
        /// Give-back value along the `true` (then) path.
        then_val: Box<GiveBackExpr>,
        /// Give-back value along the `false` (else / frame) path.
        else_val: Box<GiveBackExpr>,
    },
    /// An SSA value not derived from the borrowed input or constants (e.g. another
    /// parameter, or the result of an instruction outside the modelled fragment).
    /// Honest: marks where synthesis bottomed out at an opaque input rather than
    /// faking a body.
    Opaque(ValueId),
}

/// The forward function `f_fwd`: the original function's return values, each as a
/// **synthesized** [`GiveBackExpr`] over the borrowed input (real, not a placeholder).
#[derive(Debug, Clone, PartialEq)]
pub struct ForwardFn {
    /// The SSA values the original function returns.
    pub result: Vec<ValueId>,
    /// One synthesized body expression per returned value.
    pub result_exprs: Vec<GiveBackExpr>,
}

/// The backward / give-back function `f_back_'a`: the value the borrowed place
/// holds when the borrow ends, as a **synthesized** [`GiveBackExpr`] over `x_in`.
#[derive(Debug, Clone, PartialEq)]
pub struct BackwardFn {
    /// The region handle this give-back function closes over.
    pub region: ValueId,
    /// The borrowed place the give-back value flows back into when the borrow ends.
    pub borrowed: ValueId,
    /// The synthesized give-back value: what `*borrowed` equals when the borrow
    /// ends, in terms of `BorrowedInput` (the value when it began). For an
    /// untouched `&mut` this is exactly [`GiveBackExpr::BorrowedInput`].
    pub value_expr: GiveBackExpr,
}

/// Run the M1 give-back elaborator over `func` WITHOUT module context.
///
/// Legacy arity kept as a shim over [`elaborate_give_back_in`] with an empty
/// module: identical behavior for every module-independent shape, and
/// fail-closed (`DeclineReason::SeqMapFwdOutsideFragment`) for `Inst::SeqMap`,
/// whose element `FuncId` cannot be resolved without a module.
pub fn elaborate_give_back(func: &Function) -> GiveBackOutcome {
    elaborate_give_back_in(func, &Module::new("<no-module-context>"))
}

/// Run the M1 give-back elaborator over `func` in `module` context.
///
/// Returns [`GiveBackOutcome::Accepted`] with a [`GiveBackView`] iff `func` is
/// in the non-nested single-region `&mut` decidable subset; otherwise
/// [`GiveBackOutcome::Declined`] with the reason. The gate is a conservative
/// whitelist and always fails closed (see crate docs).
///
/// The module context is the load-bearing edge of the general `SeqMap` loop
/// (design `2026-06-30-general-seqmap-instruction.md` §3a): resolving
/// `SeqMap.fwd` — for the strict-descent termination guard here, and for the
/// recursive element elaboration in [`certifying_anchor_in`] /
/// [`give_back_recheck_directive_in`].
pub fn elaborate_give_back_in(func: &Function, module: &Module) -> GiveBackOutcome {
    use GiveBackOutcome::Declined;

    // (1) Must have a body to analyze.
    if func.blocks.is_empty() {
        return Declined(DeclineReason::NoBody);
    }

    // (2) Parameter-type gate. Reject raw pointers / Rc / opaque Ptr outright,
    //     and reject `&mut`-of-a-reference (nested mutable borrow in the type).
    if let Some(entry) = func.entry_block() {
        for (_, ty) in &entry.params {
            if let Some(name) = raw_or_rc_name(ty) {
                return Declined(DeclineReason::RawPointerOrRc(name));
            }
            if let Ty::RefMut(inner) = ty
                && is_reference_like(inner)
            {
                return Declined(DeclineReason::NestedMutableBorrow);
            }
        }
    }

    // (3) Whitelist every instruction. Anything not explicitly understood is an
    //     immediate fail-closed decline.
    for block in &func.blocks {
        for node in &block.body {
            if let Inst::SeqMap { fwd, .. } = &node.inst {
                // Module-dependent SeqMap gates (design §3 step 5).
                // (a) The element function must resolve in the module — with
                //     the module-less shim this ALWAYS declines (fail-closed).
                let Some(fwd_func) = module.function_by_id(*fwd) else {
                    return Declined(DeclineReason::SeqMapFwdOutsideFragment(
                        "element function not found in module (or no module context)",
                    ));
                };
                // (b) TERMINATION guard: the recursive elaboration must
                //     strictly descend, so the element function's body must
                //     contain no SeqMap of its own. Because `Call` is not on
                //     the M1 whitelist either, this one-level check also rules
                //     out every transitive route to another SeqMap — nested
                //     element-op loops decline here rather than recurse.
                let fwd_contains_seq_map = fwd_func
                    .blocks
                    .iter()
                    .any(|b| b.body.iter().any(|n| matches!(n.inst, Inst::SeqMap { .. })));
                if fwd_contains_seq_map {
                    return Declined(DeclineReason::SeqMapFwdOutsideFragment(
                        "element function itself contains a SeqMap (recursion must strictly descend)",
                    ));
                }
                continue;
            }
            if let Some(name) = unsupported_inst_name(&node.inst) {
                return Declined(DeclineReason::UnsupportedInstruction(name));
            }
        }
    }

    // (4) Back-edge / loop detection over the (whitelisted) control flow. A
    //     successor whose block position is <= the current block's position is a
    //     back-edge; M1 declines all loops. (Checked before the straight-line gate
    //     so a genuine loop is reported as LoopOrBackEdge, the more specific reason.)
    if has_back_edge(func) {
        return Declined(DeclineReason::LoopOrBackEdge);
    }

    // (5) CONTROL-FLOW gate (soundness, adversarial-review H2 + T-cond).
    //     The give-back synthesizer ([`synthesize_path`]) is path-LOCAL. A
    //     straight-line body is one path; a recognized `&mut` *diamond* (entry
    //     `CondBr` → two straight-line branches → common join) is exactly two paths,
    //     each synthesized independently and combined with `Cond` — sound. ANY other
    //     control flow (a `Switch`, a second `CondBr`, an unrecognizable merge) is
    //     declined fail-closed, because path-insensitive synthesis of it would give
    //     back a mutation as if it were unconditional. The actual straight-line /
    //     diamond decision + routing happens at synthesis time (step 7); here we only
    //     fail closed on shapes that are NEITHER.
    if !is_straight_line(func) && recognize_cond_diamond(func).is_none() {
        return Declined(DeclineReason::ConditionalControlFlow);
    }

    // (5) Collect borrow handles and the `&mut` regions.
    let mut borrow_handles: Vec<ValueId> = Vec::new();
    let mut mut_regions: Vec<(ValueId, ValueId)> = Vec::new(); // (handle, borrowed)
    for block in &func.blocks {
        for node in &block.body {
            match &node.inst {
                Inst::Borrow { ptr } => {
                    if let Some(h) = node.results.first() {
                        borrow_handles.push(*h);
                    }
                    let _ = ptr;
                }
                Inst::BorrowMut { ptr } => {
                    if let Some(h) = node.results.first() {
                        borrow_handles.push(*h);
                        mut_regions.push((*h, *ptr));
                    }
                }
                _ => {}
            }
        }
    }

    // (5a) Nested mutable borrow: a `BorrowMut` whose borrowed place is itself a
    //      borrow handle composes backward functions in lifetime order — M1
    //      defers this.
    for (handle, borrowed) in &mut_regions {
        if borrow_handles.iter().any(|h| h == borrowed) {
            let _ = handle;
            return Declined(DeclineReason::NestedMutableBorrow);
        }
    }

    // (6) Region-count gate.
    match mut_regions.len() {
        0 => return Declined(DeclineReason::NoMutableBorrow),
        1 => {}
        n => return Declined(DeclineReason::MultipleMutRegions(n)),
    }
    let (handle, borrowed) = mut_regions[0];

    // (7) ACCEPT. Build the structural view. Pointee type is recovered from the
    //     matching `RefMut(T)` parameter when the borrowed value is a param.
    let pointee = func.entry_block().and_then(|entry| {
        entry.params.iter().find_map(|(vid, ty)| {
            if *vid == borrowed
                && let Ty::RefMut(inner) = ty
            {
                return Some((**inner).clone());
            }
            None
        })
    });

    let result = forward_result(func);

    // Synthesize the REAL give-back bodies by symbolic execution of the borrow
    // region: track each SSA value's expression over `x_in`, and the value at the
    // borrowed place across stores. No placeholder.
    //
    // Straight-line bodies synthesize in one pass; a recognized diamond synthesizes
    // each path independently and combines them into a `Cond` give-back (path-
    // sensitive — never merged as if unconditional).
    let synth = if let Some(diamond) = recognize_cond_diamond(func) {
        synthesize_cond_diamond(func, &diamond, handle, borrowed)
    } else {
        synthesize_give_back(func, handle, borrowed)
    };
    let result_exprs = result
        .iter()
        .map(|v| synth.value_of(*v))
        .collect::<Vec<_>>();

    GiveBackOutcome::Accepted(GiveBackView {
        region: BorrowRegion {
            handle,
            borrowed,
            pointee,
        },
        forward: ForwardFn {
            result,
            result_exprs,
        },
        backward: BackwardFn {
            region: handle,
            borrowed,
            value_expr: synth.place_value,
        },
    })
}

/// Result of symbolically executing a single-region `&mut` body: the give-back
/// value at the borrowed place, plus the synthesized expression of every SSA value.
struct Synthesis {
    /// Symbolic value at the borrowed place when the borrow ends (the `f_back` body).
    place_value: GiveBackExpr,
    /// Synthesized expression for each SSA value seen.
    values: HashMap<ValueId, GiveBackExpr>,
}

impl Synthesis {
    fn value_of(&self, v: ValueId) -> GiveBackExpr {
        self.values
            .get(&v)
            .cloned()
            .unwrap_or(GiveBackExpr::Opaque(v))
    }
}

/// Symbolically execute the (loop-free, gate-accepted) body to synthesize the
/// give-back bodies. Reads through the `&mut` (`Load` of `handle`/`borrowed`)
/// yield the current place value; `Store`s through it update the place value;
/// `Const`/`BinOp`/`Copy` build first-order expressions over `BorrowedInput`.
fn synthesize_give_back(func: &Function, handle: ValueId, borrowed: ValueId) -> Synthesis {
    synthesize_path(
        func.blocks.iter().flat_map(|b| b.body.iter()),
        handle,
        borrowed,
    )
}

/// Symbolically execute ONE straight-line instruction sequence — a single basic
/// block, or a *linearized* diamond path (`entry-prefix ++ branch-body ++ join`) —
/// to synthesize the give-back value at the borrowed place plus every SSA value's
/// expression. Path-LOCAL by construction: callers that handle control flow run
/// this once per path and combine the per-path results with [`GiveBackExpr::Cond`],
/// so a conditional mutation is NEVER synthesized as if it were unconditional (the
/// unsoundness the straight-line gate guards against).
fn synthesize_path<'a>(
    nodes: impl Iterator<Item = &'a InstrNode>,
    handle: ValueId,
    borrowed: ValueId,
) -> Synthesis {
    let mut values: HashMap<ValueId, GiveBackExpr> = HashMap::new();
    // The borrowed place starts holding the borrow's initial value, `x_in`.
    let mut place_value = GiveBackExpr::BorrowedInput;
    let is_place = |p: ValueId| p == handle || p == borrowed;
    let lookup = |values: &HashMap<ValueId, GiveBackExpr>, v: ValueId| {
        values.get(&v).cloned().unwrap_or(GiveBackExpr::Opaque(v))
    };

    for node in nodes {
        let result = node.results.first().copied();
        match &node.inst {
            // Reading `*x` yields the current value at the borrowed place.
            Inst::Load { ptr, .. } if is_place(*ptr) => {
                if let Some(r) = result {
                    values.insert(r, place_value.clone());
                }
            }
            // Writing `*x` updates the give-back value at the place.
            Inst::Store { ptr, value, .. } if is_place(*ptr) => {
                place_value = lookup(&values, *value);
            }
            Inst::Const {
                value: Constant::Int(n),
                ..
            } => {
                if let Some(r) = result {
                    values.insert(r, GiveBackExpr::Const(*n));
                }
            }
            Inst::BinOp { op, lhs, rhs, .. } => {
                if let Some(r) = result {
                    let e = GiveBackExpr::BinOp(
                        *op,
                        Box::new(lookup(&values, *lhs)),
                        Box::new(lookup(&values, *rhs)),
                    );
                    values.insert(r, e);
                }
            }
            Inst::Copy { operand, .. } => {
                if let Some(r) = result {
                    let e = lookup(&values, *operand);
                    values.insert(r, e);
                }
            }
            // Reading field `f` out of an aggregate value: `agg.f`.
            Inst::ExtractField {
                aggregate, field, ..
            } => {
                if let Some(r) = result {
                    let e = GiveBackExpr::Field(Box::new(lookup(&values, *aggregate)), *field);
                    values.insert(r, e);
                }
            }
            // Rebuilding an aggregate with field `f` replaced (all others framed):
            // `{ agg with .f = v }` — the structural give-back of a field `&mut`.
            Inst::InsertField {
                aggregate,
                field,
                value,
                ..
            } => {
                if let Some(r) = result {
                    let e = GiveBackExpr::WithField {
                        base: Box::new(lookup(&values, *aggregate)),
                        field: *field,
                        value: Box::new(lookup(&values, *value)),
                    };
                    values.insert(r, e);
                }
            }
            // Element-wise sequence increment (loopFwd): map +k over the sequence.
            Inst::SeqMapAddK { seq, .. } => {
                if let Some(r) = result {
                    let e = GiveBackExpr::SeqMapIncr(Box::new(lookup(&values, *seq)));
                    values.insert(r, e);
                }
            }
            // Element-wise boolean flip (loopFwd): map not over the sequence.
            Inst::SeqMapNot { seq, .. } => {
                if let Some(r) = result {
                    let e = GiveBackExpr::SeqMapNot(Box::new(lookup(&values, *seq)));
                    values.insert(r, e);
                }
            }
            // Element-wise map by a first-class element function (loopFwd):
            // map fwd over the sequence. `fwd` is a FuncId, recorded as-is;
            // resolution + recursive certification happen in the module-aware
            // certification stage (certifying_anchor_in).
            Inst::SeqMap { seq, fwd, .. } => {
                if let Some(r) = result {
                    let e = GiveBackExpr::SeqMapGen {
                        fwd: *fwd,
                        inner: Box::new(lookup(&values, *seq)),
                    };
                    values.insert(r, e);
                }
            }
            // Any other instruction with a result: its value is opaque (an
            // input we don't model), recorded honestly rather than faked.
            _ => {
                if let Some(r) = result {
                    values.insert(r, GiveBackExpr::Opaque(r));
                }
            }
        }
    }

    Synthesis {
        place_value,
        values,
    }
}

/// Returns true iff `func` is a single basic block with no conditional branch —
/// the one-path case [`synthesize_give_back`] handles directly.
fn is_straight_line(func: &Function) -> bool {
    func.blocks.len() == 1
        && !func
            .blocks
            .iter()
            .any(|b| b.body.iter().any(|n| matches!(n.inst, Inst::CondBr { .. })))
}

/// A recognized `&mut` *diamond*: an entry block ending in a `CondBr` whose two
/// targets each run straight-line and reconverge at a single join block. This is
/// the ONLY conditional shape the elaborator accepts (strict + fail-closed):
/// anything else (a `Switch`, a second `CondBr`, asymmetric/irreducible merges, or
/// block-argument passing on the branch edges) is not a diamond and is declined.
struct CondDiamond {
    /// The entry block (where the `CondBr` lives).
    entry_id: BlockId,
    /// The `CondBr` flag value.
    cond: ValueId,
    /// The block executed only on the `true` edge before the join (`== join_id`
    /// when the then-branch is empty, i.e. `if c { } else { … }`).
    then_id: BlockId,
    /// The block executed only on the `false` edge before the join (`== join_id`
    /// when the else-branch is empty, i.e. `if c { … }`).
    else_id: BlockId,
    /// The common reconvergence block.
    join_id: BlockId,
}

/// Recognize the conditional diamond, or `None` if `func` is not exactly one.
/// STRICT by design — see [`CondDiamond`].
fn recognize_cond_diamond(func: &Function) -> Option<CondDiamond> {
    let entry = func.blocks.first()?;
    // Entry must terminate in a CondBr with NO block-argument passing (block args
    // would rebind values across the edge, which the synthesizer does not model).
    let (cond, then_target, else_target) = match entry.body.last().map(|n| &n.inst) {
        Some(Inst::CondBr {
            cond,
            then_target,
            then_args,
            else_target,
            else_args,
        }) if then_args.is_empty() && else_args.is_empty() => (*cond, *then_target, *else_target),
        _ => return None,
    };
    if then_target == else_target {
        return None; // degenerate (not a real branch)
    }
    let get = |id: BlockId| func.blocks.iter().find(|b| b.id == id);
    // The unconditional-jump target of a straight-line block (ending in `Br` with
    // no args), else None.
    let br_target = |b: &trust_ir::Block| match b.body.last().map(|n| &n.inst) {
        Some(Inst::Br { target, args }) if args.is_empty() => Some(*target),
        _ => None,
    };
    let tb = get(then_target)?;
    let eb = get(else_target)?;
    // Determine the join from the three sound diamond shapes.
    let (then_id, else_id, join_id) = match (br_target(tb), br_target(eb)) {
        // Full diamond: both branches jump to a common join.
        (Some(j1), Some(j2)) if j1 == j2 => (then_target, else_target, j1),
        // Empty else (`if c { … }`): the false edge IS the join (where the
        // then-branch also lands).
        (Some(j), _) if j == else_target => (then_target, else_target, else_target),
        // Empty then (`if c { } else { … }`): symmetric.
        (_, Some(j)) if j == then_target => (then_target, else_target, then_target),
        _ => return None,
    };
    // SOUNDNESS: the join must be TERMINAL (ends in `Return`/`Unreachable`). This is
    // the canonical &mut-diamond shape (the region's `EndBorrow` + `Return` live in
    // the join) and — critically — it rejects a *chain* CFG like `then → else → X`,
    // `else → X`, where `else_target` is a non-trivial block rather than the real
    // reconvergence `X`. Without this check the `then → else_target` arm above would
    // mistake `else_target` for the join and the synthesizer would MISS `X`'s body
    // (an unsound, incomplete give-back). A terminal join cannot continue, so both
    // paths' mutations are fully captured by the `entry-prefix ++ branch ++ join`
    // linearization.
    let join = get(join_id)?;
    match join.body.last().map(|n| &n.inst) {
        Some(Inst::Return { .. }) | Some(Inst::Unreachable) => {}
        _ => return None,
    }
    // STRICTNESS: no Switch anywhere, and no CondBr outside the entry block.
    for b in &func.blocks {
        for n in &b.body {
            match &n.inst {
                Inst::Switch { .. } => return None,
                Inst::CondBr { .. } if b.id != entry.id => return None,
                _ => {}
            }
        }
    }
    Some(CondDiamond {
        entry_id: entry.id,
        cond,
        then_id,
        else_id,
        join_id,
    })
}

/// The blocks executed, in order, along one diamond path: the entry prefix, then
/// the branch block (unless it IS the join — an empty branch), then the join.
fn diamond_path_blocks(d: &CondDiamond, branch_id: BlockId) -> Vec<BlockId> {
    let mut v = vec![d.entry_id];
    if branch_id != d.join_id {
        v.push(branch_id);
    }
    v.push(d.join_id);
    v
}

/// Synthesize a path-sensitive give-back for a recognized diamond. Each path
/// (`entry-prefix ++ branch ++ join`) is a genuine straight-line execution, so it
/// is synthesized by [`synthesize_path`] independently; the two place-values are
/// combined into a [`GiveBackExpr::Cond`] — never merged as if unconditional. The
/// returned SSA `values` are the then-path's (used only for forward results; the
/// backward give-back IS the `Cond`).
fn synthesize_cond_diamond(
    func: &Function,
    d: &CondDiamond,
    handle: ValueId,
    borrowed: ValueId,
) -> Synthesis {
    let nodes_of = |ids: &[BlockId]| -> Vec<&InstrNode> {
        ids.iter()
            .filter_map(|id| func.blocks.iter().find(|b| b.id == *id))
            .flat_map(|b| b.body.iter())
            .collect()
    };
    let then_blocks = diamond_path_blocks(d, d.then_id);
    let else_blocks = diamond_path_blocks(d, d.else_id);
    let then_synth = synthesize_path(nodes_of(&then_blocks).into_iter(), handle, borrowed);
    let else_synth = synthesize_path(nodes_of(&else_blocks).into_iter(), handle, borrowed);

    // The condition's expression (both paths see the entry prefix, so either map
    // resolves it identically; typically Opaque for a runtime flag).
    let cond_expr = then_synth.value_of(d.cond);
    let place_value = GiveBackExpr::Cond {
        cond: Box::new(cond_expr),
        then_val: Box::new(then_synth.place_value.clone()),
        else_val: Box::new(else_synth.place_value.clone()),
    };
    Synthesis {
        place_value,
        values: then_synth.values,
    }
}

/// Build the `GiveBackRefinement` proof obligation for an accepted `view`.
///
/// The obligation is **always** `ProofStatus::Pending`. Current downstream
/// give-back anchors recheck fixed law libraries for assurance only and reject
/// every `Certified` give-back claim; promotion requires a future typed ground
/// proposition and consumed proof term bound to this exact function. This
/// function never produces `Certified`.
///
/// The obligation id is derived deterministically from `function`; callers that
/// attach the obligation to a `Module` (by pushing onto
/// `Module.proof_obligations`) may renumber it to keep ids unique within the
/// module, which the core crate does not auto-assign.
pub fn give_back_obligation(view: &GiveBackView, function: FuncId) -> ProofObligation {
    let description = format!(
        "give-back refinement for &mut region (handle v{}, borrowed v{}): \
         (f_fwd, f_back) must refine the value-at-address semantics; \
         Pending until a Clean refinement certificate discharges it",
        view.region.handle.index(),
        view.region.borrowed.index(),
    );
    ProofObligation::new(
        ProofId::new(function.index()),
        ObligationKind::GiveBackRefinement,
        ProofStatus::Pending,
        description,
    )
    .with_function(function)
}

/// A kernel law anchor + theorems relevant to a synthesized give-back body.
///
/// This is the BRIDGE that makes the give-back pipeline a single chain rather
/// than two disconnected halves: the (untrusted) elaborator synthesizes a
/// [`GiveBackExpr`], and this maps that exact shape to the in-process
/// `clean-kernel` anchor + axiom-clean theorems whose proof TERMs the trusted
/// re-checker can verify for **law assurance** (`trust_ir_build::validate`). It
/// is deliberately CONSERVATIVE: it returns `Some` only for shapes covered by
/// those library laws and `None` otherwise. This mapping is not an
/// obligation-bound proof and therefore cannot promote a give-back to
/// `Certified`; the obligation stays `Pending`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GiveBackCertification {
    /// The in-process kernel anchor identifier (e.g.
    /// [`KERNEL_ANCHOR_GIVEBACK_REFINEMENT`]).
    pub anchor: &'static str,
    /// The fully-qualified axiom-clean theorem(s) that certify the give-back shape.
    pub theorems: Vec<&'static str>,
}

/// Returns `Some(k)` iff `e` is `x_in + k` for a positive constant `k` — the value
/// written back by the scalar `*x += k` (the give-back of a constant increment). The
/// parameterized `addKBack_step` law certifies every such `k` (k = 1 is the former
/// `*x += 1` case).
fn x_in_plus_const(e: &GiveBackExpr) -> Option<i128> {
    if let GiveBackExpr::BinOp(BinOp::Add, lhs, rhs) = e
        && let GiveBackExpr::Const(k) = **rhs
        && k >= 1
    {
        // Single step `x_in + k`.
        if matches!(**lhs, GiveBackExpr::BorrowedInput) {
            return Some(k);
        }
        // Nested constant-increment chain `(x_in + a) + k` = `x_in + (a + k)` — the
        // give-back of `*x += a; *x += k; …` through one borrow. Still certified by the
        // SAME parameterized `addKBack_step` at the summed constant (composition is
        // denotational: the chain reduces to a single write-back `x_in + (a+k)`).
        if let Some(a) = x_in_plus_const(lhs) {
            return a.checked_add(k);
        }
    }
    None
}

/// True iff `e` is `Field(BorrowedInput, 0) + 1` — the value placed back into
/// field 0 by `p.0 += 1` (the body of the canonical Aeneas aggregate example).
fn is_borrowed_field0_plus_one(e: &GiveBackExpr) -> bool {
    if let GiveBackExpr::BinOp(BinOp::Add, lhs, rhs) = e
        && let GiveBackExpr::Field(fb, 0) = &**lhs
        && matches!(**fb, GiveBackExpr::BorrowedInput)
        && matches!(**rhs, GiveBackExpr::Const(1))
    {
        return true;
    }
    false
}

/// Returns `Some(n)` iff `e` is the aggregate field-`n` increment give-back
/// `WithField(x_in, n, x_in.n + 1)` (the give-back of `p.n += 1`), else `None`.
/// Any field of a pair — the field-0 case is the H3 aggregate; the field-1 case is
/// the payload update of a tagged-enum match (`if Some { *x += 1 }` lowered to a
/// tagged 2-tuple). Reused as a BRANCH shape inside a conditional-aggregate `Cond`.
fn aggregate_incr_field(e: &GiveBackExpr) -> Option<u32> {
    if let GiveBackExpr::WithField { base, field, value } = e
        && matches!(**base, GiveBackExpr::BorrowedInput)
        && let GiveBackExpr::BinOp(BinOp::Add, lhs, rhs) = &**value
        && let GiveBackExpr::Field(fb, fidx) = &**lhs
        && *fidx == *field
        && matches!(**fb, GiveBackExpr::BorrowedInput)
        && matches!(**rhs, GiveBackExpr::Const(1))
    {
        return Some(*field);
    }
    None
}

/// True iff `e` is a certified "active" branch of a conditional give-back — a scalar
/// increment `x_in + 1` OR a pair-field increment `WithField(x_in, n, x_in.n + 1)`.
/// The universe-polymorphic `condSetP` certifies the conditional over EITHER (the
/// pointee guard then checks the place type matches the branch).
fn is_active_incr_branch(e: &GiveBackExpr) -> bool {
    x_in_plus_const(e).is_some() || aggregate_incr_field(e).is_some()
}

/// True iff `e` is a certified branch of a conditional give-back: an active increment
/// OR the identity frame (an untouched branch). Both are certifiable give-backs, so a
/// `Cond` whose branches are all certified — with at least one actually mutating — is
/// certified by `condSetP` (e.g. `if c { *x += 1 } else { *x += 2 }`).
fn is_certified_branch(e: &GiveBackExpr) -> bool {
    is_active_incr_branch(e) || matches!(e, GiveBackExpr::BorrowedInput)
}

/// Returns `Some(n)` for `n ∈ {0,1}` iff `e` is a pair-field SET give-back
/// `WithField(x_in, n, <value>)` (replace field `n` with some value, frame the rest)
/// that is NOT the more-specific field-`n` increment. This is the give-back of
/// `p.n = value`, certified by the universe-polymorphic pair lens (`fstLensP` for
/// field 0, `sndLensP` for field 1) over a pair of ANY element types. Nested shapes
/// (matched by an earlier arm) are handled before this by match order.
fn field_set_index(e: &GiveBackExpr) -> Option<u32> {
    if let GiveBackExpr::WithField { base, field, .. } = e
        && matches!(**base, GiveBackExpr::BorrowedInput)
        && *field < 2
        && aggregate_incr_field(e) != Some(*field)
    {
        return Some(*field);
    }
    None
}

/// True iff `ty` is a 2-element tuple of ANY element types (the trust-ir type the
/// polymorphic pair lens models — no `int` restriction on the elements).
fn is_pair(ty: &Ty) -> bool {
    matches!(ty, Ty::Tuple(fs) if fs.len() == 2)
}

/// True iff `e` is the give-back of a DOUBLY-nested field increment `p.0.0 += 1`:
/// `WithField(x_in, 0, WithField(Field(x_in,0), 0, Field(Field(x_in,0),0) + 1))`
/// — i.e. `nestBack x_in (nestFwd x_in + 1)` in structural form (rebuild the outer
/// pair with its field 0 replaced by the inner pair whose field 0 is the deep field
/// incremented; both siblings framed).
fn is_nested_field00_incr(e: &GiveBackExpr) -> bool {
    // outer: WithField(BorrowedInput, 0, inner)
    let GiveBackExpr::WithField {
        base,
        field: 0,
        value: inner,
    } = e
    else {
        return false;
    };
    if !matches!(**base, GiveBackExpr::BorrowedInput) {
        return false;
    }
    // inner: WithField(Field(BorrowedInput, 0), 0, deep_incr)
    let GiveBackExpr::WithField {
        base: ibase,
        field: 0,
        value: deep_incr,
    } = &**inner
    else {
        return false;
    };
    let GiveBackExpr::Field(ib, 0) = &**ibase else {
        return false;
    };
    if !matches!(**ib, GiveBackExpr::BorrowedInput) {
        return false;
    }
    // deep_incr: Field(Field(BorrowedInput, 0), 0) + 1
    let GiveBackExpr::BinOp(BinOp::Add, lhs, rhs) = &**deep_incr else {
        return false;
    };
    if !matches!(**rhs, GiveBackExpr::Const(1)) {
        return false;
    }
    let GiveBackExpr::Field(l1, 0) = &**lhs else {
        return false;
    };
    let GiveBackExpr::Field(l2, 0) = &**l1 else {
        return false;
    };
    matches!(**l2, GiveBackExpr::BorrowedInput)
}

/// True iff a synthesized ELEMENT give-back shape is a recognized REVERSIBLE
/// operation — i.e. its inverse exists and is certified by a proven kernel law,
/// so `listMapT_roundTrip`'s `∀x, finv (f x) = x` hypothesis is discharged by
/// the element tier's own round-trip theorem. First milestone (design §3b):
///
/// * `x_in + k` (constant increment; inverse `-k`, hypothesis `addKBack_step`)
/// * `BorrowedInput` (untouched identity; self-inverse, hypothesis `backIdP`)
///
/// Anything else fails closed: inverting an arbitrary element function is
/// undecidable (2026-07-01 coverage audit), so the whitelist only grows one
/// proven inverse lemma at a time (pair-field lens increment is the named
/// next step).
fn element_give_back_is_reversible(e: &GiveBackExpr) -> bool {
    x_in_plus_const(e).is_some() || matches!(e, GiveBackExpr::BorrowedInput)
}

/// Map a synthesized backward-function body to the kernel anchor + theorems that
/// certify it, or `None` if no proven law covers the shape (fail-closed).
///
/// Honest coverage today (each backed by axiom-clean `clean-kernel` theorems that
/// STATE the give-back, so the cited theorem genuinely expresses the function's
/// backward function — not an algebraic corollary):
/// * `BorrowedInput` (an untouched `&mut`) → the identity round-trip law
///   `backId v = v`.
/// * `x_in + k` for any constant `k ≥ 1` (the give-back of `*x += k`) → the
///   PARAMETERIZED step law `addKBack_step : ∀ k v, addKBack k v = v + k` — one law
///   for every constant increment (`*x += 2`, `*x += 100`, …), not just `*x += 1`.
/// * `WithField(x_in, 0, x_in.0 + 1)` (the give-back of an aggregate field-0
///   increment `p.0 += 1` over a `&mut (A, B)`) → the aggregate lens laws
///   `aggFst_incr` + `aggFst_frame` (H3 — the first NON-scalar shape, binds to a
///   real `&mut Struct` function).
/// * `WithField(x_in, 0, WithField(x_in.0, 0, x_in.0.0 + 1))` (the give-back of a
///   doubly-nested field increment `p.0.0 += 1` over a `&mut ((A, B), C)`) → the
///   nested lens laws `nest_incr` + `nest_frameInner` + `nest_frameOuter`, which
///   STATE that the deep field reads back as `incr(old)` and BOTH siblings are
///   framed (two-level structure-eta).
/// * `Cond(c, <active>, x_in)` (and its mirror) — the give-back of ANY conditional
///   increment: scalar `if c { *x += 1 }`, aggregate `if c { p.0 += 1 }`, or enum
///   `match o { Some(x) => *x += 1, .. }` (Option as a tagged 2-tuple, payload update
///   on the `Some` branch). ALL certified by the SINGLE universe-polymorphic pair of
///   case laws `condSetP_true` + `condSetP_false` (`∀ {α} old v`), which state that the
///   `Bool.rec` combinator yields the taken-branch value on `true` and frames on
///   `false` for any place type `α`. Path-sensitive (branches synthesized PER-PATH,
///   T-cond); the pointee guard checks the place TYPE matches the active branch. This
///   is the anti-catalog primitive: one law for every conditional place type, instead
///   of a per-type `condSet` / `condSetPair` / … .
///
/// Each shape cites its OWN per-shape anchor (`build_anchor_env` dispatches on the
/// anchor string to rebuild the matching clean-kernel env). Any other shape
/// (`x_in + c` for `c ≠ 1`, other field indices, non-incr branches, opaque inputs,
/// unmodelled ops) is `None` (fail-closed): the obligation stays `Pending`.
#[must_use]
pub fn certifying_anchor(value_expr: &GiveBackExpr) -> Option<GiveBackCertification> {
    certifying_anchor_in(value_expr, &Module::new("<no-module-context>"))
}

/// Module-aware [`certifying_anchor`]: identical for every module-independent
/// shape, plus the general `SeqMap` loop shape, which needs the module to
/// RECURSIVELY elaborate + certify its element function (design
/// `2026-06-30-general-seqmap-instruction.md` §3 steps 2–3). No combined /
/// cross-anchor env: the loop cert cites ONLY `listMapT_roundTrip` (proven in
/// the loop anchor); the element operation carries its OWN independently
/// rechecked obligation in ITS own anchor.
#[must_use]
pub fn certifying_anchor_in(
    value_expr: &GiveBackExpr,
    module: &Module,
) -> Option<GiveBackCertification> {
    match value_expr {
        // Untouched `&mut` of ANY type: the give-back is the identity; certified by the
        // universe-POLYMORPHIC round-trip law `backIdP v = v` (∀ {α}), so an untouched
        // `&mut Struct` / `&mut Enum` certifies too, not just a scalar.
        GiveBackExpr::BorrowedInput => Some(GiveBackCertification {
            anchor: KERNEL_ANCHOR_GIVEBACK_REFINEMENT,
            theorems: vec!["RustSem.GiveBack.backIdP_roundTrips"],
        }),
        // The give-back of a CONSTANT increment `*x += k` for any k ≥ 1: x_in + k.
        // Cite the PARAMETERIZED step law `addKBack_step : ∀ k v, addKBack k v = v + k`
        // — ONE law covering every constant increment (subsumes the k = 1 case), so
        // `*x += 2`, `*x += 100`, … certify, not just `*x += 1`.
        _ if x_in_plus_const(value_expr).is_some() => Some(GiveBackCertification {
            anchor: KERNEL_ANCHOR_GIVEBACK_REFINEMENT,
            theorems: vec!["RustSem.GiveBack.addKBack_step"],
        }),
        // THE LOOP GIVE-BACK — `for x in &mut l { *x += k }`: the borrowed sequence ends
        // holding `SeqMapIncr(x_in)` = loopFwd(x_in) (every element mapped by the constant
        // increment `+k`). Its backward function is `map (λx. x - k)`, and the round-trip
        // is the GENERAL law `listMap_roundTrip` (∀ f finv, (∀x, finv(f x)=x) → ∀l,
        // listMap finv (listMap f l) = l), proved in the kernel by List.rec STRUCTURAL
        // INDUCTION for ANY reversible element operation — not just `+1`. Also cite
        // `loop_roundTrip`/`loopFwd_cons` (the `k = 1` instance). Aeneas's signature loop
        // backward function, generalized to any constant increment and bound to a real fn.
        GiveBackExpr::SeqMapIncr(inner) if matches!(**inner, GiveBackExpr::BorrowedInput) => {
            Some(GiveBackCertification {
                anchor: KERNEL_ANCHOR_GIVEBACK_LOOP,
                theorems: vec![
                    "RustSem.GiveBack.listMap_roundTrip",
                    "RustSem.GiveBack.loop_roundTrip",
                    "RustSem.GiveBack.loopFwd_cons",
                ],
            })
        }
        // THE SECOND ELEMENT-OP LOOP — `for b in &mut l { *b = !*b }`: the borrowed
        // sequence ends holding `SeqMapNot(x_in)` = map not (x_in). `Bool.not` is
        // self-inverse, so the backward function is `map not`, certified by the kernel
        // `boolNotLoop_roundTrip` (an instance of the type-polymorphic `listMapT_roundTrip`
        // at A=Bool). Proves the loop give-back is not `+k`-locked — a genuinely different,
        // non-arithmetic element op bound to a real function.
        GiveBackExpr::SeqMapNot(inner) if matches!(**inner, GiveBackExpr::BorrowedInput) => {
            Some(GiveBackCertification {
                anchor: KERNEL_ANCHOR_GIVEBACK_LOOP,
                theorems: vec![
                    "RustSem.GiveBack.boolNotLoop_roundTrip",
                    "RustSem.GiveBack.listMapT_roundTrip",
                ],
            })
        }
        // THE GENERAL ELEMENT-OP LOOP — `for x in &mut l { *x = fwd(x) }` with a
        // FIRST-CLASS element function (`Inst::SeqMap`). The loop composes with the
        // scalar tier RECURSIVELY (design §1): re-elaborate the element function in
        // the module; the loop certifies iff the ELEMENT give-back is itself
        // certified AND is a recognized REVERSIBLE shape. Then the loop backward
        // function is `map (giveback fwd)` and its round-trip is ONE application of
        // the universe-polymorphic `listMapT_roundTrip` (∀ {A} f finv, (∀x, finv (f
        // x) = x) → ∀l, listMapT finv (listMapT f l) = l) to `fwd`'s own round-trip
        // — already kernel-checked by the element tier. The loop cert cites ONLY
        // `listMapT_roundTrip`; no combined env, no new axioms, fail-closed on
        // anything the element tier does not prove.
        //
        // First milestone (design §3b, deliberately de-risked): the recognized
        // reversible element shapes are the scalar constant increment `x_in + k`
        // (give-back `map (-k)`; hypothesis = `addKBack_step`) and the untouched
        // identity (`backIdP`). Extending coverage = widening
        // `element_give_back_is_reversible`, one shape at a time.
        GiveBackExpr::SeqMapGen { fwd, inner }
            if matches!(**inner, GiveBackExpr::BorrowedInput) =>
        {
            // Resolve + recursively elaborate the element function. The
            // strict-descent guard in elaborate_give_back_in ensures the
            // element view can never itself contain a SeqMapGen, so this
            // recursion terminates after ONE level.
            let fwd_func = module.function_by_id(*fwd)?;
            let element_view = match elaborate_give_back_in(fwd_func, module) {
                GiveBackOutcome::Accepted(view) => view,
                GiveBackOutcome::Declined(_) => return None, // fail-closed
            };
            // The element give-back must be a recognized REVERSIBLE shape…
            if !element_give_back_is_reversible(&element_view.backward.value_expr) {
                return None; // fail-closed: inverting arbitrary fwd is undecidable
            }
            // …and must itself be certified in ITS own anchor (pointee guard
            // included) — an uncertified fwd cannot be laundered into a loop cert.
            give_back_recheck_directive_in(&element_view, module)?;
            Some(GiveBackCertification {
                anchor: KERNEL_ANCHOR_GIVEBACK_LOOP,
                theorems: vec!["RustSem.GiveBack.listMapT_roundTrip"],
            })
        }
        // The give-back of an aggregate field-0 increment `p.0 += 1` over a
        // `&mut (A, B)`: rebuild the pair with field 0 set to `(p.0)_in + 1` and
        // field 1 framed — Aeneas's backward function `aggFstBack p (incr p.fst)`.
        // Cite the two axiom-clean laws that STATE this give-back: `aggFst_incr`
        // (after the mutation, reading p.0 yields incr(old p.0)) and `aggFst_frame`
        // (the sibling field p.1 is left untouched). Together they fully express
        // the `WithField(x_in, 0, x_in.0 + 1)` structural give-back — the first
        // NON-scalar shape that binds the synthesized body to a real function.
        GiveBackExpr::WithField {
            base,
            field: 0,
            value,
        } if matches!(**base, GiveBackExpr::BorrowedInput)
            && is_borrowed_field0_plus_one(value) =>
        {
            // NOTE the anchor: the aggregate laws live in the SEPARATE
            // `init_giveback_aggregate_refinement` env, so the directive must cite
            // `KERNEL_ANCHOR_GIVEBACK_AGGREGATE` — `build_anchor_env` dispatches on
            // this string to decide which clean-kernel env to rebuild, and only that
            // env registers `aggFst_incr`/`aggFst_frame`.
            Some(GiveBackCertification {
                anchor: KERNEL_ANCHOR_GIVEBACK_AGGREGATE,
                theorems: vec![
                    "RustSem.GiveBack.aggFst_incr",
                    "RustSem.GiveBack.aggFst_frame",
                ],
            })
        }
        // The give-back of a DOUBLY-nested field increment `p.0.0 += 1` over a
        // `&mut ((A, B), C)`: rebuild BOTH levels — the inner pair with the deep field
        // set to `incr(old)` and the outer pair with that inner — framing both siblings
        // (`p.0.1`, `p.1`). Aeneas's `nestBack p (nestFwd p + 1)`. Cite the laws that
        // STATE it under the SEPARATE `rust_giveback_nested` anchor: `nest_incr` (deep
        // field reads back as incr) + `nest_frameInner` + `nest_frameOuter` (both
        // siblings untouched, proved by two-level structure-eta).
        _ if is_nested_field00_incr(value_expr) => Some(GiveBackCertification {
            anchor: KERNEL_ANCHOR_GIVEBACK_NESTED,
            theorems: vec![
                "RustSem.GiveBack.nest_incr",
                "RustSem.GiveBack.nest_frameInner",
                "RustSem.GiveBack.nest_frameOuter",
            ],
        }),
        // GENERAL LENS — the give-back of a pair-field SET `p.n = a` over a `&mut (A, B)`
        // of ANY element types: `WithField(x_in, n, a)` = the field-`n` lens applied. Cite
        // the universe-POLYMORPHIC pair-lens laws (`fstLensP` for field 0, `sndLensP` for
        // field 1) — putGet (field `n` reads back as `a`) + frame (sibling untouched),
        // holding for ALL `A`, `B`. The general-lens generalization: one polymorphic lens
        // per projection instead of a per-element-type aggregate law (works for pairs of
        // structs/enums/…, not just ints). The pointee guard confirms a 2-tuple.
        GiveBackExpr::WithField { base, field: 0, .. }
            if matches!(**base, GiveBackExpr::BorrowedInput)
                && field_set_index(value_expr) == Some(0) =>
        {
            Some(GiveBackCertification {
                anchor: KERNEL_ANCHOR_GIVEBACK_AGGREGATE,
                theorems: vec![
                    "RustSem.GiveBack.fstLensP_putGet",
                    "RustSem.GiveBack.fstLensP_frame",
                ],
            })
        }
        GiveBackExpr::WithField { base, field: 1, .. }
            if matches!(**base, GiveBackExpr::BorrowedInput)
                && field_set_index(value_expr) == Some(1) =>
        {
            Some(GiveBackCertification {
                anchor: KERNEL_ANCHOR_GIVEBACK_AGGREGATE,
                theorems: vec![
                    "RustSem.GiveBack.sndLensP_putGet",
                    "RustSem.GiveBack.sndLensP_frame",
                ],
            })
        }
        // The give-back of ANY conditional increment whose taken branch is a certified
        // give-back and whose untaken branch frames — ONE arm, ONE law, for every place
        // type, thanks to the universe-POLYMORPHIC `condSetP`. Covers:
        //   * scalar `if c { *x += 1 }`            (active branch = x_in + 1);
        //   * aggregate `if c { p.0 += 1 }`        (active branch = WithField(x_in,0,·)) — T-cond ∘ H3;
        //   * enum `match o { Some(x)=>*x+=1, None=>() }` over `&mut Option<T>` — at the
        //     IR level `Option` is a tagged 2-tuple `{tag, payload}`, the match is a
        //     diamond on `icmp(tag,1)`, and the taken branch updates the PAYLOAD (field 1);
        //   * either `if c {…}` / `if c {} else {…}` orientation;
        //   * and BOTH branches mutating differently, e.g. `if c { *x += 1 } else { *x += 2 }`
        //     (give-back `Cond(c, x_in+1, x_in+2) = condSetP c (x_in+2) (x_in+1)`).
        // The `Bool.rec` case laws `condSetP_true`/`condSetP_false` hold for ANY α, so a
        // single citation certifies the conditional for any place type — the branch
        // values were synthesized PER-PATH (sound, not a path-insensitive merge), and the
        // pointee guard ([`give_back_recheck_directive`]) confirms BOTH branches' TYPE.
        // Each branch must be a certified give-back (an increment or the identity frame),
        // and at least one must actually mutate. This replaces the former per-type
        // condSet / condSetPair citations: the anti-catalog primitive in action.
        GiveBackExpr::Cond {
            cond: _,
            then_val,
            else_val,
        } if is_certified_branch(then_val)
            && is_certified_branch(else_val)
            && (is_active_incr_branch(then_val) || is_active_incr_branch(else_val)) =>
        {
            Some(GiveBackCertification {
                anchor: KERNEL_ANCHOR_GIVEBACK_COND,
                theorems: vec![
                    "RustSem.GiveBack.condSetP_true",
                    "RustSem.GiveBack.condSetP_false",
                ],
            })
        }
        _ => None,
    }
}

/// Build the [`CleanCicKernelRecheck`] directive for the fixed law library
/// relevant to a give-back VIEW, or `None` when no safe mapping exists. The
/// directive is useful for theorem assurance and candidate reporting only:
/// `trust_ir_build::validate` rejects it as `Certified` until a typed ground
/// proposition and proof term bind the exact function semantics.
/// True iff `ty` is a fixed-width integer scalar (the trust-ir types the clean
/// `Nat`-typed give-back laws model).
fn is_int_scalar(ty: &Ty) -> bool {
    matches!(
        ty,
        Ty::I8
            | Ty::I16
            | Ty::I32
            | Ty::I64
            | Ty::I128
            | Ty::U8
            | Ty::U16
            | Ty::U32
            | Ty::U64
            | Ty::U128
    )
}

/// True iff `ty` is a 2-element tuple of integer scalars — the trust-ir type the
/// `Prod Nat Nat` aggregate/cond-aggregate laws model.
fn is_int_pair(ty: &Ty) -> bool {
    matches!(ty, Ty::Tuple(fs) if fs.len() == 2 && fs.iter().all(is_int_scalar))
}

/// True when a synthesized give-back depends on fixed-width machine arithmetic.
///
/// Clean's currently wired `addKBack_step`/aggregate/nested/loop arithmetic laws
/// are stated over unbounded `Nat`; TrustIR evaluates integer `Add` modulo the
/// operand width for every I*/U* type. A theorem true over Nat is therefore not
/// authority for these program operations (e.g. U8::MAX + 1 = 0, not 256).
/// Walk recursively so arithmetic cannot be laundered through a conditional,
/// aggregate, nested projection, or sequence map. For a first-class `SeqMap`,
/// re-elaborate the element function and inspect its synthesized give-back too;
/// failure to resolve/elaborate is conservatively authority-blocking.
const ARITHMETIC_WALK_MAX_DEPTH: usize = 128;
const ARITHMETIC_WALK_MAX_NODES: usize = 4_096;

struct ArithmeticWalk {
    visiting_functions: HashSet<FuncId>,
    remaining_nodes: usize,
}

fn uses_fixed_width_arithmetic(expr: &GiveBackExpr, module: &Module) -> bool {
    let mut walk = ArithmeticWalk {
        visiting_functions: HashSet::new(),
        remaining_nodes: ARITHMETIC_WALK_MAX_NODES,
    };
    uses_fixed_width_arithmetic_inner(expr, module, 0, &mut walk)
}

fn uses_fixed_width_arithmetic_inner(
    expr: &GiveBackExpr,
    module: &Module,
    depth: usize,
    walk: &mut ArithmeticWalk,
) -> bool {
    // `true` means authority-blocked. Exhaustion and cycles therefore fail
    // closed rather than risking unbounded recursion on an attacker-shaped
    // module graph.
    if depth > ARITHMETIC_WALK_MAX_DEPTH || walk.remaining_nodes == 0 {
        return true;
    }
    walk.remaining_nodes -= 1;

    match expr {
        GiveBackExpr::BinOp(..) | GiveBackExpr::SeqMapIncr(_) => true,
        GiveBackExpr::SeqMapGen { fwd, inner } => {
            if uses_fixed_width_arithmetic_inner(inner, module, depth + 1, walk) {
                return true;
            }
            if !walk.visiting_functions.insert(*fwd) {
                return true;
            }
            let Some(fwd_func) = module.function_by_id(*fwd) else {
                walk.visiting_functions.remove(fwd);
                return true;
            };
            let GiveBackOutcome::Accepted(view) = elaborate_give_back_in(fwd_func, module) else {
                walk.visiting_functions.remove(fwd);
                return true;
            };
            let blocked = uses_fixed_width_arithmetic_inner(
                &view.backward.value_expr,
                module,
                depth + 1,
                walk,
            );
            walk.visiting_functions.remove(fwd);
            blocked
        }
        GiveBackExpr::SeqMapNot(inner) | GiveBackExpr::Field(inner, _) => {
            uses_fixed_width_arithmetic_inner(inner, module, depth + 1, walk)
        }
        GiveBackExpr::WithField { base, value, .. } => {
            uses_fixed_width_arithmetic_inner(base, module, depth + 1, walk)
                || uses_fixed_width_arithmetic_inner(value, module, depth + 1, walk)
        }
        GiveBackExpr::Cond {
            cond,
            then_val,
            else_val,
        } => {
            uses_fixed_width_arithmetic_inner(cond, module, depth + 1, walk)
                || uses_fixed_width_arithmetic_inner(then_val, module, depth + 1, walk)
                || uses_fixed_width_arithmetic_inner(else_val, module, depth + 1, walk)
        }
        GiveBackExpr::BorrowedInput | GiveBackExpr::Const(_) | GiveBackExpr::Opaque(_) => false,
    }
}

/// TYPE guard (closes the type-erasure leg): a synthesized give-back shape may only
/// certify when the `&mut` place's `pointee` type matches the type the monomorphic
/// clean law is stated over. Without this, a WIDER struct doing `field0 += 1` would
/// synthesize the same type-erased `WithField(x_in, 0, ·)` shape and spuriously cite
/// the `Prod Nat Nat` pair law. Fail-closed: no pointee ⇒ reject.
fn pointee_matches_shape(module: &Module, pointee: Option<&Ty>, expr: &GiveBackExpr) -> bool {
    let Some(ty) = pointee else {
        return false;
    };
    match expr {
        // Untouched &mut → the POLYMORPHIC identity law backIdP (∀ {α}): ANY place type
        // is fine (the law holds for every α). We still require a known pointee (Some).
        GiveBackExpr::BorrowedInput => {
            let _ = ty;
            true
        }
        // Loop give-back (loopFwd): the place must be a Sequence (the clean loop laws are
        // over List Nat / List A).
        GiveBackExpr::SeqMapIncr(_) | GiveBackExpr::SeqMapNot(_) => {
            matches!(ty, Ty::Sequence(_))
        }
        // General element-op loop: the place must be `Sequence(elem)` with a
        // module-resolvable `elem` that is EXACTLY the element function's
        // `&mut` pointee (design §3 step 4) — a `Seq<bool>` place cannot
        // certify against an `fn(&mut i32)` element op. Fail-closed on any
        // unresolvable piece.
        GiveBackExpr::SeqMapGen { fwd, .. } => {
            let Ty::Sequence(elem_id) = ty else {
                return false;
            };
            let Some(elem) = module.ty(*elem_id) else {
                return false;
            };
            let Some(fwd_func) = module.function_by_id(*fwd) else {
                return false;
            };
            let Some(fwd_ty) = module.func_type(fwd_func.ty) else {
                return false;
            };
            fwd_ty.returns.is_empty()
                && !fwd_ty.is_vararg
                && fwd_ty.params.len() == 1
                && matches!(&fwd_ty.params[0], Ty::RefMut(p) if **p == *elem)
        }
        // Conditional: BOTH branches must match the place type (the identity frame
        // matches any type via backIdP; an active increment must match its shape). This
        // covers one-branch-mutates AND both-branches-mutate conditionals.
        GiveBackExpr::Cond {
            then_val, else_val, ..
        } => {
            pointee_matches_shape(module, pointee, then_val)
                && pointee_matches_shape(module, pointee, else_val)
        }
        _ if x_in_plus_const(expr).is_some() => is_int_scalar(ty),
        // Any pair-field increment (field 0 aggregate OR field 1 enum payload): the
        // place must be a 2-tuple of ints (Prod Nat Nat). The `field < 2` bound makes
        // the guard reject e.g. a 5-field struct's field-3 update on a mislabelled pair.
        _ if aggregate_incr_field(expr).is_some_and(|n| n < 2) => is_int_pair(ty),
        _ if is_nested_field00_incr(expr) => {
            matches!(ty, Ty::Tuple(fs) if fs.len() == 2 && is_int_pair(&fs[0]) && is_int_scalar(&fs[1]))
        }
        // A pair-field SET (`p.n = a`) via the polymorphic pair lens: the place must be a
        // 2-tuple, but of ANY element types (fstLensP/sndLensP are universe-polymorphic).
        // Placed AFTER the incr/nested cases so those keep their stricter int-typed guards.
        _ if field_set_index(expr).is_some() => is_pair(ty),
        _ => false,
    }
}

#[must_use]
pub fn give_back_recheck_directive(view: &GiveBackView) -> Option<CleanCicKernelRecheck> {
    give_back_recheck_directive_in(view, &Module::new("<no-module-context>"))
}

/// Module-aware [`give_back_recheck_directive`]: identical for every
/// module-independent shape; required for the general `SeqMap` loop, whose
/// certification recursively elaborates its element function in the module and
/// whose pointee guard resolves `Ty::Sequence(elem)` against the element
/// function's `&mut` pointee.
#[must_use]
pub fn give_back_recheck_directive_in(
    view: &GiveBackView,
    module: &Module,
) -> Option<CleanCicKernelRecheck> {
    // SOUNDNESS: fixed-width TrustIR arithmetic wraps, while the currently
    // available give-back arithmetic laws are over unbounded Nat. Rechecking
    // those library laws cannot establish this program's machine semantics.
    // Fail closed recursively until a width-aware, obligation-bound ground
    // proposition and proof are available.
    if uses_fixed_width_arithmetic(&view.backward.value_expr, module) {
        return None;
    }
    let cert = certifying_anchor_in(&view.backward.value_expr, module)?;
    // TYPE guard: the place type must match the monomorphic law's type, else the
    // (type-erased) shape match would mis-cite a law about a different type.
    if !pointee_matches_shape(
        module,
        view.region.pointee.as_ref(),
        &view.backward.value_expr,
    ) {
        return None;
    }
    Some(CleanCicKernelRecheck {
        module: "RustSem.GiveBack".to_string(),
        theorems: cert.theorems.iter().map(|s| (*s).to_string()).collect(),
        anchor: cert.anchor.to_string(),
        // The foundational CIC trust base; the cited laws are constructive
        // (Eq.refl over δ/β/ι). sorry/sorryAx are never admissible regardless.
        allowed_axioms: ["propext", "Classical.choice", "Quot.sound", "Eq.refl"]
            .iter()
            .map(|s| (*s).to_string())
            .collect(),
        binding: None,
    })
}

/// Returns a static name iff `ty` is a raw pointer / `Rc` / opaque pointer that
/// the M1 fragment excludes.
fn raw_or_rc_name(ty: &Ty) -> Option<&'static str> {
    match ty {
        Ty::PtrConst(_) => Some("PtrConst"),
        Ty::PtrMut(_) => Some("PtrMut"),
        Ty::Rc(_) => Some("Rc"),
        Ty::Ptr => Some("Ptr"),
        _ => None,
    }
}

/// Any reference-or-pointer-like type (used for nested-borrow detection).
fn is_reference_like(ty: &Ty) -> bool {
    matches!(
        ty,
        Ty::Ref(_) | Ty::RefMut(_) | Ty::PtrConst(_) | Ty::PtrMut(_) | Ty::Rc(_) | Ty::Ptr
    )
}

/// Returns the variant name iff `inst` is NOT on the M1 whitelist.
///
/// Whitelist (explicitly understood): the borrow trio, `Return`, simple
/// value/memory plumbing, and the branch terminators `Br`/`CondBr`. NOTE: the
/// straight-line gate in [`elaborate_give_back`] (step 3.5) declines any function
/// with `CondBr` or more than one block BEFORE this whitelist matters, because the
/// path-insensitive synthesizer would be unsound on branches (adversarial-review
/// H2); `Br`/`CondBr` remain whitelisted only so a hypothetical single-block
/// degenerate terminator does not trip the "unsupported instruction" path first.
/// Everything else fails closed — notably `Switch`, all calls, atomics,
/// raw-pointer casts, ARC, and proof instructions.
fn unsupported_inst_name(inst: &Inst) -> Option<&'static str> {
    match inst {
        // Borrow vocabulary — the heart of the analysis.
        Inst::Borrow { .. }
        | Inst::BorrowMut { .. }
        | Inst::EndBorrow { .. }
        // Simple, side-effect-understood plumbing.
        | Inst::Load { .. }
        | Inst::Store { .. }
        | Inst::Copy { .. }
        | Inst::Const { .. }
        | Inst::BinOp { .. }
        | Inst::ICmp { .. }
        | Inst::ExtractField { .. }
        | Inst::InsertField { .. }
        // Structural sequence increment / boolean flip (loopFwd) — core ops, fixed semantics.
        | Inst::SeqMapAddK { .. }
        | Inst::SeqMapNot { .. }
        // General element-op map (loopFwd with a first-class element FuncId).
        // The module-dependent gates (fwd resolvable, strict-descent) run in
        // elaborate_give_back_in's whitelist loop BEFORE this fn is consulted.
        | Inst::SeqMap { .. }
        // Forward-only control flow (back-edges rejected in has_back_edge).
        | Inst::Br { .. }
        | Inst::CondBr { .. }
        | Inst::Return { .. } => None,
        // Everything else is not understood -> fail closed.
        other => Some(inst_variant_name(other)),
    }
}

/// Best-effort variant name for a not-understood instruction (diagnostics only).
fn inst_variant_name(inst: &Inst) -> &'static str {
    match inst {
        Inst::Switch { .. } => "Switch",
        Inst::Call { .. } => "Call",
        Inst::CallIndirect { .. } => "CallIndirect",
        Inst::CallCannotUnwind { .. } => "CallCannotUnwind",
        Inst::CallIndirectCannotUnwind { .. } => "CallIndirectCannotUnwind",
        Inst::Unreachable => "Unreachable",
        Inst::Assume { .. } => "Assume",
        Inst::Assert { .. } => "Assert",
        Inst::Alloca { .. } => "Alloca",
        Inst::HeapAlloc { .. } => "HeapAlloc",
        Inst::Dealloc { .. } => "Dealloc",
        Inst::MemCopy { .. } => "MemCopy",
        Inst::MemSet { .. } => "MemSet",
        Inst::GEP { .. } => "GEP",
        Inst::AtomicLoad { .. } => "AtomicLoad",
        Inst::AtomicStore { .. } => "AtomicStore",
        Inst::AtomicRMW { .. } => "AtomicRMW",
        Inst::CmpXchg { .. } => "CmpXchg",
        Inst::Fence { .. } => "Fence",
        Inst::Retain { .. } => "Retain",
        Inst::Release { .. } => "Release",
        Inst::IsUnique { .. } => "IsUnique",
        _ => "unsupported",
    }
}

/// True iff the CFG has a back-edge: a terminator successor whose block position
/// is `<=` the source block's position. Conservative (treats any non-forward
/// edge as a loop), which is the safe direction for M1.
fn has_back_edge(func: &Function) -> bool {
    use std::collections::HashMap;
    let pos: HashMap<u32, usize> = func
        .blocks
        .iter()
        .enumerate()
        .map(|(i, b)| (b.id.index(), i))
        .collect();
    for (i, block) in func.blocks.iter().enumerate() {
        for node in &block.body {
            // Every edge, from the exhaustive accessor (amendment D §1.3):
            // the old walk saw only `Br` / `CondBr`, so a `Switch` or invoke
            // back edge read as loop-free (fail-open for M1).
            for edge in node.inst.successor_edges() {
                let t = edge.target;
                if let Some(&j) = pos.get(&t.index())
                    && j <= i
                {
                    return true;
                }
            }
        }
    }
    false
}

/// Structural forward result: the values of the (first) `Return` in the body.
fn forward_result(func: &Function) -> Vec<ValueId> {
    for block in &func.blocks {
        for node in &block.body {
            if let Inst::Return { values } = &node.inst {
                return values.clone();
            }
        }
    }
    Vec::new()
}

#[cfg(test)]
mod tests {
    use super::*;
    use trust_ir::{Block, BlockId, Constant, InstrNode};

    fn v(n: u32) -> ValueId {
        ValueId::new(n)
    }
    fn bid(n: u32) -> BlockId {
        BlockId::new(n)
    }

    /// A single-block function: `f(x: &mut i32)` borrows `x` mutably, ends the
    /// borrow, and returns unit. This is the canonical M1 ACCEPT case.
    fn single_mut_function() -> Function {
        let entry = bid(0);
        let mut func = Function::new(
            FuncId::new(7),
            "single_mut",
            trust_ir::FuncTyId::new(0),
            entry,
        );
        let mut block = Block::new(entry);
        // param v0 : &mut i32
        block.params.push((v(0), Ty::RefMut(Box::new(Ty::I32))));
        // v1 = borrow_mut v0
        block
            .body
            .push(InstrNode::new(Inst::BorrowMut { ptr: v(0) }).with_result(v(1)));
        // end_borrow v1
        block
            .body
            .push(InstrNode::new(Inst::EndBorrow { borrow_ptr: v(1) }));
        // return ()
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        func.blocks.push(block);
        func
    }

    #[test]
    fn single_mut_is_accepted_and_emits_pending_giveback_obligation() {
        let func = single_mut_function();
        let outcome = elaborate_give_back(&func);
        let view = match outcome {
            GiveBackOutcome::Accepted(v) => v,
            other => panic!("expected Accepted, got {other:?}"),
        };
        // The recovered region is the borrow handle v1 over borrowed place v0,
        // with the pointee type recovered from the `&mut i32` parameter.
        assert_eq!(view.region.handle, v(1));
        assert_eq!(view.region.borrowed, v(0));
        assert_eq!(view.region.pointee, Some(Ty::I32));
        assert_eq!(view.backward.region, v(1));
        assert_eq!(view.backward.borrowed, v(0));
        assert!(view.forward.result.is_empty());
        // The `&mut` is never written, so the synthesized give-back value is
        // exactly the unchanged input — the identity backward function, derived
        // (not assumed) by symbolic execution.
        assert_eq!(view.backward.value_expr, GiveBackExpr::BorrowedInput);
        assert!(view.forward.result_exprs.is_empty());

        let obl = give_back_obligation(&view, func.id);
        assert_eq!(obl.kind, ObligationKind::GiveBackRefinement);
        assert_eq!(obl.status, ProofStatus::Pending);
        assert_eq!(obl.function, Some(func.id));
    }

    /// `incr(x: &mut i32) { *x += 1 }` — borrow_mut, load `*x`, add 1, store back,
    /// end borrow. The elaborator must SYNTHESIZE the real backward function
    /// `f_back = x_in + 1`, i.e. `BinOp(Add, BorrowedInput, Const(1))` — proving
    /// give-back body synthesis is genuine, not a placeholder.
    fn incr_function() -> Function {
        let entry = bid(0);
        let mut func = Function::new(FuncId::new(11), "incr", trust_ir::FuncTyId::new(0), entry);
        let mut block = Block::new(entry);
        block.params.push((v(0), Ty::RefMut(Box::new(Ty::I32))));
        // v1 = borrow_mut v0
        block
            .body
            .push(InstrNode::new(Inst::BorrowMut { ptr: v(0) }).with_result(v(1)));
        // v2 = load *v1   (reads x_in)
        block.body.push(
            InstrNode::new(Inst::Load {
                ty: Ty::I32,
                ptr: v(1),
                volatile: false,
                align: None,
            })
            .with_result(v(2)),
        );
        // v3 = const 1
        block.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(1),
            })
            .with_result(v(3)),
        );
        // v4 = v2 + v3
        block.body.push(
            InstrNode::new(Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I32,
                lhs: v(2),
                rhs: v(3),
            })
            .with_result(v(4)),
        );
        // store *v1 = v4   (writes x_in + 1)
        block.body.push(InstrNode::new(Inst::Store {
            ty: Ty::I32,
            ptr: v(1),
            value: v(4),
            volatile: false,
            align: None,
        }));
        block
            .body
            .push(InstrNode::new(Inst::EndBorrow { borrow_ptr: v(1) }));
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        func.blocks.push(block);
        func
    }

    #[test]
    fn incr_synthesizes_real_backward_function_x_plus_one() {
        let func = incr_function();
        let view = match elaborate_give_back(&func) {
            GiveBackOutcome::Accepted(v) => v,
            other => panic!("expected Accepted, got {other:?}"),
        };
        // The SYNTHESIZED give-back body is exactly `x_in + 1` — derived by
        // symbolic execution of load/add/store, not a placeholder.
        let expected = GiveBackExpr::BinOp(
            BinOp::Add,
            Box::new(GiveBackExpr::BorrowedInput),
            Box::new(GiveBackExpr::Const(1)),
        );
        assert_eq!(
            view.backward.value_expr, expected,
            "incr's backward function must synthesize to x_in + 1"
        );
    }

    #[test]
    fn incr_synthesized_body_maps_to_nat_law_but_has_no_program_authority() {
        // The BRIDGE: the elaborator's SYNTHESIZED give-back body (x_in + 1) maps to
        // the PARAMETERIZED step law `addKBack_step` (∀ k v, addKBack k v = v+k) that
        // STATES the give-back for any constant increment — no hand-written citation.
        let func = incr_function();
        let view = match elaborate_give_back(&func) {
            GiveBackOutcome::Accepted(v) => v,
            other => panic!("expected Accepted, got {other:?}"),
        };
        let cert = certifying_anchor(&view.backward.value_expr)
            .expect("the synthesized x_in + 1 must bind to a certifying anchor");
        assert_eq!(cert.anchor, KERNEL_ANCHOR_GIVEBACK_REFINEMENT);
        assert!(
            cert.theorems.contains(&"RustSem.GiveBack.addKBack_step"),
            "incr must be certified by the parameterized give-back law addKBack_step, got {cert:?}"
        );

        assert!(
            give_back_recheck_directive(&view).is_none(),
            "the Nat add law is not authority for wrapping I32 addition"
        );
    }

    #[test]
    fn increment_by_two_maps_to_parameterized_nat_law_but_stays_pending() {
        // COVERAGE: `*x += 2` (k ≠ 1) synthesizes to `x_in + 2` and now binds — where
        // it previously declined (only k = 1 was recognized). One parameterized law
        // `addKBack_step` covers every constant increment.
        let entry = bid(0);
        let mut func = Function::new(FuncId::new(20), "incr2", trust_ir::FuncTyId::new(0), entry);
        let mut block = Block::new(entry);
        block.params.push((v(0), Ty::RefMut(Box::new(Ty::I32))));
        block
            .body
            .push(InstrNode::new(Inst::BorrowMut { ptr: v(0) }).with_result(v(1)));
        block.body.push(
            InstrNode::new(Inst::Load {
                ty: Ty::I32,
                ptr: v(1),
                volatile: false,
                align: None,
            })
            .with_result(v(2)),
        );
        block.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(2),
            })
            .with_result(v(3)),
        );
        block.body.push(
            InstrNode::new(Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I32,
                lhs: v(2),
                rhs: v(3),
            })
            .with_result(v(4)),
        );
        block.body.push(InstrNode::new(Inst::Store {
            ty: Ty::I32,
            ptr: v(1),
            value: v(4),
            volatile: false,
            align: None,
        }));
        block
            .body
            .push(InstrNode::new(Inst::EndBorrow { borrow_ptr: v(1) }));
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        func.blocks.push(block);

        let view = match elaborate_give_back(&func) {
            GiveBackOutcome::Accepted(v) => v,
            other => panic!("expected Accepted, got {other:?}"),
        };
        let expected = GiveBackExpr::BinOp(
            BinOp::Add,
            Box::new(GiveBackExpr::BorrowedInput),
            Box::new(GiveBackExpr::Const(2)),
        );
        assert_eq!(view.backward.value_expr, expected);
        let cert = certifying_anchor(&view.backward.value_expr)
            .expect("*x += 2 must now bind to the parameterized law");
        assert!(cert.theorems.contains(&"RustSem.GiveBack.addKBack_step"));
        assert!(
            give_back_recheck_directive(&view).is_none(),
            "*x += 2 over a fixed-width scalar must stay non-authoritative"
        );
    }

    /// `fn agg_fst_incr(p: &mut (I32, I32)) { p.0 += 1 }` — the canonical Aeneas
    /// aggregate example. Body: borrow_mut, load the whole pair, ExtractField 0,
    /// `+1`, InsertField 0, store the pair back. The synthesized give-back is the
    /// structural field update `WithField(x_in, 0, x_in.0 + 1)`.
    fn agg_fst_incr_function() -> Function {
        let entry = bid(0);
        let pair = Ty::Tuple(vec![Ty::I32, Ty::I32]);
        let mut func = Function::new(
            FuncId::new(12),
            "agg_fst_incr",
            trust_ir::FuncTyId::new(0),
            entry,
        );
        let mut block = Block::new(entry);
        block
            .params
            .push((v(0), Ty::RefMut(Box::new(pair.clone()))));
        // v1 = borrow_mut v0
        block
            .body
            .push(InstrNode::new(Inst::BorrowMut { ptr: v(0) }).with_result(v(1)));
        // v2 = load *v1  (reads the whole pair = x_in)
        block.body.push(
            InstrNode::new(Inst::Load {
                ty: pair.clone(),
                ptr: v(1),
                volatile: false,
                align: None,
            })
            .with_result(v(2)),
        );
        // v3 = extractfield v2 .0   (x_in.0)
        block.body.push(
            InstrNode::new(Inst::ExtractField {
                ty: Ty::I32,
                aggregate: v(2),
                field: 0,
            })
            .with_result(v(3)),
        );
        // v4 = const 1
        block.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(1),
            })
            .with_result(v(4)),
        );
        // v5 = v3 + v4   (x_in.0 + 1)
        block.body.push(
            InstrNode::new(Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I32,
                lhs: v(3),
                rhs: v(4),
            })
            .with_result(v(5)),
        );
        // v6 = insertfield v2 .0 = v5   ({ x_in with .0 = x_in.0 + 1 })
        block.body.push(
            InstrNode::new(Inst::InsertField {
                ty: pair.clone(),
                aggregate: v(2),
                field: 0,
                value: v(5),
            })
            .with_result(v(6)),
        );
        // store *v1 = v6
        block.body.push(InstrNode::new(Inst::Store {
            ty: pair,
            ptr: v(1),
            value: v(6),
            volatile: false,
            align: None,
        }));
        block
            .body
            .push(InstrNode::new(Inst::EndBorrow { borrow_ptr: v(1) }));
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        func.blocks.push(block);
        func
    }

    #[test]
    fn agg_fst_incr_synthesizes_structural_field_update_give_back() {
        let func = agg_fst_incr_function();
        let view = match elaborate_give_back(&func) {
            GiveBackOutcome::Accepted(v) => v,
            other => panic!("expected Accepted for a &mut (A,B) field incr, got {other:?}"),
        };
        // The SYNTHESIZED give-back is `{ x_in with .0 = x_in.0 + 1 }` — derived by
        // symbolic execution of load / extractfield / add / insertfield / store.
        let expected = GiveBackExpr::WithField {
            base: Box::new(GiveBackExpr::BorrowedInput),
            field: 0,
            value: Box::new(GiveBackExpr::BinOp(
                BinOp::Add,
                Box::new(GiveBackExpr::Field(
                    Box::new(GiveBackExpr::BorrowedInput),
                    0,
                )),
                Box::new(GiveBackExpr::Const(1)),
            )),
        };
        assert_eq!(
            view.backward.value_expr, expected,
            "aggregate field-0 incr must synthesize to WithField(x_in, 0, x_in.0 + 1)"
        );
    }

    #[test]
    fn agg_fst_incr_maps_to_nat_aggregate_law_but_stays_pending() {
        // H3: a NON-scalar synthesized give-back body binds — with no hand-written
        // citation — to the aggregate lens laws that STATE the give-back. The whole
        // chain (synthesis → certifying_anchor → recheck directive) runs over a real
        // `&mut Struct` function.
        let func = agg_fst_incr_function();
        let view = match elaborate_give_back(&func) {
            GiveBackOutcome::Accepted(v) => v,
            other => panic!("expected Accepted, got {other:?}"),
        };
        let cert = certifying_anchor(&view.backward.value_expr)
            .expect("the synthesized aggregate field update must bind to a certifying anchor");
        // The aggregate laws live in the aggregate anchor env, NOT the scalar one.
        assert_eq!(cert.anchor, KERNEL_ANCHOR_GIVEBACK_AGGREGATE);
        assert!(
            cert.theorems.contains(&"RustSem.GiveBack.aggFst_incr"),
            "aggregate field-0 incr must cite the give-back law aggFst_incr, got {cert:?}"
        );
        assert!(
            cert.theorems.contains(&"RustSem.GiveBack.aggFst_frame"),
            "aggregate field-0 incr must cite the frame law aggFst_frame, got {cert:?}"
        );

        assert!(
            give_back_recheck_directive(&view).is_none(),
            "an aggregate containing fixed-width addition must stay non-authoritative"
        );
    }

    #[test]
    fn other_field_index_does_not_falsely_bind_to_field0_anchor() {
        // Fail-closed: a give-back that updates field 1 (not 0) must NOT spuriously
        // cite the field-0 aggregate law. It stays uncertified (None) until a law
        // for that shape is proven.
        let field1_update = GiveBackExpr::WithField {
            base: Box::new(GiveBackExpr::BorrowedInput),
            field: 1,
            value: Box::new(GiveBackExpr::BinOp(
                BinOp::Add,
                Box::new(GiveBackExpr::Field(
                    Box::new(GiveBackExpr::BorrowedInput),
                    1,
                )),
                Box::new(GiveBackExpr::Const(1)),
            )),
        };
        assert!(
            certifying_anchor(&field1_update).is_none(),
            "field-1 update must not bind to the field-0 aggregate anchor (fail-closed)"
        );
    }

    #[test]
    fn field0_set_over_a_pair_of_any_types_certifies_via_the_polymorphic_lens() {
        // GENERAL LENS: `fn(p: &mut (bool, i32), a: bool) { p.0 = a }` — a field-0 SET
        // (not an increment) over a pair whose element types are NOT ints. The universe-
        // polymorphic fstLensP certifies it, where the Nat-specific aggregate law could
        // not (bool is not an int). Give-back = WithField(x_in, 0, a).
        let entry = bid(0);
        let pair = Ty::Tuple(vec![Ty::Bool, Ty::I32]);
        let mut func = Function::new(FuncId::new(22), "set0", trust_ir::FuncTyId::new(0), entry);
        let mut block = Block::new(entry);
        block
            .params
            .push((v(0), Ty::RefMut(Box::new(pair.clone()))));
        block.params.push((v(1), Ty::Bool)); // the new value `a`
        block
            .body
            .push(InstrNode::new(Inst::BorrowMut { ptr: v(0) }).with_result(v(2)));
        block.body.push(
            InstrNode::new(Inst::Load {
                ty: pair.clone(),
                ptr: v(2),
                volatile: false,
                align: None,
            })
            .with_result(v(3)),
        );
        block.body.push(
            InstrNode::new(Inst::InsertField {
                ty: pair.clone(),
                aggregate: v(3),
                field: 0,
                value: v(1),
            })
            .with_result(v(4)),
        );
        block.body.push(InstrNode::new(Inst::Store {
            ty: pair,
            ptr: v(2),
            value: v(4),
            volatile: false,
            align: None,
        }));
        block
            .body
            .push(InstrNode::new(Inst::EndBorrow { borrow_ptr: v(2) }));
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        func.blocks.push(block);

        let view = match elaborate_give_back(&func) {
            GiveBackOutcome::Accepted(v) => v,
            other => panic!("field-0 set must be accepted, got {other:?}"),
        };
        // give-back = { x_in with .0 = a } where a is the opaque parameter v1
        let expected = GiveBackExpr::WithField {
            base: Box::new(GiveBackExpr::BorrowedInput),
            field: 0,
            value: Box::new(GiveBackExpr::Opaque(v(1))),
        };
        assert_eq!(view.backward.value_expr, expected);
        let cert = certifying_anchor(&view.backward.value_expr)
            .expect("field-0 set must bind to the polymorphic pair lens");
        assert_eq!(cert.anchor, KERNEL_ANCHOR_GIVEBACK_AGGREGATE);
        assert!(cert.theorems.contains(&"RustSem.GiveBack.fstLensP_putGet"));
        assert!(cert.theorems.contains(&"RustSem.GiveBack.fstLensP_frame"));
        assert!(
            give_back_recheck_directive(&view).is_some(),
            "a &mut (bool, i32) field-0 set must certify via the polymorphic lens"
        );
    }

    #[test]
    fn field1_set_binds_to_the_sndlensp_projection() {
        // The SIBLING projection: a field-1 SET `p.1 = b` binds to sndLensP (the field-1
        // pair lens), completing the generic pair lens (both projections).
        let set1 = GiveBackExpr::WithField {
            base: Box::new(GiveBackExpr::BorrowedInput),
            field: 1,
            value: Box::new(GiveBackExpr::Opaque(v(7))),
        };
        let cert =
            certifying_anchor(&set1).expect("field-1 set must bind to the sndLensP projection");
        assert_eq!(cert.anchor, KERNEL_ANCHOR_GIVEBACK_AGGREGATE);
        assert!(cert.theorems.contains(&"RustSem.GiveBack.sndLensP_putGet"));
        assert!(cert.theorems.contains(&"RustSem.GiveBack.sndLensP_frame"));
        assert!(!cert.theorems.contains(&"RustSem.GiveBack.fstLensP_putGet"));
    }

    /// `fn nested(p: &mut ((i32,i32), i32)) { p.0.0 += 1 }` — the doubly-nested
    /// field increment. Body: load outer, extract .0 (inner), extract .0 (deep), +1,
    /// insert .0 into inner, insert .0 into outer, store. Synthesizes to the two-level
    /// `WithField(x_in, 0, WithField(x_in.0, 0, x_in.0.0 + 1))`.
    fn nested_field00_incr_function() -> Function {
        let entry = bid(0);
        let inner = Ty::Tuple(vec![Ty::I32, Ty::I32]);
        let outer = Ty::Tuple(vec![inner.clone(), Ty::I32]);
        let mut func = Function::new(FuncId::new(15), "nested", trust_ir::FuncTyId::new(0), entry);
        let mut block = Block::new(entry);
        block
            .params
            .push((v(0), Ty::RefMut(Box::new(outer.clone()))));
        block
            .body
            .push(InstrNode::new(Inst::BorrowMut { ptr: v(0) }).with_result(v(1)));
        block.body.push(
            InstrNode::new(Inst::Load {
                ty: outer.clone(),
                ptr: v(1),
                volatile: false,
                align: None,
            })
            .with_result(v(2)),
        );
        block.body.push(
            InstrNode::new(Inst::ExtractField {
                ty: inner.clone(),
                aggregate: v(2),
                field: 0,
            })
            .with_result(v(3)),
        );
        block.body.push(
            InstrNode::new(Inst::ExtractField {
                ty: Ty::I32,
                aggregate: v(3),
                field: 0,
            })
            .with_result(v(4)),
        );
        block.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(1),
            })
            .with_result(v(5)),
        );
        block.body.push(
            InstrNode::new(Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I32,
                lhs: v(4),
                rhs: v(5),
            })
            .with_result(v(6)),
        );
        block.body.push(
            InstrNode::new(Inst::InsertField {
                ty: inner.clone(),
                aggregate: v(3),
                field: 0,
                value: v(6),
            })
            .with_result(v(7)),
        );
        block.body.push(
            InstrNode::new(Inst::InsertField {
                ty: outer.clone(),
                aggregate: v(2),
                field: 0,
                value: v(7),
            })
            .with_result(v(8)),
        );
        block.body.push(InstrNode::new(Inst::Store {
            ty: outer,
            ptr: v(1),
            value: v(8),
            volatile: false,
            align: None,
        }));
        block
            .body
            .push(InstrNode::new(Inst::EndBorrow { borrow_ptr: v(1) }));
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        func.blocks.push(block);
        func
    }

    #[test]
    fn nested_field00_incr_synthesizes_two_level_give_back_and_binds() {
        let func = nested_field00_incr_function();
        let view = match elaborate_give_back(&func) {
            GiveBackOutcome::Accepted(v) => v,
            other => panic!("nested field incr must be accepted, got {other:?}"),
        };
        // give-back = { x_in with .0 = { x_in.0 with .0 = x_in.0.0 + 1 } }
        let x0 = || GiveBackExpr::Field(Box::new(GiveBackExpr::BorrowedInput), 0);
        let deep = GiveBackExpr::Field(Box::new(x0()), 0);
        let expected = GiveBackExpr::WithField {
            base: Box::new(GiveBackExpr::BorrowedInput),
            field: 0,
            value: Box::new(GiveBackExpr::WithField {
                base: Box::new(x0()),
                field: 0,
                value: Box::new(GiveBackExpr::BinOp(
                    BinOp::Add,
                    Box::new(deep),
                    Box::new(GiveBackExpr::Const(1)),
                )),
            }),
        };
        assert_eq!(
            view.backward.value_expr, expected,
            "nested p.0.0 += 1 must synthesize to the two-level WithField give-back"
        );

        let cert = certifying_anchor(&view.backward.value_expr)
            .expect("nested field incr must bind to the nested anchor");
        assert_eq!(cert.anchor, KERNEL_ANCHOR_GIVEBACK_NESTED);
        assert!(cert.theorems.contains(&"RustSem.GiveBack.nest_incr"));
        assert!(cert.theorems.contains(&"RustSem.GiveBack.nest_frameInner"));
        assert!(cert.theorems.contains(&"RustSem.GiveBack.nest_frameOuter"));
    }

    #[test]
    fn wider_struct_field0_incr_does_not_certify_with_the_pair_law() {
        // TYPE-ERASURE guard: a 3-field struct doing `p.0 += 1` synthesizes the SAME
        // type-erased `WithField(x_in, 0, x_in.0 + 1)` shape as a pair, and even matches
        // `certifying_anchor` (which is type-blind) — but its place is NOT `Prod Nat Nat`,
        // so `give_back_recheck_directive` must REFUSE it (the pointee-type guard), else it
        // would mis-cite the pair aggregate law for a 3-tuple. Fail-closed.
        let entry = bid(0);
        let triple = Ty::Tuple(vec![Ty::I32, Ty::I32, Ty::I32]);
        let mut func = Function::new(FuncId::new(17), "triple", trust_ir::FuncTyId::new(0), entry);
        let mut block = Block::new(entry);
        block
            .params
            .push((v(0), Ty::RefMut(Box::new(triple.clone()))));
        block
            .body
            .push(InstrNode::new(Inst::BorrowMut { ptr: v(0) }).with_result(v(1)));
        block.body.push(
            InstrNode::new(Inst::Load {
                ty: triple.clone(),
                ptr: v(1),
                volatile: false,
                align: None,
            })
            .with_result(v(2)),
        );
        block.body.push(
            InstrNode::new(Inst::ExtractField {
                ty: Ty::I32,
                aggregate: v(2),
                field: 0,
            })
            .with_result(v(3)),
        );
        block.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(1),
            })
            .with_result(v(4)),
        );
        block.body.push(
            InstrNode::new(Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I32,
                lhs: v(3),
                rhs: v(4),
            })
            .with_result(v(5)),
        );
        block.body.push(
            InstrNode::new(Inst::InsertField {
                ty: triple.clone(),
                aggregate: v(2),
                field: 0,
                value: v(5),
            })
            .with_result(v(6)),
        );
        block.body.push(InstrNode::new(Inst::Store {
            ty: triple,
            ptr: v(1),
            value: v(6),
            volatile: false,
            align: None,
        }));
        block
            .body
            .push(InstrNode::new(Inst::EndBorrow { borrow_ptr: v(1) }));
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        func.blocks.push(block);

        let view = match elaborate_give_back(&func) {
            GiveBackOutcome::Accepted(v) => v,
            other => panic!("expected Accepted, got {other:?}"),
        };
        // The type-ERASED shape still matches the aggregate arm...
        assert!(
            certifying_anchor(&view.backward.value_expr).is_some(),
            "the type-erased shape does match the (type-blind) aggregate anchor"
        );
        // ...but the recheck directive is REFUSED, because the place is a 3-tuple.
        assert!(
            give_back_recheck_directive(&view).is_none(),
            "a 3-field struct field-0 incr must NOT certify with the Prod Nat Nat pair law"
        );
    }

    /// `fn incr_all(l: &mut Seq<i32>) { for x in &mut l { *x += 1 } }` — lowered with the
    /// structural `SeqMapIncr` (loopFwd). The borrowed sequence ends holding
    /// `SeqMapIncr(x_in)`, whose backward function is `loopBack`, certified by
    /// `loop_roundTrip` (List.rec induction).
    fn seq_incr_all_function() -> Function {
        let entry = bid(0);
        let seq_ty = Ty::Sequence(trust_ir::TyId::new(0));
        let mut func = Function::new(
            FuncId::new(23),
            "incr_all",
            trust_ir::FuncTyId::new(0),
            entry,
        );
        let mut block = Block::new(entry);
        block
            .params
            .push((v(0), Ty::RefMut(Box::new(seq_ty.clone()))));
        block
            .body
            .push(InstrNode::new(Inst::BorrowMut { ptr: v(0) }).with_result(v(1)));
        block.body.push(
            InstrNode::new(Inst::Load {
                ty: seq_ty.clone(),
                ptr: v(1),
                volatile: false,
                align: None,
            })
            .with_result(v(2)),
        );
        block.body.push(
            InstrNode::new(Inst::SeqMapAddK {
                ty: seq_ty.clone(),
                seq: v(2),
                k: 1,
            })
            .with_result(v(3)),
        );
        block.body.push(InstrNode::new(Inst::Store {
            ty: seq_ty,
            ptr: v(1),
            value: v(3),
            volatile: false,
            align: None,
        }));
        block
            .body
            .push(InstrNode::new(Inst::EndBorrow { borrow_ptr: v(1) }));
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        func.blocks.push(block);
        func
    }

    #[test]
    fn loop_seq_incr_maps_to_nat_loop_law_but_stays_pending() {
        // THE SIGNATURE AENEAS FEATURE: a real `&mut Seq` map-loop function gives back
        // via the kernel loop laws (List.rec induction), no unrolling.
        let func = seq_incr_all_function();
        let view = match elaborate_give_back(&func) {
            GiveBackOutcome::Accepted(v) => v,
            other => panic!("seq incr-all must be accepted, got {other:?}"),
        };
        let expected = GiveBackExpr::SeqMapIncr(Box::new(GiveBackExpr::BorrowedInput));
        assert_eq!(
            view.backward.value_expr, expected,
            "the borrowed sequence must end holding SeqMapIncr(x_in) = loopFwd(x_in)"
        );
        let cert = certifying_anchor(&view.backward.value_expr)
            .expect("the loop give-back must bind to the loop anchor");
        assert_eq!(cert.anchor, KERNEL_ANCHOR_GIVEBACK_LOOP);
        assert!(cert.theorems.contains(&"RustSem.GiveBack.loop_roundTrip"));
        assert!(
            give_back_recheck_directive(&view).is_none(),
            "a fixed-width Seq map-loop must stay non-authoritative"
        );
    }

    #[test]
    fn untouched_mut_binds_to_identity_roundtrip_anchor() {
        // An untouched &mut synthesizes to BorrowedInput, which binds to the
        // POLYMORPHIC identity round-trip law (holds for any place type).
        let cert = certifying_anchor(&GiveBackExpr::BorrowedInput)
            .expect("identity give-back must bind to the round-trip law");
        assert_eq!(cert.anchor, KERNEL_ANCHOR_GIVEBACK_REFINEMENT);
        assert_eq!(cert.theorems, vec!["RustSem.GiveBack.backIdP_roundTrips"]);
    }

    #[test]
    fn untouched_mut_of_a_struct_now_certifies() {
        // GENERALITY: an untouched `&mut (i32, i32)` (a non-scalar place) synthesizes
        // to BorrowedInput and — thanks to the polymorphic backIdP — now yields a
        // recheck directive, where the Nat-only backId would have been refused by the
        // pointee guard.
        let entry = bid(0);
        let pair = Ty::Tuple(vec![Ty::I32, Ty::I32]);
        let mut func = Function::new(
            FuncId::new(19),
            "untouched",
            trust_ir::FuncTyId::new(0),
            entry,
        );
        let mut block = Block::new(entry);
        block
            .params
            .push((v(0), Ty::RefMut(Box::new(pair.clone()))));
        block
            .body
            .push(InstrNode::new(Inst::BorrowMut { ptr: v(0) }).with_result(v(1)));
        // load but do NOT store (untouched)
        block.body.push(
            InstrNode::new(Inst::Load {
                ty: pair,
                ptr: v(1),
                volatile: false,
                align: None,
            })
            .with_result(v(2)),
        );
        block
            .body
            .push(InstrNode::new(Inst::EndBorrow { borrow_ptr: v(1) }));
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        func.blocks.push(block);

        let view = match elaborate_give_back(&func) {
            GiveBackOutcome::Accepted(v) => v,
            other => panic!("expected Accepted, got {other:?}"),
        };
        assert_eq!(view.backward.value_expr, GiveBackExpr::BorrowedInput);
        assert!(
            give_back_recheck_directive(&view).is_some(),
            "an untouched &mut of a struct must certify via the polymorphic backIdP"
        );
    }

    #[test]
    fn uncertified_shapes_fail_closed_to_none() {
        // Fail-closed: shapes with no proven law return None (stay Pending) —
        // never spuriously certified. (`x_in + k` for k ≥ 1 IS now certified by the
        // parameterized addKBack_step, so use genuinely-unmodelled shapes here.)
        // x_in * 2: multiplication is not a modelled give-back.
        let times_two = GiveBackExpr::BinOp(
            BinOp::Mul,
            Box::new(GiveBackExpr::BorrowedInput),
            Box::new(GiveBackExpr::Const(2)),
        );
        assert!(
            certifying_anchor(&times_two).is_none(),
            "x_in * 2 must not be certified (no multiplication give-back law)"
        );
        // x_in + 0: below the k ≥ 1 increment threshold (a no-op, not a real increment).
        let plus_zero = GiveBackExpr::BinOp(
            BinOp::Add,
            Box::new(GiveBackExpr::BorrowedInput),
            Box::new(GiveBackExpr::Const(0)),
        );
        assert!(
            certifying_anchor(&plus_zero).is_none(),
            "x_in + 0 is not covered"
        );
        // An opaque input: synthesis bottomed out, nothing to certify.
        assert!(certifying_anchor(&GiveBackExpr::Opaque(v(9))).is_none());
        // A bare constant give-back: not modelled.
        assert!(certifying_anchor(&GiveBackExpr::Const(7)).is_none());
    }

    #[test]
    fn two_mut_regions_are_declined() {
        let entry = bid(0);
        let mut func = Function::new(FuncId::new(1), "two_mut", trust_ir::FuncTyId::new(0), entry);
        let mut block = Block::new(entry);
        block.params.push((v(0), Ty::RefMut(Box::new(Ty::I32))));
        block.params.push((v(1), Ty::RefMut(Box::new(Ty::I32))));
        block
            .body
            .push(InstrNode::new(Inst::BorrowMut { ptr: v(0) }).with_result(v(2)));
        block
            .body
            .push(InstrNode::new(Inst::BorrowMut { ptr: v(1) }).with_result(v(3)));
        block
            .body
            .push(InstrNode::new(Inst::EndBorrow { borrow_ptr: v(2) }));
        block
            .body
            .push(InstrNode::new(Inst::EndBorrow { borrow_ptr: v(3) }));
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        func.blocks.push(block);

        assert_eq!(
            elaborate_give_back(&func),
            GiveBackOutcome::Declined(DeclineReason::MultipleMutRegions(2))
        );
    }

    #[test]
    fn raw_pointer_param_is_declined() {
        let entry = bid(0);
        let mut func = Function::new(FuncId::new(2), "raw_ptr", trust_ir::FuncTyId::new(0), entry);
        let mut block = Block::new(entry);
        // param v0 : *mut i32  -> outside the safe-sequential-&mut fragment
        block.params.push((v(0), Ty::PtrMut(Box::new(Ty::I32))));
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        func.blocks.push(block);

        assert_eq!(
            elaborate_give_back(&func),
            GiveBackOutcome::Declined(DeclineReason::RawPointerOrRc("PtrMut"))
        );
    }

    #[test]
    fn loop_back_edge_is_declined() {
        // block0 -> block1 (forward), block1 -> block0 (BACK-EDGE).
        let entry = bid(0);
        let mut func = Function::new(FuncId::new(3), "loopy", trust_ir::FuncTyId::new(0), entry);

        let mut b0 = Block::new(bid(0));
        b0.params.push((v(0), Ty::RefMut(Box::new(Ty::I32))));
        b0.body
            .push(InstrNode::new(Inst::BorrowMut { ptr: v(0) }).with_result(v(1)));
        b0.body.push(InstrNode::new(Inst::Br {
            target: bid(1),
            args: vec![],
        }));

        let mut b1 = Block::new(bid(1));
        // Back-edge to the entry block.
        b1.body.push(InstrNode::new(Inst::Br {
            target: bid(0),
            args: vec![],
        }));

        func.blocks.push(b0);
        func.blocks.push(b1);

        assert_eq!(
            elaborate_give_back(&func),
            GiveBackOutcome::Declined(DeclineReason::LoopOrBackEdge)
        );
    }

    #[test]
    fn has_back_edge_sees_switch_and_invoke_back_edges() {
        // Amendment D §1.3: the probe reads every edge from the exhaustive
        // accessor. It once listed only `Br` / `CondBr`, so a back edge on a
        // `Switch` arm or an invoke's normal edge read as loop-free. (The M1
        // whitelist declines both instructions before this probe runs, so
        // the probe itself is pinned here.)
        let switch_back = |back_on_default: bool| {
            let mut func = Function::new(FuncId::new(4), "sw", trust_ir::FuncTyId::new(0), bid(0));
            let mut b0 = Block::new(bid(0));
            b0.body.push(InstrNode::new(Inst::Br {
                target: bid(1),
                args: vec![],
            }));
            let mut b1 = Block::new(bid(1));
            b1.params.push((v(0), Ty::I32));
            let (default, case) = if back_on_default {
                (bid(0), bid(2))
            } else {
                (bid(2), bid(0))
            };
            b1.body.push(InstrNode::new(Inst::Switch {
                value: v(0),
                default,
                default_args: vec![],
                cases: vec![trust_ir::SwitchCase {
                    value: Constant::Int(0),
                    target: case,
                    args: vec![],
                }],
                exhaustive_enum_unreachable: false,
            }));
            let mut b2 = Block::new(bid(2));
            b2.body
                .push(InstrNode::new(Inst::Return { values: vec![] }));
            func.blocks.extend([b0, b1, b2]);
            func
        };
        assert!(
            has_back_edge(&switch_back(true)),
            "switch default back edge"
        );
        assert!(has_back_edge(&switch_back(false)), "switch case back edge");

        let mut func = Function::new(FuncId::new(5), "inv", trust_ir::FuncTyId::new(0), bid(0));
        let mut b0 = Block::new(bid(0));
        b0.body.push(InstrNode::new(Inst::Br {
            target: bid(1),
            args: vec![],
        }));
        let mut b1 = Block::new(bid(1));
        b1.body.push(InstrNode::new(Inst::Invoke {
            callee: FuncId::new(5),
            args: vec![],
            normal_dest: bid(0),
            normal_args: vec![],
            unwind_dest: bid(2),
        }));
        let mut b2 = Block::new(bid(2));
        b2.body.push(InstrNode::new(Inst::Unreachable));
        func.blocks.extend([b0, b1, b2]);
        assert!(has_back_edge(&func), "invoke normal-edge back edge");
    }

    /// `fn f(x: &mut i32, c: bool) { if c { *x += 1 } }` — the canonical conditional
    /// mutation diamond (entry `CondBr` → mutate block → join).
    fn cond_incr_function() -> Function {
        let entry = bid(0);
        let mut func = Function::new(FuncId::new(7), "cond", trust_ir::FuncTyId::new(0), entry);

        let mut b0 = Block::new(bid(0));
        b0.params.push((v(0), Ty::RefMut(Box::new(Ty::I32))));
        b0.params.push((v(9), Ty::Bool)); // the runtime flag `c`
        b0.body
            .push(InstrNode::new(Inst::BorrowMut { ptr: v(0) }).with_result(v(1)));
        // Branch on the flag to the mutate block (then) or straight to the join (else).
        b0.body.push(InstrNode::new(Inst::CondBr {
            cond: v(9),
            then_target: bid(1),
            then_args: vec![],
            else_target: bid(2),
            else_args: vec![],
        }));

        // then: *x += 1
        let mut b1 = Block::new(bid(1));
        b1.body.push(
            InstrNode::new(Inst::Load {
                ty: Ty::I32,
                ptr: v(1),
                volatile: false,
                align: None,
            })
            .with_result(v(3)),
        );
        b1.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(1),
            })
            .with_result(v(4)),
        );
        b1.body.push(
            InstrNode::new(Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I32,
                lhs: v(3),
                rhs: v(4),
            })
            .with_result(v(5)),
        );
        b1.body.push(InstrNode::new(Inst::Store {
            ty: Ty::I32,
            ptr: v(1),
            value: v(5),
            volatile: false,
            align: None,
        }));
        b1.body.push(InstrNode::new(Inst::Br {
            target: bid(2),
            args: vec![],
        }));

        // join: end borrow + return
        let mut b2 = Block::new(bid(2));
        b2.body
            .push(InstrNode::new(Inst::EndBorrow { borrow_ptr: v(1) }));
        b2.body
            .push(InstrNode::new(Inst::Return { values: vec![] }));

        func.blocks.push(b0);
        func.blocks.push(b1);
        func.blocks.push(b2);
        func
    }

    #[test]
    fn conditional_diamond_is_accepted_with_path_sensitive_giveback() {
        // T-cond: a forward conditional-mutation diamond is ACCEPTED and synthesized
        // PATH-SENSITIVELY. The give-back is `x_in + 1` on the taken branch and
        // `x_in` (frame) on the untaken branch — NEVER `x_in + 1` on both (the
        // path-INSENSITIVE unsoundness the old straight-line gate guarded against; it
        // is now structurally impossible because each path is synthesized separately).
        let func = cond_incr_function();
        let view = match elaborate_give_back(&func) {
            GiveBackOutcome::Accepted(v) => v,
            other => panic!("the conditional diamond must be accepted, got {other:?}"),
        };
        let expected = GiveBackExpr::Cond {
            cond: Box::new(GiveBackExpr::Opaque(v(9))),
            then_val: Box::new(GiveBackExpr::BinOp(
                BinOp::Add,
                Box::new(GiveBackExpr::BorrowedInput),
                Box::new(GiveBackExpr::Const(1)),
            )),
            else_val: Box::new(GiveBackExpr::BorrowedInput),
        };
        assert_eq!(
            view.backward.value_expr, expected,
            "the give-back must be path-sensitive: x_in+1 on the taken branch, x_in (frame) otherwise"
        );

        // It binds to the control-flow anchor's case laws (no hand-written citation).
        let cert = certifying_anchor(&view.backward.value_expr)
            .expect("the conditional incr must bind to the cond anchor");
        assert_eq!(cert.anchor, KERNEL_ANCHOR_GIVEBACK_COND);
        assert!(cert.theorems.contains(&"RustSem.GiveBack.condSetP_true"));
        assert!(cert.theorems.contains(&"RustSem.GiveBack.condSetP_false"));
        assert!(
            give_back_recheck_directive(&view).is_none(),
            "the conditional contains fixed-width arithmetic and must stay Pending"
        );
    }

    #[test]
    fn both_branches_mutate_conditional_stays_pending() {
        // COVERAGE: `if c { *x += 1 } else { *x += 2 }` — BOTH branches mutate (neither
        // frames). Give-back = Cond(c, x_in+1, x_in+2), certified by condSetP (the case
        // laws hold whatever the two branch values are).
        let entry = bid(0);
        let mut func = Function::new(FuncId::new(21), "both", trust_ir::FuncTyId::new(0), entry);
        let mut b0 = Block::new(bid(0));
        b0.params.push((v(0), Ty::RefMut(Box::new(Ty::I32))));
        b0.params.push((v(9), Ty::Bool));
        b0.body
            .push(InstrNode::new(Inst::BorrowMut { ptr: v(0) }).with_result(v(1)));
        b0.body.push(InstrNode::new(Inst::CondBr {
            cond: v(9),
            then_target: bid(1),
            then_args: vec![],
            else_target: bid(2),
            else_args: vec![],
        }));
        // then: *x += 1
        let mut b1 = Block::new(bid(1));
        b1.body.push(
            InstrNode::new(Inst::Load {
                ty: Ty::I32,
                ptr: v(1),
                volatile: false,
                align: None,
            })
            .with_result(v(2)),
        );
        b1.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(1),
            })
            .with_result(v(3)),
        );
        b1.body.push(
            InstrNode::new(Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I32,
                lhs: v(2),
                rhs: v(3),
            })
            .with_result(v(7)),
        );
        b1.body.push(InstrNode::new(Inst::Store {
            ty: Ty::I32,
            ptr: v(1),
            value: v(7),
            volatile: false,
            align: None,
        }));
        b1.body.push(InstrNode::new(Inst::Br {
            target: bid(3),
            args: vec![],
        }));
        // else: *x += 2
        let mut b2 = Block::new(bid(2));
        b2.body.push(
            InstrNode::new(Inst::Load {
                ty: Ty::I32,
                ptr: v(1),
                volatile: false,
                align: None,
            })
            .with_result(v(4)),
        );
        b2.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(2),
            })
            .with_result(v(5)),
        );
        b2.body.push(
            InstrNode::new(Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I32,
                lhs: v(4),
                rhs: v(5),
            })
            .with_result(v(6)),
        );
        b2.body.push(InstrNode::new(Inst::Store {
            ty: Ty::I32,
            ptr: v(1),
            value: v(6),
            volatile: false,
            align: None,
        }));
        b2.body.push(InstrNode::new(Inst::Br {
            target: bid(3),
            args: vec![],
        }));
        // join
        let mut b3 = Block::new(bid(3));
        b3.body
            .push(InstrNode::new(Inst::EndBorrow { borrow_ptr: v(1) }));
        b3.body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        func.blocks.push(b0);
        func.blocks.push(b1);
        func.blocks.push(b2);
        func.blocks.push(b3);

        let view = match elaborate_give_back(&func) {
            GiveBackOutcome::Accepted(v) => v,
            other => panic!("both-branches conditional must be accepted, got {other:?}"),
        };
        let expected = GiveBackExpr::Cond {
            cond: Box::new(GiveBackExpr::Opaque(v(9))),
            then_val: Box::new(GiveBackExpr::BinOp(
                BinOp::Add,
                Box::new(GiveBackExpr::BorrowedInput),
                Box::new(GiveBackExpr::Const(1)),
            )),
            else_val: Box::new(GiveBackExpr::BinOp(
                BinOp::Add,
                Box::new(GiveBackExpr::BorrowedInput),
                Box::new(GiveBackExpr::Const(2)),
            )),
        };
        assert_eq!(view.backward.value_expr, expected);
        assert!(
            give_back_recheck_directive(&view).is_none(),
            "both wrapping arithmetic branches must remain non-authoritative"
        );
    }

    #[test]
    fn non_diamond_control_flow_is_declined() {
        // Fail-closed: a conditional whose branches DON'T reconverge to a single join
        // (here each branch returns independently) is NOT a recognized diamond, so the
        // elaborator declines it rather than guessing a give-back. Preserves the H2
        // guarantee for every control-flow shape outside the accepted diamond.
        let entry = bid(0);
        let mut func = Function::new(FuncId::new(8), "fork", trust_ir::FuncTyId::new(0), entry);
        let mut b0 = Block::new(bid(0));
        b0.params.push((v(0), Ty::RefMut(Box::new(Ty::I32))));
        b0.params.push((v(9), Ty::Bool));
        b0.body
            .push(InstrNode::new(Inst::BorrowMut { ptr: v(0) }).with_result(v(1)));
        b0.body.push(InstrNode::new(Inst::CondBr {
            cond: v(9),
            then_target: bid(1),
            then_args: vec![],
            else_target: bid(2),
            else_args: vec![],
        }));
        // Two branches that each END (Return) — no common join block.
        let mut b1 = Block::new(bid(1));
        b1.body
            .push(InstrNode::new(Inst::EndBorrow { borrow_ptr: v(1) }));
        b1.body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        let mut b2 = Block::new(bid(2));
        b2.body
            .push(InstrNode::new(Inst::EndBorrow { borrow_ptr: v(1) }));
        b2.body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        func.blocks.push(b0);
        func.blocks.push(b1);
        func.blocks.push(b2);

        assert_eq!(
            elaborate_give_back(&func),
            GiveBackOutcome::Declined(DeclineReason::ConditionalControlFlow),
            "a non-diamond conditional (no common join) must be declined fail-closed"
        );
    }

    #[test]
    fn chain_cfg_is_not_misrecognized_as_a_diamond() {
        // SOUNDNESS regression: a CHAIN `entry CondBr → then → els → join`, `els → join`
        // (where `then` jumps INTO `els`, which itself continues) must NOT be mistaken
        // for an empty-else diamond with `els` as the join — that would make the
        // synthesizer miss `join`'s body. The terminal-join check rejects it (the
        // candidate "join" `els` ends in `Br`, not `Return`), so it fails closed.
        let entry = bid(0);
        let mut func = Function::new(FuncId::new(14), "chain", trust_ir::FuncTyId::new(0), entry);
        let mut b0 = Block::new(bid(0));
        b0.params.push((v(0), Ty::RefMut(Box::new(Ty::I32))));
        b0.params.push((v(9), Ty::Bool));
        b0.body
            .push(InstrNode::new(Inst::BorrowMut { ptr: v(0) }).with_result(v(1)));
        b0.body.push(InstrNode::new(Inst::CondBr {
            cond: v(9),
            then_target: bid(1),
            then_args: vec![],
            else_target: bid(2),
            else_args: vec![],
        }));
        // then(1): jumps INTO the else block (the chain).
        let mut b1 = Block::new(bid(1));
        b1.body.push(InstrNode::new(Inst::Br {
            target: bid(2),
            args: vec![],
        }));
        // els(2): a real block that continues to the join (NOT terminal).
        let mut b2 = Block::new(bid(2));
        b2.body.push(InstrNode::new(Inst::Br {
            target: bid(3),
            args: vec![],
        }));
        // join(3): the true reconvergence (endborrow + return).
        let mut b3 = Block::new(bid(3));
        b3.body
            .push(InstrNode::new(Inst::EndBorrow { borrow_ptr: v(1) }));
        b3.body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        func.blocks.push(b0);
        func.blocks.push(b1);
        func.blocks.push(b2);
        func.blocks.push(b3);

        assert_eq!(
            elaborate_give_back(&func),
            GiveBackOutcome::Declined(DeclineReason::ConditionalControlFlow),
            "a chain CFG must NOT be misrecognized as a diamond (terminal-join check)"
        );
    }

    /// `fn f(p: &mut (i32,i32), c: bool) { if c { p.0 += 1 } }` — the COMPOSITION of a
    /// conditional diamond (T-cond) with an aggregate field update (H3).
    fn cond_aggregate_function() -> Function {
        let entry = bid(0);
        let pair = Ty::Tuple(vec![Ty::I32, Ty::I32]);
        let mut func = Function::new(
            FuncId::new(16),
            "cond_agg",
            trust_ir::FuncTyId::new(0),
            entry,
        );
        let mut b0 = Block::new(bid(0));
        b0.params.push((v(0), Ty::RefMut(Box::new(pair.clone()))));
        b0.params.push((v(9), Ty::Bool));
        b0.body
            .push(InstrNode::new(Inst::BorrowMut { ptr: v(0) }).with_result(v(1)));
        b0.body.push(InstrNode::new(Inst::CondBr {
            cond: v(9),
            then_target: bid(1),
            then_args: vec![],
            else_target: bid(2),
            else_args: vec![],
        }));
        // then: p.0 += 1
        let mut b1 = Block::new(bid(1));
        b1.body.push(
            InstrNode::new(Inst::Load {
                ty: pair.clone(),
                ptr: v(1),
                volatile: false,
                align: None,
            })
            .with_result(v(2)),
        );
        b1.body.push(
            InstrNode::new(Inst::ExtractField {
                ty: Ty::I32,
                aggregate: v(2),
                field: 0,
            })
            .with_result(v(3)),
        );
        b1.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(1),
            })
            .with_result(v(4)),
        );
        b1.body.push(
            InstrNode::new(Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I32,
                lhs: v(3),
                rhs: v(4),
            })
            .with_result(v(5)),
        );
        b1.body.push(
            InstrNode::new(Inst::InsertField {
                ty: pair.clone(),
                aggregate: v(2),
                field: 0,
                value: v(5),
            })
            .with_result(v(6)),
        );
        b1.body.push(InstrNode::new(Inst::Store {
            ty: pair,
            ptr: v(1),
            value: v(6),
            volatile: false,
            align: None,
        }));
        b1.body.push(InstrNode::new(Inst::Br {
            target: bid(2),
            args: vec![],
        }));
        // join
        let mut b2 = Block::new(bid(2));
        b2.body
            .push(InstrNode::new(Inst::EndBorrow { borrow_ptr: v(1) }));
        b2.body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        func.blocks.push(b0);
        func.blocks.push(b1);
        func.blocks.push(b2);
        func
    }

    #[test]
    fn conditional_aggregate_composes_and_binds_to_pair_cond_laws() {
        // COMPOSITION: `if c { p.0 += 1 }` synthesizes to a Cond whose taken branch is
        // the AGGREGATE give-back and whose untaken branch frames — and binds to the
        // Prod-typed conditional case laws (T-cond ∘ H3, one directive).
        let func = cond_aggregate_function();
        let view = match elaborate_give_back(&func) {
            GiveBackOutcome::Accepted(v) => v,
            other => panic!("conditional aggregate must be accepted, got {other:?}"),
        };
        let agg = GiveBackExpr::WithField {
            base: Box::new(GiveBackExpr::BorrowedInput),
            field: 0,
            value: Box::new(GiveBackExpr::BinOp(
                BinOp::Add,
                Box::new(GiveBackExpr::Field(
                    Box::new(GiveBackExpr::BorrowedInput),
                    0,
                )),
                Box::new(GiveBackExpr::Const(1)),
            )),
        };
        let expected = GiveBackExpr::Cond {
            cond: Box::new(GiveBackExpr::Opaque(v(9))),
            then_val: Box::new(agg),
            else_val: Box::new(GiveBackExpr::BorrowedInput),
        };
        assert_eq!(
            view.backward.value_expr, expected,
            "if c {{ p.0 += 1 }} must synthesize to Cond(c, aggregate-incr, frame)"
        );

        let cert = certifying_anchor(&view.backward.value_expr)
            .expect("conditional aggregate must bind to the Prod-typed cond laws");
        assert_eq!(cert.anchor, KERNEL_ANCHOR_GIVEBACK_COND);
        assert!(cert.theorems.contains(&"RustSem.GiveBack.condSetP_true"));
        assert!(cert.theorems.contains(&"RustSem.GiveBack.condSetP_false"));
    }

    /// `fn incr_opt(o: &mut Option<u32>) { match o { Some(x) => *x += 1, None => () } }`
    /// — at the IR level `Option<u32>` is a tagged 2-tuple `{tag: i32, payload: u32}`,
    /// the match is a diamond on `icmp(tag, 1)`, and the taken branch increments the
    /// PAYLOAD (field 1). So the enum give-back is a conditional-aggregate on field 1:
    /// `Cond(tag==1, WithField(x_in, 1, x_in.1 + 1), x_in)`.
    fn enum_option_incr_function() -> Function {
        let entry = bid(0);
        // tagged Option<u32> = (tag: i32, payload: u32)
        let opt = Ty::Tuple(vec![Ty::I32, Ty::U32]);
        let mut func = Function::new(
            FuncId::new(18),
            "incr_opt",
            trust_ir::FuncTyId::new(0),
            entry,
        );
        let mut b0 = Block::new(bid(0));
        b0.params.push((v(0), Ty::RefMut(Box::new(opt.clone()))));
        b0.body
            .push(InstrNode::new(Inst::BorrowMut { ptr: v(0) }).with_result(v(1)));
        b0.body.push(
            InstrNode::new(Inst::Load {
                ty: opt.clone(),
                ptr: v(1),
                volatile: false,
                align: None,
            })
            .with_result(v(2)),
        );
        // read discriminant (tag = field 0) and test == 1 (the Some tag)
        b0.body.push(
            InstrNode::new(Inst::ExtractField {
                ty: Ty::I32,
                aggregate: v(2),
                field: 0,
            })
            .with_result(v(3)),
        );
        b0.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(1),
            })
            .with_result(v(4)),
        );
        b0.body.push(
            InstrNode::new(Inst::ICmp {
                op: trust_ir::ICmpOp::Eq,
                ty: Ty::I32,
                lhs: v(3),
                rhs: v(4),
            })
            .with_result(v(5)),
        );
        b0.body.push(InstrNode::new(Inst::CondBr {
            cond: v(5),
            then_target: bid(1),
            then_args: vec![],
            else_target: bid(2),
            else_args: vec![],
        }));
        // Some branch: payload (field 1) += 1
        let mut b1 = Block::new(bid(1));
        b1.body.push(
            InstrNode::new(Inst::ExtractField {
                ty: Ty::U32,
                aggregate: v(2),
                field: 1,
            })
            .with_result(v(6)),
        );
        b1.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::U32,
                value: Constant::Int(1),
            })
            .with_result(v(7)),
        );
        b1.body.push(
            InstrNode::new(Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::U32,
                lhs: v(6),
                rhs: v(7),
            })
            .with_result(v(8)),
        );
        b1.body.push(
            InstrNode::new(Inst::InsertField {
                ty: opt.clone(),
                aggregate: v(2),
                field: 1,
                value: v(8),
            })
            .with_result(v(9)),
        );
        b1.body.push(InstrNode::new(Inst::Store {
            ty: opt,
            ptr: v(1),
            value: v(9),
            volatile: false,
            align: None,
        }));
        b1.body.push(InstrNode::new(Inst::Br {
            target: bid(2),
            args: vec![],
        }));
        // join
        let mut b2 = Block::new(bid(2));
        b2.body
            .push(InstrNode::new(Inst::EndBorrow { borrow_ptr: v(1) }));
        b2.body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        func.blocks.push(b0);
        func.blocks.push(b1);
        func.blocks.push(b2);
        func
    }

    #[test]
    fn enum_option_incr_maps_to_conditional_laws_but_stays_pending() {
        // ENUM give-back at the tagged-struct IR level: the Option-match diamond
        // synthesizes to a conditional PAYLOAD (field-1) update over the tagged pair,
        // and binds to the field-agnostic Prod-typed cond laws. A real `&mut Option`
        // function reaches a recheck directive.
        let func = enum_option_incr_function();
        let view = match elaborate_give_back(&func) {
            GiveBackOutcome::Accepted(v) => v,
            other => panic!("the Option-match diamond must be accepted, got {other:?}"),
        };
        let payload_incr = GiveBackExpr::WithField {
            base: Box::new(GiveBackExpr::BorrowedInput),
            field: 1,
            value: Box::new(GiveBackExpr::BinOp(
                BinOp::Add,
                Box::new(GiveBackExpr::Field(
                    Box::new(GiveBackExpr::BorrowedInput),
                    1,
                )),
                Box::new(GiveBackExpr::Const(1)),
            )),
        };
        let expected = GiveBackExpr::Cond {
            cond: Box::new(GiveBackExpr::Opaque(v(5))),
            then_val: Box::new(payload_incr),
            else_val: Box::new(GiveBackExpr::BorrowedInput),
        };
        assert_eq!(
            view.backward.value_expr, expected,
            "Option-match must synthesize to Cond(tag==1, payload+1, frame)"
        );

        let cert = certifying_anchor(&view.backward.value_expr)
            .expect("the tagged-Option give-back must bind to the Prod-typed cond laws");
        assert_eq!(cert.anchor, KERNEL_ANCHOR_GIVEBACK_COND);
        assert!(cert.theorems.contains(&"RustSem.GiveBack.condSetP_true"));
        assert!(
            give_back_recheck_directive(&view).is_none(),
            "the tagged payload uses fixed-width addition and must stay Pending"
        );
    }

    #[test]
    fn nested_mutable_borrow_is_declined() {
        // v1 = borrow_mut v0 ; v2 = borrow_mut v1  (borrowing a borrow handle).
        let entry = bid(0);
        let mut func = Function::new(FuncId::new(5), "nested", trust_ir::FuncTyId::new(0), entry);
        let mut block = Block::new(entry);
        block.params.push((v(0), Ty::RefMut(Box::new(Ty::I32))));
        block
            .body
            .push(InstrNode::new(Inst::BorrowMut { ptr: v(0) }).with_result(v(1)));
        block
            .body
            .push(InstrNode::new(Inst::BorrowMut { ptr: v(1) }).with_result(v(2)));
        block
            .body
            .push(InstrNode::new(Inst::EndBorrow { borrow_ptr: v(2) }));
        block
            .body
            .push(InstrNode::new(Inst::EndBorrow { borrow_ptr: v(1) }));
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        func.blocks.push(block);

        // Two BorrowMut would also trip MultipleMutRegions, but the nested check
        // runs first and is the more specific (and correct) reason here.
        assert_eq!(
            elaborate_give_back(&func),
            GiveBackOutcome::Declined(DeclineReason::NestedMutableBorrow)
        );
    }

    #[test]
    fn unsupported_instruction_is_declined() {
        // A `Call` is deliberately not on the whitelist.
        let entry = bid(0);
        let mut func = Function::new(FuncId::new(6), "calls", trust_ir::FuncTyId::new(0), entry);
        let mut block = Block::new(entry);
        block.params.push((v(0), Ty::RefMut(Box::new(Ty::I32))));
        block.body.push(InstrNode::new(Inst::Call {
            callee: FuncId::new(99),
            args: vec![],
        }));
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        func.blocks.push(block);

        assert_eq!(
            elaborate_give_back(&func),
            GiveBackOutcome::Declined(DeclineReason::UnsupportedInstruction("Call"))
        );
    }

    #[test]
    fn empty_no_mut_function_is_declined_conservatively() {
        // A trivial function with no &mut region: documented conservative choice
        // is to DECLINE (nothing to certify), NOT accept-with-no-obligation.
        let entry = bid(0);
        let mut func = Function::new(FuncId::new(4), "trivial", trust_ir::FuncTyId::new(0), entry);
        let mut block = Block::new(entry);
        block.params.push((v(0), Ty::I32));
        block.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(0),
            })
            .with_result(v(1)),
        );
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![v(1)] }));
        func.blocks.push(block);

        assert_eq!(
            elaborate_give_back(&func),
            GiveBackOutcome::Declined(DeclineReason::NoMutableBorrow)
        );
    }

    #[test]
    fn body_less_declaration_is_declined() {
        let func = Function::new(FuncId::new(8), "decl", trust_ir::FuncTyId::new(0), bid(0));
        assert_eq!(
            elaborate_give_back(&func),
            GiveBackOutcome::Declined(DeclineReason::NoBody)
        );
    }

    // -----------------------------------------------------------------
    // General SeqMap loop (SeqMapGen): module-threaded recursive element
    // certification (designs/2026-06-30-general-seqmap-instruction.md §3).
    // -----------------------------------------------------------------

    /// The single-&mut element function `incr_elem(x: &mut i32) { *x += 1 }`.
    fn incr_elem_function(fid: u32) -> Function {
        let entry = bid(0);
        let mut func = Function::new(
            FuncId::new(fid),
            "incr_elem",
            trust_ir::FuncTyId::new(1),
            entry,
        );
        let mut block = Block::new(entry);
        block.params.push((v(0), Ty::RefMut(Box::new(Ty::I32))));
        block
            .body
            .push(InstrNode::new(Inst::BorrowMut { ptr: v(0) }).with_result(v(1)));
        block.body.push(
            InstrNode::new(Inst::Load {
                ty: Ty::I32,
                ptr: v(1),
                volatile: false,
                align: None,
            })
            .with_result(v(2)),
        );
        block.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(1),
            })
            .with_result(v(3)),
        );
        block.body.push(
            InstrNode::new(Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I32,
                lhs: v(2),
                rhs: v(3),
            })
            .with_result(v(4)),
        );
        block.body.push(InstrNode::new(Inst::Store {
            ty: Ty::I32,
            ptr: v(1),
            value: v(4),
            volatile: false,
            align: None,
        }));
        block
            .body
            .push(InstrNode::new(Inst::EndBorrow { borrow_ptr: v(1) }));
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        func.blocks.push(block);
        func
    }

    /// The loop `incr_all(l: &mut Seq<i32>) { for x in &mut l { *x = fwd(x) } }`
    /// lowered with the GENERAL `Inst::SeqMap { fwd }`.
    fn seq_map_gen_loop_function(fid: u32, fwd: u32, elem_tyid: u32) -> Function {
        let entry = bid(0);
        let seq_ty = Ty::Sequence(trust_ir::TyId::new(elem_tyid));
        let mut func = Function::new(
            FuncId::new(fid),
            "incr_all",
            trust_ir::FuncTyId::new(0),
            entry,
        );
        let mut block = Block::new(entry);
        block
            .params
            .push((v(0), Ty::RefMut(Box::new(seq_ty.clone()))));
        block
            .body
            .push(InstrNode::new(Inst::BorrowMut { ptr: v(0) }).with_result(v(1)));
        block.body.push(
            InstrNode::new(Inst::Load {
                ty: seq_ty.clone(),
                ptr: v(1),
                volatile: false,
                align: None,
            })
            .with_result(v(2)),
        );
        block.body.push(
            InstrNode::new(Inst::SeqMap {
                ty: seq_ty.clone(),
                seq: v(2),
                fwd: FuncId::new(fwd),
            })
            .with_result(v(3)),
        );
        block.body.push(InstrNode::new(Inst::Store {
            ty: seq_ty,
            ptr: v(1),
            value: v(3),
            volatile: false,
            align: None,
        }));
        block
            .body
            .push(InstrNode::new(Inst::EndBorrow { borrow_ptr: v(1) }));
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        func.blocks.push(block);
        func
    }

    /// Module carrying the loop + element functions, the interned i32 element
    /// type, and both signatures — everything the module-threaded elaboration
    /// and the pointee guard resolve.
    fn seq_map_gen_module() -> Module {
        let mut m = Module::new("seq-map-gen");
        let i32_id = m.add_type(Ty::I32).expect("Module::add_type: test fixture");
        assert_eq!(i32_id.index(), 0);
        let seq_ty = Ty::Sequence(i32_id);
        let loop_ft = m
            .add_func_type(trust_ir::FuncTy {
                params: vec![Ty::RefMut(Box::new(seq_ty))],
                returns: vec![],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        assert_eq!(loop_ft.index(), 0);
        let elem_ft = m
            .add_func_type(trust_ir::FuncTy {
                params: vec![Ty::RefMut(Box::new(Ty::I32))],
                returns: vec![],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        assert_eq!(elem_ft.index(), 1);
        m.functions.push(seq_map_gen_loop_function(30, 31, 0));
        m.functions.push(incr_elem_function(31));
        m
    }

    #[test]
    fn seq_map_gen_synthesizes_but_arithmetic_element_stays_non_authoritative() {
        let m = seq_map_gen_module();
        let loop_fn = &m.functions[0];
        let view = match elaborate_give_back_in(loop_fn, &m) {
            GiveBackOutcome::Accepted(view) => view,
            other => panic!("the general SeqMap loop must be accepted, got {other:?}"),
        };
        // Synthesis: the borrowed sequence ends holding map fwd (x_in).
        assert_eq!(
            view.backward.value_expr,
            GiveBackExpr::SeqMapGen {
                fwd: FuncId::new(31),
                inner: Box::new(GiveBackExpr::BorrowedInput),
            }
        );
        assert!(
            certifying_anchor_in(&view.backward.value_expr, &m).is_none(),
            "a Nat list law plus a Nat element law is not authority for fixed-width Seq<i32>"
        );
        assert!(
            give_back_recheck_directive_in(&view, &m).is_none(),
            "the arithmetic element operation must remain Pending"
        );
    }

    #[test]
    fn seq_map_gen_without_module_context_declines_fail_closed() {
        // The legacy module-less shim cannot resolve fwd: fail-closed decline,
        // never a silent Accept.
        let loop_fn = seq_map_gen_loop_function(30, 31, 0);
        match elaborate_give_back(&loop_fn) {
            GiveBackOutcome::Declined(DeclineReason::SeqMapFwdOutsideFragment(_)) => {}
            other => panic!("module-less SeqMap must decline fail-closed, got {other:?}"),
        }
    }

    #[test]
    fn seq_map_gen_missing_fwd_declines_fail_closed() {
        let mut m = seq_map_gen_module();
        m.functions.remove(1); // drop the element function
        let loop_fn = m.functions[0].clone();
        match elaborate_give_back_in(&loop_fn, &m) {
            GiveBackOutcome::Declined(DeclineReason::SeqMapFwdOutsideFragment(_)) => {}
            other => panic!("missing element function must decline, got {other:?}"),
        }
    }

    #[test]
    fn seq_map_gen_nested_seq_map_fwd_declines_strict_descent() {
        // TERMINATION guard: an element function that itself contains a SeqMap
        // (here: pointing back at the loop — a would-be recursion cycle) declines.
        let mut m = seq_map_gen_module();
        // Replace the element function with one containing a SeqMap.
        m.functions[1] = seq_map_gen_loop_function(31, 30, 0);
        let loop_fn = m.functions[0].clone();
        match elaborate_give_back_in(&loop_fn, &m) {
            GiveBackOutcome::Declined(DeclineReason::SeqMapFwdOutsideFragment(_)) => {}
            other => panic!("nested SeqMap element fn must decline, got {other:?}"),
        }

        // Defense in depth: even a manually supplied view that bypassed the
        // elaboration whitelist must not recurse forever through A → B → A.
        let expr = GiveBackExpr::SeqMapGen {
            fwd: FuncId::new(31),
            inner: Box::new(GiveBackExpr::BorrowedInput),
        };
        let mut walk = ArithmeticWalk {
            visiting_functions: HashSet::from([FuncId::new(31)]),
            remaining_nodes: ARITHMETIC_WALK_MAX_NODES,
        };
        assert!(
            uses_fixed_width_arithmetic_inner(&expr, &m, 0, &mut walk),
            "a recursive FuncId edge must be authority-blocked"
        );
    }

    #[test]
    fn arithmetic_authority_walk_fails_closed_on_depth_exhaustion() {
        let mut expr = GiveBackExpr::BorrowedInput;
        for _ in 0..=ARITHMETIC_WALK_MAX_DEPTH {
            expr = GiveBackExpr::Field(Box::new(expr), 0);
        }
        assert!(
            uses_fixed_width_arithmetic(&expr, &Module::new("depth-exhaustion")),
            "traversal-budget exhaustion must block authority"
        );
    }

    #[test]
    fn seq_map_gen_uncertified_element_fn_fails_closed() {
        // A LOSSY element operation (`*x = 7`: constant store, not reversible)
        // elaborates but has no certified give-back — the loop must NOT bind.
        let mut m = seq_map_gen_module();
        let lossy = {
            let entry = bid(0);
            let mut func = Function::new(
                FuncId::new(31),
                "lossy_elem",
                trust_ir::FuncTyId::new(1),
                entry,
            );
            let mut block = Block::new(entry);
            block.params.push((v(0), Ty::RefMut(Box::new(Ty::I32))));
            block
                .body
                .push(InstrNode::new(Inst::BorrowMut { ptr: v(0) }).with_result(v(1)));
            block.body.push(
                InstrNode::new(Inst::Const {
                    ty: Ty::I32,
                    value: Constant::Int(7),
                })
                .with_result(v(2)),
            );
            block.body.push(InstrNode::new(Inst::Store {
                ty: Ty::I32,
                ptr: v(1),
                value: v(2),
                volatile: false,
                align: None,
            }));
            block
                .body
                .push(InstrNode::new(Inst::EndBorrow { borrow_ptr: v(1) }));
            block
                .body
                .push(InstrNode::new(Inst::Return { values: vec![] }));
            func.blocks.push(block);
            func
        };
        m.functions[1] = lossy;
        let loop_fn = m.functions[0].clone();
        let view = match elaborate_give_back_in(&loop_fn, &m) {
            GiveBackOutcome::Accepted(view) => view,
            other => panic!("the loop itself still elaborates, got {other:?}"),
        };
        assert!(
            certifying_anchor_in(&view.backward.value_expr, &m).is_none(),
            "a loop over a NON-reversible element op must fail closed"
        );
        assert!(give_back_recheck_directive_in(&view, &m).is_none());
    }

    #[test]
    fn seq_map_gen_pointee_mismatch_fails_closed() {
        // Seq<bool> place against fn(&mut i32): the pointee guard rejects.
        let mut m = seq_map_gen_module();
        let bool_id = m
            .add_type(Ty::Bool)
            .expect("Module::add_type: test fixture");
        let loop_fn = seq_map_gen_loop_function(30, 31, bool_id.index());
        m.functions[0] = loop_fn.clone();
        let view = match elaborate_give_back_in(&loop_fn, &m) {
            GiveBackOutcome::Accepted(view) => view,
            other => panic!("expected Accepted, got {other:?}"),
        };
        assert!(
            give_back_recheck_directive_in(&view, &m).is_none(),
            "a Seq<bool> place must not certify against an fn(&mut i32) element op"
        );
    }
}

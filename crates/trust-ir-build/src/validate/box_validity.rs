// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! The validator rules of `Inst::BoxDeref` (wire v74): the carried
//! [`BoxValidityFact`] is judged here and nowhere else.
//!
//! A `BoxDeref` states that its operand, a thin pointer, is the address of a
//! live `Box` allocation of the named pointee. The fact names, per validity
//! conjunct, the evidence the producer offers. Every rule below REFUSES; none
//! repairs, defaults or infers a missing part:
//!
//! 1. **Types** ([`ValidationError::BoxDerefTypeMismatch`]): `ptr_ty` is
//!    `Ty::Ptr` and the operand has exactly that type.
//! 2. **Pointee scope** ([`ValidationError::BoxDerefPointeeOutOfScope`]): the
//!    sized pointee has a known layout, a nonzero size and is inhabited. A
//!    zero-sized or uninhabited pointee has no dereferenceable region to
//!    state, and is outside this rule set rather than vacuously inside it.
//! 3. **Conjunct cover** ([`ValidationError::BoxDerefConjunctCover`]): the
//!    evidence list is exactly the pointee's conjunct set, each once, in
//!    canonical order. A thin pointee's set is `NonNull`, `Aligned`,
//!    `Dereferenceable`; `MetadataValid` on it is refused.
//! 4. **Premise** ([`ValidationError::BoxDerefPremiseNotPinned`]): a premise
//!    names exactly the pinned standing assumptions, in canonical order.
//! 5. **Session** ([`ValidationError::BoxDerefSessionRefused`]): a fact that
//!    offers evidence states that it was produced in a proof session and
//!    judged on the verification snapshot. The producer decides validity in its verifier,
//!    so no fact of any root or evidence kind exists outside that session.
//! 6. **Dominating check**
//!    ([`ValidationError::BoxDerefDominatingCheckInvalid`]): REFUSED wherever
//!    it appears. The evidence kind keeps its wire spelling and no shape of
//!    check is admitted.
//! 7. **Obligation** ([`ValidationError::BoxDerefObligationUnbound`]):
//!    REFUSED wherever it appears. The evidence kind keeps its wire spelling
//!    and no row is admitted.
//! 8. **Non-claims** ([`ValidationError::BoxDerefNonClaimsNotPinned`]): the
//!    fact spells out exactly the pinned list of what it does not say.
//! 9. **Premise sanity** ([`ValidationError::BoxDerefPremiseContradicted`]):
//!    the premises of one fact name one root, and the function does not
//!    visibly contradict it (the list is at [`premise_contradictions`]).
//! 10. **No evidence** ([`ValidationError::BoxDerefConjunctUnestablished`],
//!     wire v75): every `Unestablished` entry is reported, on every
//!     admission and at every floor. Nothing in this repository discharges
//!     it. A consumer may discharge it only for a conjunct it RE-DERIVES
//!     itself from the instruction's own function, under its own named
//!     contract; every other consumer refuses the instruction. Rule 5 does
//!     not judge the session of a fact whose every entry is `Unestablished`:
//!     such a fact offers nothing a session could stand behind.
//!
//! The site id is carried and never judged: inlining copies a cast, so one
//! id may label many instructions of a module, each with its own fact. A
//! consumer counts instructions, never ids.
//!
//! The evidence floor ([`box_validity_floor_errors`],
//! [`ValidationError::BoxValidityEvidenceBelowFloor`]) is a consumer policy
//! layered on top by [`super::CodegenAdmission`]; it never relaxes a rule
//! above.
//!
//! Why rule 6 admits nothing. A check is evidence only in a shape some
//! producer emits and every consumer can lower. Neither holds: the producing
//! compiler's null and alignment checks reach this format as a conditional
//! branch and a call (never an `Assert`), with a pointer copy between the
//! cast and the tested address, so no `Assert`-over-the-result shape has
//! been run against producer output; and a target with no route for a
//! failing assert would refuse a module the other targets accept. A shape
//! that exempts `ptrtoint` of the result from the uses the check must
//! dominate is also unsound on its own: the address can be turned back into
//! a pointer (`inttoptr`) and dereferenced on a path the check does not
//! cover. Corpus rows `refuse/box_deref_check_pinned_shape` and
//! `refuse/box_deref_check_address_round_trip` pin both refusals.
//!
//! Why rule 7 admits nothing. A row's kind, owner and site can be checked,
//! and whether a certificate of it was replayed; its formula is not compared
//! with the conjunct. One replayed `MemorySafety` row stating anything,
//! sited on the instruction, would back every conjunct at once with no named
//! root and no standing assumption.
//!
//! Evidence boundary: rules 1–9 establish that the fact is WELL-FORMED. They
//! do not establish that a premise is true. Rule 9 removes premises the
//! function itself shows to be false or unrooted; a premise that passes it
//! is still a named assumption, at [`BoxValidityTier::NamedPremise`] or
//! [`BoxValidityTier::AssumedRootPremise`] by its root.

use std::collections::BTreeMap;

use trust_ir::analysis::{DominatorTree, SsaDefinitionSite, SsaUseSite};
use trust_ir::box_validity::{
    BoxPointee, BoxValidityFact, BoxValidityNonClaim, BoxValidityTier, JudgedBody, PremiseRoot,
    ProducingSession, StandingAssumption, ValidityConjunct, ValidityEvidence,
};
use trust_ir::{BlockId, CastOp, Function, Inst, Module, Ty, ValueId};

use super::ValidationError;

/// Whether `module` holds any `BoxDeref`; every pass below costs nothing on
/// a module that has none.
fn has_box_deref(module: &Module) -> bool {
    module.functions.iter().any(|func| {
        func.blocks.iter().any(|block| {
            block
                .body
                .iter()
                .any(|node| matches!(node.inst, Inst::BoxDeref { .. }))
        })
    })
}

/// Where a `BoxDeref` stands, for error payloads.
#[derive(Clone, Copy)]
struct At<'a> {
    func: &'a Function,
    block: BlockId,
    inst_index: usize,
}

impl At<'_> {
    fn function(&self) -> String {
        self.func.name.clone()
    }
    fn block(&self) -> u32 {
        self.block.index()
    }
    fn inst(&self) -> u32 {
        self.inst_index as u32
    }
}

/// What rule 9 reads of one function, built once per function that holds a
/// premise.
struct PremiseContext<'a> {
    func: &'a Function,
    /// SSA value -> its defining instruction, single-result definitions only.
    definitions: BTreeMap<u32, &'a Inst>,
    dominators: DominatorTree,
    /// The function takes at least one parameter.
    has_parameter: bool,
    /// The body holds a `HeapAlloc`.
    has_heap_alloc: bool,
    /// The body holds a call of any spelling.
    has_call: bool,
}

impl<'a> PremiseContext<'a> {
    fn new(func: &'a Function) -> Self {
        let mut definitions = BTreeMap::new();
        let mut has_heap_alloc = false;
        let mut has_call = false;
        for block in &func.blocks {
            for node in &block.body {
                if let [result] = node.results.as_slice() {
                    definitions.insert(result.index(), &node.inst);
                }
                has_heap_alloc |= matches!(node.inst, Inst::HeapAlloc { .. });
                has_call |= matches!(
                    node.inst,
                    Inst::Call { .. }
                        | Inst::CallIndirect { .. }
                        | Inst::Invoke { .. }
                        | Inst::InvokeIndirect { .. }
                        | Inst::CallCannotUnwind { .. }
                        | Inst::CallIndirectCannotUnwind { .. }
                );
            }
        }
        let has_parameter = func
            .blocks
            .iter()
            .find(|block| block.id == func.entry)
            .is_some_and(|entry| !entry.params.is_empty());
        Self {
            func,
            definitions,
            dominators: DominatorTree::new(func),
            has_parameter,
            has_heap_alloc,
            has_call,
        }
    }

    /// A `Dealloc` of exactly `pointer` that dominates the instruction at
    /// (`block`, `inst_index`): every path to the instruction has freed the
    /// allocation `pointer` names.
    fn dealloc_dominates(&self, pointer: ValueId, block: BlockId, inst_index: usize) -> bool {
        self.func.blocks.iter().any(|candidate| {
            candidate.body.iter().enumerate().any(|(index, node)| {
                matches!(&node.inst, Inst::Dealloc { ptr } if *ptr == pointer)
                    && self.dominators.definition_available_at(
                        SsaDefinitionSite {
                            block: candidate.id,
                            instruction: Some(index),
                        },
                        SsaUseSite::BeforeInstruction {
                            block,
                            instruction: inst_index,
                        },
                    )
            })
        })
    }
}

/// Rule 9. The reasons the premises of `fact`, on `operand` at
/// (`block`, `inst_index`), are contradicted by the function; empty when
/// none is.
///
/// These are SANITY refusals, decided from the function's own instructions
/// with no analysis beyond one definition and one dominance query. Passing
/// them does not make a premise true:
///
/// * the premises of one fact name ONE root, so a summary by root describes
///   every conjunct;
/// * the operand is not defined by `null_ptr` (not non-null), by `undef` (no
///   value to hold a property of) or by `inttoptr` (an address with no
///   allocation behind its definition, which no pinned root describes);
/// * `param_by_value` and `reference_arg_box_valid` name a parameter, so the
///   function has one;
/// * `alloc_postcondition` names an in-body allocation, so the body holds a
///   `HeapAlloc` or a call;
/// * `returned_box_discharged` and `returned_box_assumed` name a call's
///   return, so the body holds a call;
/// * no `Dealloc` of the operand dominates the instruction (a freed box is
///   not dereferenceable). `Drop` is not such an instruction: it runs the
///   pointee's glue in place and frees nothing.
///
/// The root is not otherwise related to the operand: that the operand IS the
/// named parameter, allocation or return is the producer's statement.
fn premise_contradictions(
    context: &PremiseContext<'_>,
    fact: &BoxValidityFact,
    operand: ValueId,
    block: BlockId,
    inst_index: usize,
) -> Vec<&'static str> {
    let mut reasons = Vec::new();
    let mut roots: Vec<PremiseRoot> = Vec::new();
    for entry in &fact.evidence {
        if let ValidityEvidence::Premise { root, .. } = &entry.evidence
            && !roots.contains(root)
        {
            roots.push(*root);
        }
    }
    if roots.is_empty() {
        return reasons;
    }
    if roots.len() > 1 {
        reasons.push(
            "the premises of one fact name more than one root; a fact has one root for every \
             premised conjunct",
        );
    }
    match context.definitions.get(&operand.index()) {
        Some(Inst::NullPtr) => {
            reasons.push("the operand is defined by null_ptr, so it is not non-null");
        }
        Some(Inst::Undef { .. }) => {
            reasons.push("the operand is defined by undef, which has no value to premise");
        }
        Some(Inst::Cast {
            op: CastOp::IntToPtr,
            ..
        }) => reasons.push(
            "the operand is defined by inttoptr: an address made from an integer is not a \
             parameter, an allocation or a returned box",
        ),
        _ => {}
    }
    for root in roots {
        match root {
            PremiseRoot::ParamByValue | PremiseRoot::ReferenceArgBoxValid => {
                if !context.has_parameter {
                    reasons.push("the root names a parameter and the function takes none");
                }
            }
            PremiseRoot::AllocPostcondition => {
                if !context.has_heap_alloc && !context.has_call {
                    reasons.push(
                        "the root names an in-body allocation and the body holds no heap_alloc \
                         and no call",
                    );
                }
            }
            PremiseRoot::ReturnedBoxDischarged | PremiseRoot::ReturnedBoxAssumed => {
                if !context.has_call {
                    reasons.push("the root names a call's return and the body holds no call");
                }
            }
        }
    }
    if context.dealloc_dominates(operand, block, inst_index) {
        reasons.push(
            "a dealloc of the operand dominates the instruction, so the allocation is freed on \
             every path to it",
        );
    }
    reasons
}

/// Rules 1–9 over every `BoxDeref` of `module`, in function / block /
/// instruction order.
pub(super) fn box_deref_errors(module: &Module) -> Vec<ValidationError> {
    let mut errors = Vec::new();
    if !has_box_deref(module) {
        return errors;
    }
    let layouts = module.layout_table();
    for func in &module.functions {
        let mut value_types: Option<BTreeMap<u32, Ty>> = None;
        let mut premise_context: Option<PremiseContext<'_>> = None;
        for block in &func.blocks {
            for (inst_index, node) in block.body.iter().enumerate() {
                let Inst::BoxDeref {
                    ptr_ty,
                    pointee,
                    operand,
                    fact,
                } = &node.inst
                else {
                    continue;
                };
                let at = At {
                    func,
                    block: block.id,
                    inst_index,
                };

                // Rule 1: types.
                if *ptr_ty != Ty::Ptr {
                    errors.push(ValidationError::BoxDerefTypeMismatch {
                        function: at.function(),
                        block: at.block(),
                        inst_index: at.inst(),
                        detail: format!(
                            "ptr_ty is {ptr_ty}, and a sized pointee is addressed by ptr"
                        ),
                    });
                }
                let types = value_types
                    .get_or_insert_with(|| super::build_module_value_types(func, module));
                match types.get(&operand.index()) {
                    Some(found) if found == ptr_ty => {}
                    Some(found) => errors.push(ValidationError::BoxDerefTypeMismatch {
                        function: at.function(),
                        block: at.block(),
                        inst_index: at.inst(),
                        detail: format!("operand has type {found}, not ptr_ty {ptr_ty}"),
                    }),
                    None => errors.push(ValidationError::BoxDerefTypeMismatch {
                        function: at.function(),
                        block: at.block(),
                        inst_index: at.inst(),
                        detail: "operand has no known type".to_string(),
                    }),
                }

                // Rule 2: pointee scope.
                if let Err(reason) = pointee_scope(&layouts, pointee) {
                    errors.push(ValidationError::BoxDerefPointeeOutOfScope {
                        function: at.function(),
                        block: at.block(),
                        inst_index: at.inst(),
                        reason,
                    });
                }

                // Rule 3: conjunct cover.
                if let Some(detail) = conjunct_cover_defect(pointee, fact) {
                    errors.push(ValidationError::BoxDerefConjunctCover {
                        function: at.function(),
                        block: at.block(),
                        inst_index: at.inst(),
                        detail,
                    });
                }

                // Rule 5: the session of a fact that offers evidence. Both
                // halves are reported when both are false. A fact whose every
                // entry is `Unestablished` offers nothing, so its session is
                // carried and not judged (rule 10 reports every entry).
                let judges_session = !fact.offers_no_evidence();
                if judges_session && fact.session.producing != ProducingSession::ProofSession {
                    errors.push(ValidationError::BoxDerefSessionRefused {
                        function: at.function(),
                        block: at.block(),
                        inst_index: at.inst(),
                        reason: "the fact was not produced in a proof session: the producer's \
                                 verifier did not run, so it holds no verdict for this site",
                    });
                }
                if judges_session && fact.session.judged != JudgedBody::VerificationSnapshot {
                    errors.push(ValidationError::BoxDerefSessionRefused {
                        function: at.function(),
                        block: at.block(),
                        inst_index: at.inst(),
                        reason: "the fact was judged on the optimized fallback body, which is \
                                 not the body the verifier examined",
                    });
                }

                for entry in &fact.evidence {
                    match &entry.evidence {
                        ValidityEvidence::Premise { root: _, standing } => {
                            // Rule 4.
                            if standing.as_slice() != StandingAssumption::PINNED.as_slice() {
                                errors.push(ValidationError::BoxDerefPremiseNotPinned {
                                    function: at.function(),
                                    block: at.block(),
                                    inst_index: at.inst(),
                                    conjunct: entry.conjunct.name(),
                                });
                            }
                        }
                        ValidityEvidence::DominatingCheck { .. } => {
                            // Rule 6: refused by name.
                            errors.push(ValidationError::BoxDerefDominatingCheckInvalid {
                                function: at.function(),
                                block: at.block(),
                                inst_index: at.inst(),
                                conjunct: entry.conjunct.name(),
                                reason: "dominating-check evidence is not admitted in this \
                                         version: no check shape is measured against a \
                                         producer or lowered by every target",
                            });
                        }
                        ValidityEvidence::Obligation { obligation } => {
                            // Rule 7: refused by name.
                            errors.push(ValidationError::BoxDerefObligationUnbound {
                                function: at.function(),
                                block: at.block(),
                                inst_index: at.inst(),
                                obligation: obligation.index(),
                                reason: "obligation evidence is not admitted in this version: \
                                         nothing compares the row's formula with the conjunct",
                            });
                        }
                        ValidityEvidence::Unestablished => {
                            // Rule 10: no evidence, reported on every
                            // admission. Only a consumer that re-derives
                            // the conjunct itself may discharge it.
                            errors.push(ValidationError::BoxDerefConjunctUnestablished {
                                function: at.function(),
                                block: at.block(),
                                inst_index: at.inst(),
                                conjunct: entry.conjunct.name(),
                            });
                        }
                    }
                }

                // Rule 9: premise sanity.
                if fact
                    .evidence
                    .iter()
                    .any(|entry| matches!(entry.evidence, ValidityEvidence::Premise { .. }))
                {
                    let context = premise_context.get_or_insert_with(|| PremiseContext::new(func));
                    for reason in
                        premise_contradictions(context, fact, *operand, block.id, inst_index)
                    {
                        errors.push(ValidationError::BoxDerefPremiseContradicted {
                            function: at.function(),
                            block: at.block(),
                            inst_index: at.inst(),
                            reason,
                        });
                    }
                }

                // Rule 8.
                if fact.not_claimed.as_slice() != BoxValidityNonClaim::PINNED.as_slice() {
                    errors.push(ValidationError::BoxDerefNonClaimsNotPinned {
                        function: at.function(),
                        block: at.block(),
                        inst_index: at.inst(),
                    });
                }
            }
        }
    }
    errors
}

/// Rule 2. The reason the pointee is outside the scope, read from the
/// module's layout table at the module target's widths.
fn pointee_scope(
    layouts: &trust_ir::LayoutTable<'_>,
    pointee: &BoxPointee,
) -> Result<(), &'static str> {
    let BoxPointee::Sized { ty } = pointee;
    let Ok(layout) = layouts.ty_layout(ty) else {
        return Err("the pointee has no computable layout, so no size or alignment to state");
    };
    if layouts.ty_is_uninhabited(ty) {
        return Err("the pointee is uninhabited: no live allocation of it exists");
    }
    if layout.size_bits == 0 {
        return Err("the pointee is zero-sized: it has no dereferenceable region");
    }
    if layout.size_bits % 8 != 0 {
        return Err("the pointee's size is not a whole number of bytes");
    }
    match layout.align_bits {
        Some(bits) if bits >= 8 && bits % 8 == 0 && (bits / 8).is_power_of_two() => Ok(()),
        _ => Err("the pointee has no byte power-of-two ABI alignment to state"),
    }
}

/// Rule 3. `None` when the evidence list is exactly the pointee's conjunct
/// set in canonical order.
fn conjunct_cover_defect(pointee: &BoxPointee, fact: &BoxValidityFact) -> Option<String> {
    let required: &[ValidityConjunct] = if pointee.is_wide() {
        &ValidityConjunct::ALL
    } else {
        &ValidityConjunct::THIN
    };
    let offered: Vec<ValidityConjunct> = fact.evidence.iter().map(|e| e.conjunct).collect();
    if offered.as_slice() == required {
        return None;
    }
    if let Some(extra) = offered.iter().find(|c| !required.contains(c)) {
        return Some(format!(
            "conjunct {} is not a conjunct of a {} pointee",
            extra.name(),
            pointee.shape_name()
        ));
    }
    if let Some(missing) = required.iter().find(|c| !offered.contains(c)) {
        return Some(format!("conjunct {} has no evidence", missing.name()));
    }
    if let Some(repeated) = required
        .iter()
        .find(|c| offered.iter().filter(|o| o == c).count() > 1)
    {
        return Some(format!(
            "conjunct {} carries evidence more than once",
            repeated.name()
        ));
    }
    Some("the conjuncts are not in canonical order".to_string())
}

/// The evidence-floor layer ALONE: one
/// [`ValidationError::BoxValidityEvidenceBelowFloor`] per conjunct of a
/// `BoxDeref` whose evidence tier is below `floor`, in function / block /
/// instruction / conjunct order. Run by
/// [`super::validate_module_for_codegen_with`] under
/// [`super::CodegenAdmission::with_require_box_validity_evidence`].
#[must_use]
pub fn box_validity_floor_errors(module: &Module, floor: BoxValidityTier) -> Vec<ValidationError> {
    let mut errors = Vec::new();
    for func in &module.functions {
        for block in &func.blocks {
            for (inst_index, node) in block.body.iter().enumerate() {
                let Inst::BoxDeref { fact, .. } = &node.inst else {
                    continue;
                };
                for entry in &fact.evidence {
                    // The tier is the entry's alone: an assumed root is
                    // below `NamedPremise`, a reserved evidence kind below
                    // every meaningful floor. `NotAdmitted` is the ordered
                    // minimum and therefore a no-op floor.
                    let tier = entry.evidence.tier();
                    if tier < floor {
                        errors.push(ValidationError::BoxValidityEvidenceBelowFloor {
                            function: func.name.clone(),
                            block: block.id.index(),
                            inst_index: inst_index as u32,
                            conjunct: entry.conjunct.name(),
                            tier: tier.name(),
                            floor: floor.name(),
                        });
                    }
                }
            }
        }
    }
    errors
}

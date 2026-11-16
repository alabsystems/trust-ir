// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! The validity fact an [`crate::Inst::BoxDeref`] carries (wire v74, Inst tag
//! 77; `docs/SPEC_RATIFICATIONS.md` §28).
//!
//! Rust defines the deref of a `Box<T>` as a pointer-to-pointer transmute
//! that is undefined behaviour unless the input is valid as a `Box<T>`. The
//! value half of that definition needs no fact: the result IS the operand.
//! The validity half is a hypothesis of the program, and this module is its
//! carrier. It states exactly the conjuncts rustc's interpreter checks at the
//! cast (non-null, aligned, dereferenceable for the pointee's size) and, per
//! conjunct, the authority the producer holds it on.
//!
//! # What the fact is not
//!
//! A [`BoxValidityFact`] is NOT a proof. The one evidence kind this version
//! admits is a named assumption ([`ValidityEvidence::Premise`]). The other
//! two have a wire spelling and are REFUSED by the validator wherever they
//! appear: a sited certificate ([`ValidityEvidence::Obligation`]), because
//! nothing compares its formula with the conjunct, and a runtime check on
//! the result ([`ValidityEvidence::DominatingCheck`]), because no check
//! shape has been measured against a producer's output and one target has
//! no route for a failing check. The class is read from the entry
//! ([`ValidityEvidence::tier`]); no status word raises it.
//!
//! # What a consumer may do with the instruction
//!
//! The instruction is undefined behaviour when a conjunct is false, and the
//! reference engines say so. That statement is NOT a licence: no consumer or
//! pass may use it, or a fact below a tier its own contract states, to
//! remove a check, to remove a branch, or to move or introduce a memory
//! access (`docs/SPEC_RATIFICATIONS.md` §28, "No licence from the undefined
//! behaviour"). A named assumption is carried and reported; it is never
//! acted on as if it were established.
//!
//! The fact also says nothing about three things, and carries that statement
//! on the wire as [`BoxValidityFact::not_claimed`], which must equal
//! [`BoxValidityNonClaim::PINNED`]:
//!
//! - uniqueness or ownership ([`BoxValidityNonClaim::Uniqueness`]): the
//!   format has no Rust aliasing carrier, and `BoxUnique` appears only as an
//!   assumption a premise depends on, never as a conclusion;
//! - the pointee's bytes ([`BoxValidityNonClaim::PointeeValidity`]): not
//!   initialised, not valid at its type, not inhabited. No consumer may
//!   derive unreachability from a fact about a `Box` of an uninhabited type;
//! - the allocator ([`BoxValidityNonClaim::Allocator`]).
//!
//! # Value properties and the point-in-time property
//!
//! `NonNull` and `Aligned` are properties of the pointer VALUE and hold for
//! every copy of it. `Dereferenceable` holds only AT the instruction: any
//! later operation that may free the allocation ends it. A consumer must not
//! carry it to another program point.

use crate::value::ProofId;

/// What a `Box` points at, as far as its validity rule needs to know.
///
/// Stage 1 carries the thin, statically sized shape only. Slice, `str`,
/// trait-object and unsized-tail pointees are not representable, so a
/// producer cannot spell one and a consumer never has to refuse one it
/// half-understands.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum BoxPointeeG<X> {
    /// A pointee of statically known size and alignment: the pointer is thin
    /// ([`crate::Ty::Ptr`]). The validator requires a positive static size
    /// (`BoxDerefPointeeOutOfScope`): a zero-sized or uninhabited pointee
    /// makes `Dereferenceable` vacuous and waits for its own evidence kind.
    Sized {
        /// The pointee type `T` of `Box<T>`.
        ty: crate::ty::TyG<X>,
    },
}

/// The level-R pointee shape.
pub type BoxPointee = BoxPointeeG<crate::level::NoExt>;

impl<X> BoxPointeeG<X> {
    /// The text spelling of the shape's head.
    pub const fn shape_name(&self) -> &'static str {
        match self {
            BoxPointeeG::Sized { .. } => "sized",
        }
    }

    /// The pointee type the shape is over.
    pub const fn ty(&self) -> &crate::ty::TyG<X> {
        match self {
            BoxPointeeG::Sized { ty } => ty,
        }
    }

    /// Mutable access to the pointee type.
    pub fn ty_mut(&mut self) -> &mut crate::ty::TyG<X> {
        match self {
            BoxPointeeG::Sized { ty } => ty,
        }
    }

    /// Whether the pointer is wide (carries metadata). No stage-1 shape is.
    pub const fn is_wide(&self) -> bool {
        match self {
            BoxPointeeG::Sized { .. } => false,
        }
    }
}

/// One conjunct of "valid as a `Box<T>`", in rustc's interpreter order.
///
/// The derived order is the CANONICAL order of
/// [`BoxValidityFact::evidence`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum ValidityConjunct {
    /// The address is not 0. A property of the value.
    NonNull,
    /// The address is a multiple of the pointee's alignment. A property of
    /// the value.
    Aligned,
    /// The pointer points into a live allocation covering
    /// `[addr, addr + size)`. Holds only at the instruction.
    Dereferenceable,
    /// Wide pointers only: the metadata is valid for the pointee. No stage-1
    /// shape is wide, so the validator refuses this conjunct wherever it
    /// appears (`BoxDerefConjunctCover`).
    MetadataValid,
}

impl ValidityConjunct {
    /// Every conjunct, in canonical order.
    pub const ALL: [ValidityConjunct; 4] = [
        ValidityConjunct::NonNull,
        ValidityConjunct::Aligned,
        ValidityConjunct::Dereferenceable,
        ValidityConjunct::MetadataValid,
    ];

    /// The conjuncts a THIN pointee's fact carries, in canonical order.
    pub const THIN: [ValidityConjunct; 3] = [
        ValidityConjunct::NonNull,
        ValidityConjunct::Aligned,
        ValidityConjunct::Dereferenceable,
    ];

    /// The text spelling.
    pub const fn name(self) -> &'static str {
        match self {
            ValidityConjunct::NonNull => "nonnull",
            ValidityConjunct::Aligned => "aligned",
            ValidityConjunct::Dereferenceable => "dereferenceable",
            ValidityConjunct::MetadataValid => "metadata_valid",
        }
    }

    /// Inverse of [`Self::name`].
    pub fn from_name(name: &str) -> Option<Self> {
        Self::ALL.into_iter().find(|c| c.name() == name)
    }

    /// Whether the conjunct is a property of the pointer VALUE (true for
    /// every copy) rather than of the program point.
    pub const fn is_value_property(self) -> bool {
        !matches!(self, ValidityConjunct::Dereferenceable)
    }
}

/// Where a named premise starts: the front end's root for "this box is
/// validity-rooted". The list is closed and pinned; a root outside it has no
/// spelling in any format.
///
/// Coverage boundary: this is the list drawn before any producer was
/// measured. The stage 0 census of the producing compiler found that these
/// five roots cover 4 of its Box casts and no whole program; the casts they
/// miss (a `vec!` expansion's store, a reborrow-only deref, a box reached
/// through a reference a safe call returned, a box slot lent as `&mut`)
/// have no root here and so no spelling. Each needs its own named root with
/// a refusal twin, which is a later wire version.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum PremiseRoot {
    /// A `Box<T, Global>` that is, or is reached by a field or variant path
    /// inside, a by-value parameter that is never reassigned.
    ParamByValue,
    /// An in-body `Box::new` / `Box::new_uninit`.
    AllocPostcondition,
    /// A `Box` returned by an admitted safe call whose callee the same
    /// session verified.
    ReturnedBoxDischarged,
    /// A `Box` returned by an admitted safe call whose callee was NOT
    /// verified (a sysroot or verify-off dependency). Named apart from
    /// [`Self::ReturnedBoxDischarged`] so the weaker cannot be read as the
    /// stronger.
    ReturnedBoxAssumed,
    /// The installed reference-argument premise, which nothing in the
    /// producing compiler proves.
    ReferenceArgBoxValid,
}

impl PremiseRoot {
    /// Every root, in declaration order.
    pub const ALL: [PremiseRoot; 5] = [
        PremiseRoot::ParamByValue,
        PremiseRoot::AllocPostcondition,
        PremiseRoot::ReturnedBoxDischarged,
        PremiseRoot::ReturnedBoxAssumed,
        PremiseRoot::ReferenceArgBoxValid,
    ];

    /// The text spelling.
    pub const fn name(self) -> &'static str {
        match self {
            PremiseRoot::ParamByValue => "param_by_value",
            PremiseRoot::AllocPostcondition => "alloc_postcondition",
            PremiseRoot::ReturnedBoxDischarged => "returned_box_discharged",
            PremiseRoot::ReturnedBoxAssumed => "returned_box_assumed",
            PremiseRoot::ReferenceArgBoxValid => "reference_arg_box_valid",
        }
    }

    /// Inverse of [`Self::name`].
    pub fn from_name(name: &str) -> Option<Self> {
        Self::ALL.into_iter().find(|r| r.name() == name)
    }

    /// The strength class of a premise on this root. Both classes are named
    /// assumptions; the lower one is a root whose own definition says the
    /// producing session verified nothing behind it.
    pub const fn tier(self) -> BoxValidityTier {
        match self {
            PremiseRoot::ParamByValue
            | PremiseRoot::AllocPostcondition
            | PremiseRoot::ReturnedBoxDischarged => BoxValidityTier::NamedPremise,
            PremiseRoot::ReturnedBoxAssumed | PremiseRoot::ReferenceArgBoxValid => {
                BoxValidityTier::AssumedRootPremise
            }
        }
    }
}

/// An assumption every premise depends on between its root and the cast.
///
/// The roots hold at function entry or at the allocation; the fact is needed
/// later. The front end bridges that gap with these three assumptions, so a
/// premise names all of them ([`Self::PINNED`]) or is malformed.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum StandingAssumption {
    /// No unsafe operation anywhere in the body.
    SafeBody,
    /// Every call between the root and the cast is sound.
    SoundCallees,
    /// No alias can free the allocation. Something the premise DEPENDS ON,
    /// not a conjunct the fact establishes.
    BoxUnique,
}

impl StandingAssumption {
    /// The standing set every premise carries, in canonical order.
    pub const PINNED: [StandingAssumption; 3] = [
        StandingAssumption::SafeBody,
        StandingAssumption::SoundCallees,
        StandingAssumption::BoxUnique,
    ];

    /// The text spelling.
    pub const fn name(self) -> &'static str {
        match self {
            StandingAssumption::SafeBody => "safe_body",
            StandingAssumption::SoundCallees => "sound_callees",
            StandingAssumption::BoxUnique => "box_unique",
        }
    }

    /// Inverse of [`Self::name`].
    pub fn from_name(name: &str) -> Option<Self> {
        Self::PINNED.into_iter().find(|s| s.name() == name)
    }
}

/// The strength class of one evidence entry. Ordered weakest first.
///
/// Every class an admitted entry reaches is a NAMED ASSUMPTION: not
/// exhaustive, not statistical, not solver-backed and not replayed evidence
/// of the conjunct. No entry reaches a solver-backed or kernel-replayed
/// class: those need the validator to bind an obligation's formula to the
/// conjunct, which it does not do.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum BoxValidityTier {
    /// An evidence kind this version refuses ([`ValidityEvidence::Obligation`],
    /// [`ValidityEvidence::DominatingCheck`]). As the ordered minimum, a
    /// floor set to `NotAdmitted` is a no-op; the structural rules still
    /// refuse both reserved evidence kinds. Meaningful floors begin at
    /// [`BoxValidityTier::AssumedRootPremise`].
    NotAdmitted,
    /// A premise whose root says the producing session verified nothing
    /// behind it ([`PremiseRoot::ReturnedBoxAssumed`],
    /// [`PremiseRoot::ReferenceArgBoxValid`]).
    AssumedRootPremise,
    /// A premise on one of the other pinned roots. Still an assumption: the
    /// name says which one, and nothing in the format establishes it.
    NamedPremise,
    /// Evidence every consumer re-derives from the instructions themselves.
    /// No evidence kind of this version reaches it; a floor set here refuses
    /// every `BoxDeref`.
    ConsumerRederived,
}

impl BoxValidityTier {
    /// Every class, weakest first.
    pub const ALL: [BoxValidityTier; 4] = [
        BoxValidityTier::NotAdmitted,
        BoxValidityTier::AssumedRootPremise,
        BoxValidityTier::NamedPremise,
        BoxValidityTier::ConsumerRederived,
    ];

    /// The diagnostic spelling.
    pub const fn name(self) -> &'static str {
        match self {
            BoxValidityTier::NotAdmitted => "not_admitted",
            BoxValidityTier::AssumedRootPremise => "assumed_root_premise",
            BoxValidityTier::NamedPremise => "named_premise",
            BoxValidityTier::ConsumerRederived => "consumer_rederived",
        }
    }
}

/// On whose authority one conjunct holds.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum ValidityEvidence {
    /// A named trust-base assumption: a root plus the standing assumptions
    /// that carry it to the cast. `standing` must equal
    /// [`StandingAssumption::PINNED`] (`BoxDerefPremiseNotPinned`), every
    /// premise of one fact names the same root, and the module must not
    /// visibly contradict the root (`BoxDerefPremiseContradicted`).
    Premise {
        root: PremiseRoot,
        standing: Vec<StandingAssumption>,
    },
    /// A runtime check on the instruction's result, for `NonNull` (`align`
    /// absent) and `Aligned` (`align` the pointee's alignment in bytes).
    ///
    /// RESERVED: the wire carries it and the validator refuses every
    /// occurrence (`BoxDerefDominatingCheckInvalid`). No check shape is
    /// admitted because none has been measured against a producer: the
    /// producing compiler's null and alignment checks reach this format as a
    /// conditional branch and a call, with a pointer copy between the cast
    /// and the tested address, never as an `Assert` over the result. A
    /// consumer whose target has no route for a failing check would also
    /// refuse a module the other targets accept.
    DominatingCheck {
        /// The alignment the check enforces, for `Aligned`.
        #[cfg_attr(feature = "serde", serde(default))]
        align: Option<u64>,
    },
    /// A sited obligation row.
    ///
    /// RESERVED: the wire carries it and the validator refuses every
    /// occurrence (`BoxDerefObligationUnbound`). A row's kind, owner and
    /// site can be checked, but nothing compares its formula with the
    /// conjunct, so a replayed certificate of any statement sited on the
    /// instruction would otherwise back every conjunct at once.
    Obligation { obligation: ProofId },
}

impl ValidityEvidence {
    /// The text spelling of the evidence kind.
    pub const fn kind_name(&self) -> &'static str {
        match self {
            ValidityEvidence::Premise { .. } => "premise",
            ValidityEvidence::DominatingCheck { .. } => "dominating_check",
            ValidityEvidence::Obligation { .. } => "obligation",
        }
    }

    /// The strength class this entry may be reported at. Read from the
    /// entry's kind and, for a premise, its root.
    pub const fn tier(&self) -> BoxValidityTier {
        match self {
            ValidityEvidence::Premise { root, .. } => root.tier(),
            ValidityEvidence::DominatingCheck { .. } | ValidityEvidence::Obligation { .. } => {
                BoxValidityTier::NotAdmitted
            }
        }
    }
}

/// One conjunct with its evidence.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct ConjunctEvidence {
    pub conjunct: ValidityConjunct,
    pub evidence: ValidityEvidence,
}

/// The identity of the source cast a fact was produced for: the defining
/// item plus a per-body ordinal.
///
/// The id travels with the cast through inlining and copy propagation, so one
/// id may label many emitted instructions; every count a consumer keeps is
/// per instruction, never per id. The format checks nothing about it.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct BoxDerefSite {
    /// The defining item's 128-bit stable hash, verbatim.
    pub item: [u8; 16],
    /// The cast's ordinal within that item's body.
    pub ordinal: u32,
}

/// Which body the producer's verifier judged.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum JudgedBody {
    /// The verification snapshot: the body the verifier was meant to judge.
    VerificationSnapshot,
    /// The optimized body the snapshot fell back to. A fact judged here is
    /// refused (`BoxDerefSessionRefused`): the verifier's positions are not
    /// the positions of the body it was meant to judge.
    OptimizedFallback,
}

impl JudgedBody {
    /// Both bodies, in declaration order.
    pub const ALL: [JudgedBody; 2] = [
        JudgedBody::VerificationSnapshot,
        JudgedBody::OptimizedFallback,
    ];

    /// The text spelling.
    pub const fn name(self) -> &'static str {
        match self {
            JudgedBody::VerificationSnapshot => "snapshot",
            JudgedBody::OptimizedFallback => "optimized_fallback",
        }
    }

    /// Inverse of [`Self::name`].
    pub fn from_name(name: &str) -> Option<Self> {
        Self::ALL.into_iter().find(|b| b.name() == name)
    }
}

/// Whether the compiler session that produced the fact ran its verifier.
///
/// The producer decides validity in its verifier, so a fact exists only in a
/// PROOF session. Such a session runs the unoptimized MIR pipeline at every
/// optimization level and refuses every option that would change it, so "a
/// proof session" is also "no value-changing MIR optimization ran": there is
/// no optimized proof session to name separately. A session whose verifier
/// did not run produced no verdict for any root or evidence kind.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum ProducingSession {
    /// The verifier ran over the body in this session.
    ProofSession,
    /// The verifier did not run. A fact that states this is refused
    /// (`BoxDerefSessionRefused`), whatever its evidence.
    NonProofSession,
}

impl ProducingSession {
    /// Both, in declaration order.
    pub const ALL: [ProducingSession; 2] = [
        ProducingSession::ProofSession,
        ProducingSession::NonProofSession,
    ];

    /// The text spelling.
    pub const fn name(self) -> &'static str {
        match self {
            ProducingSession::ProofSession => "proof_session",
            ProducingSession::NonProofSession => "non_proof_session",
        }
    }

    /// Inverse of [`Self::name`].
    pub fn from_name(name: &str) -> Option<Self> {
        Self::ALL.into_iter().find(|s| s.name() == name)
    }
}

/// The session condition a fact was produced under.
///
/// The format cannot observe the producing compiler, so this is the
/// producer's own statement; the validator refuses every statement other
/// than [`Self::PROOF_SNAPSHOT`] and takes nothing else from it.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct BoxFactSession {
    pub judged: JudgedBody,
    pub producing: ProducingSession,
}

impl BoxFactSession {
    /// The one admitted session: a proof session whose verifier judged the
    /// verification snapshot.
    pub const PROOF_SNAPSHOT: BoxFactSession = BoxFactSession {
        judged: JudgedBody::VerificationSnapshot,
        producing: ProducingSession::ProofSession,
    };
}

/// Something a [`BoxValidityFact`] does NOT say. The fact carries the whole
/// list ([`Self::PINNED`]) so the limit is on the wire, not only in prose.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum BoxValidityNonClaim {
    /// Nothing about uniqueness or ownership.
    Uniqueness,
    /// Nothing about the pointee being initialised, valid at its type, or
    /// inhabited.
    PointeeValidity,
    /// Nothing about the allocator.
    Allocator,
}

impl BoxValidityNonClaim {
    /// The non-claims every fact carries, in canonical order.
    pub const PINNED: [BoxValidityNonClaim; 3] = [
        BoxValidityNonClaim::Uniqueness,
        BoxValidityNonClaim::PointeeValidity,
        BoxValidityNonClaim::Allocator,
    ];

    /// The text spelling.
    pub const fn name(self) -> &'static str {
        match self {
            BoxValidityNonClaim::Uniqueness => "uniqueness",
            BoxValidityNonClaim::PointeeValidity => "pointee_validity",
            BoxValidityNonClaim::Allocator => "allocator",
        }
    }

    /// Inverse of [`Self::name`].
    pub fn from_name(name: &str) -> Option<Self> {
        Self::PINNED.into_iter().find(|n| n.name() == name)
    }
}

/// The validity record of one [`crate::Inst::BoxDeref`].
///
/// A mandatory field of the instruction: a `BoxDeref` with no fact has no
/// spelling. Every list is checked by the validator against its canonical
/// form; the constructor [`Self::premise`] builds that form.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct BoxValidityFact {
    /// The source cast this fact was produced for.
    pub site: BoxDerefSite,
    /// The session condition it was produced under.
    pub session: BoxFactSession,
    /// One entry per conjunct, in [`ValidityConjunct`] order, covering the
    /// pointee shape's conjuncts exactly.
    pub evidence: Vec<ConjunctEvidence>,
    /// What the fact does not say: exactly [`BoxValidityNonClaim::PINNED`].
    pub not_claimed: Vec<BoxValidityNonClaim>,
}

impl BoxValidityFact {
    /// A thin-pointee fact whose three conjuncts all rest on one named
    /// premise, in canonical form.
    pub fn premise(site: BoxDerefSite, session: BoxFactSession, root: PremiseRoot) -> Self {
        Self {
            site,
            session,
            evidence: ValidityConjunct::THIN
                .into_iter()
                .map(|conjunct| ConjunctEvidence {
                    conjunct,
                    evidence: ValidityEvidence::Premise {
                        root,
                        standing: StandingAssumption::PINNED.to_vec(),
                    },
                })
                .collect(),
            not_claimed: BoxValidityNonClaim::PINNED.to_vec(),
        }
    }

    /// The evidence entry for `conjunct`: the first one, if several are
    /// (invalidly) present.
    pub fn evidence_for(&self, conjunct: ValidityConjunct) -> Option<&ValidityEvidence> {
        self.evidence
            .iter()
            .find(|entry| entry.conjunct == conjunct)
            .map(|entry| &entry.evidence)
    }

    /// The one root every premise entry names, or `None` when the fact has
    /// no premise entry or its premises disagree. The validator refuses a
    /// disagreement, so on a validated fact a summary by this root describes
    /// every premise.
    pub fn premise_root(&self) -> Option<PremiseRoot> {
        let mut roots = self
            .evidence
            .iter()
            .filter_map(|entry| match entry.evidence {
                ValidityEvidence::Premise { root, .. } => Some(root),
                _ => None,
            });
        let first = roots.next()?;
        roots.all(|root| root == first).then_some(first)
    }

    /// The weakest strength class among the entries, or `None` for a fact
    /// with no entry (which the validator refuses). A fact is only as strong
    /// as its weakest conjunct.
    pub fn weakest_tier(&self) -> Option<BoxValidityTier> {
        self.evidence
            .iter()
            .map(|entry| entry.evidence.tier())
            .min()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn canonical_premise_fact_covers_the_thin_conjuncts_in_order() {
        let fact = BoxValidityFact::premise(
            BoxDerefSite {
                item: [7; 16],
                ordinal: 3,
            },
            BoxFactSession::PROOF_SNAPSHOT,
            PremiseRoot::ParamByValue,
        );
        let conjuncts: Vec<_> = fact.evidence.iter().map(|e| e.conjunct).collect();
        assert_eq!(conjuncts, ValidityConjunct::THIN);
        assert_eq!(fact.not_claimed, BoxValidityNonClaim::PINNED);
        assert_eq!(fact.weakest_tier(), Some(BoxValidityTier::NamedPremise));
    }

    #[test]
    fn the_reserved_evidence_kinds_are_below_every_premise() {
        let obligation = ValidityEvidence::Obligation {
            obligation: ProofId(0),
        };
        assert_eq!(obligation.tier(), BoxValidityTier::NotAdmitted);
        let check = ValidityEvidence::DominatingCheck { align: None };
        assert_eq!(check.tier(), BoxValidityTier::NotAdmitted);
        assert!(BoxValidityTier::ALL.is_sorted());
        for root in PremiseRoot::ALL {
            assert!(BoxValidityTier::NotAdmitted < root.tier(), "{root:?}");
            assert!(root.tier() < BoxValidityTier::ConsumerRederived, "{root:?}");
        }
    }

    #[test]
    fn a_root_that_verified_nothing_is_a_class_below_the_others() {
        let assumed: Vec<_> = PremiseRoot::ALL
            .into_iter()
            .filter(|root| root.tier() == BoxValidityTier::AssumedRootPremise)
            .collect();
        assert_eq!(
            assumed,
            [
                PremiseRoot::ReturnedBoxAssumed,
                PremiseRoot::ReferenceArgBoxValid
            ]
        );
        assert!(BoxValidityTier::AssumedRootPremise < BoxValidityTier::NamedPremise);
    }

    #[test]
    fn a_fact_is_as_strong_as_its_weakest_conjunct() {
        let site = BoxDerefSite {
            item: [0; 16],
            ordinal: 0,
        };
        let mut fact = BoxValidityFact::premise(
            site,
            BoxFactSession::PROOF_SNAPSHOT,
            PremiseRoot::AllocPostcondition,
        );
        assert_eq!(fact.premise_root(), Some(PremiseRoot::AllocPostcondition));
        if let ValidityEvidence::Premise { root, .. } = &mut fact.evidence[2].evidence {
            *root = PremiseRoot::ReturnedBoxAssumed;
        }
        assert_eq!(
            fact.weakest_tier(),
            Some(BoxValidityTier::AssumedRootPremise)
        );
        assert_eq!(fact.premise_root(), None, "the premises disagree");
        fact.evidence[0].evidence = ValidityEvidence::DominatingCheck { align: None };
        assert_eq!(fact.weakest_tier(), Some(BoxValidityTier::NotAdmitted));
        fact.evidence.clear();
        assert_eq!(fact.weakest_tier(), None);
        assert_eq!(fact.premise_root(), None);
    }

    #[test]
    fn names_round_trip() {
        for conjunct in ValidityConjunct::ALL {
            assert_eq!(ValidityConjunct::from_name(conjunct.name()), Some(conjunct));
        }
        for root in PremiseRoot::ALL {
            assert_eq!(PremiseRoot::from_name(root.name()), Some(root));
        }
        for standing in StandingAssumption::PINNED {
            assert_eq!(
                StandingAssumption::from_name(standing.name()),
                Some(standing)
            );
        }
        for non_claim in BoxValidityNonClaim::PINNED {
            assert_eq!(
                BoxValidityNonClaim::from_name(non_claim.name()),
                Some(non_claim)
            );
        }
        for body in JudgedBody::ALL {
            assert_eq!(JudgedBody::from_name(body.name()), Some(body));
        }
        for producing in ProducingSession::ALL {
            assert_eq!(
                ProducingSession::from_name(producing.name()),
                Some(producing)
            );
        }
    }

    #[test]
    fn exactly_one_session_is_the_admitted_one() {
        let admitted: Vec<_> = JudgedBody::ALL
            .into_iter()
            .flat_map(|judged| {
                ProducingSession::ALL
                    .into_iter()
                    .map(move |producing| BoxFactSession { judged, producing })
            })
            .filter(|session| *session == BoxFactSession::PROOF_SNAPSHOT)
            .collect();
        assert_eq!(admitted, [BoxFactSession::PROOF_SNAPSHOT]);
    }
}

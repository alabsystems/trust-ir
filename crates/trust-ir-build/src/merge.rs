// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Library module merge and id remap (roadmap WS4.11, F-069).
//!
//! [`merge_into`] joins one module (`src`) into another (`dst`) and returns
//! the [`Remap`] that names, for every id of `src`, the id it has in `dst`.
//! Before this module every producer and consumer that joined modules — the
//! `trust-ir run` linker, ~/trust's Clean-origin join, trust-cg's
//! `module_merge` — re-implemented the table remap privately, so every
//! id-bearing construct the format gained (v42 tuple layouts, v43 handles,
//! predicates and universes) had to be re-taught to each private remapper,
//! and "unremapped-table refusal" was a trusted-base row.
//!
//! # Exhaustiveness is the design
//!
//! The merger DESTRUCTURES [`Module`], [`Function`], [`Global`],
//! [`InstrNode`], [`Block`], [`FuncAttrs`], [`ParamAttrs`],
//! [`FunctionSummary`], [`EffectSummary`], [`ProofObligation`],
//! [`ProofCertificate`], [`ObligationDiagnostic`], [`SpecModule`],
//! [`SpecAnchor`], [`StructDef`], [`EnumDef`], [`RecordDef`], [`ClosureTy`],
//! [`FuncTy`], [`TupleLayoutDescriptor`], [`ClosureLayoutDescriptor`] and
//! every [`Inst`], [`Ty`], [`Constant`], [`EffectSet`], [`EffectPlace`] and
//! [`ProofEvidence`] variant with no `..`: a field or variant added to any of
//! them is a compile error here, never an id silently copied stale. (Proof
//! annotations are the one wildcard: the only id-bearing one, `ProofRef`, is
//! matched by name, and the feature-gated `Goal` variant cannot be named
//! portably from this crate.)
//!
//! # What merges how
//!
//! * **Symbols are identity.** Functions and globals are keyed by their
//!   link-time symbol (`name`). The merger never renames: two `Internal`
//!   functions that share a symbol are one entity here, exactly as two
//!   `External` ones are, and a caller that wants them kept apart renames
//!   first.
//! * **Definitions** under [`DuplicateDef::DedupIdentical`] dedup only on
//!   FULL equality of the remapped [`Function`] — body, `producer`,
//!   `body_gate`, `display_path`, `attrs`, `linkage`, `calling_conv`,
//!   `summary`, `proofs`, … (every field but `id` and the dropped
//!   `source_provenance`; the license is compared without its dropped v61
//!   evidence, below). Any difference is
//!   [`MergeError::ConflictingDefinition`] naming the first differing field,
//!   never "keep the first": otherwise input ORDER would choose a codegen
//!   license or a proof claim. Equality is structural `PartialEq`, including
//!   [`Constant`]'s bit-exact float identity: signed zero and distinct NaN
//!   payloads differ, while identical NaN bit patterns dedup.
//! * **A declaration and a definition** resolve to the definition. They must
//!   agree on `ty` and `calling_conv` (an ABI fact both sides state); every
//!   other field of the declaration — its summary included — is dropped,
//!   which can lose a claim and never gains one. An obligation scoped to a
//!   superseded declaration is refused
//!   ([`MergeError::SupersededDeclarationScoped`]): re-scoped to the
//!   definition it could back a claim it was never about.
//! * **Two declarations** follow [`MergePolicy::on_duplicate_declaration`].
//!   Under [`DuplicateDecl::RequireIdentical`] (the verification image) they
//!   must be identical in every field: a declaration's summary is a claim,
//!   and input order must not pick one. Under [`DuplicateDecl::FirstStands`]
//!   (the execution image — the WS4.6 linker's rule, "a declaration adds
//!   nothing to an existing entry") they must agree on the ABI both state,
//!   `ty` and `calling_conv`, and the EARLIER declaration stands: every other
//!   field of the later one is dropped exactly as a declaration's is when a
//!   definition resolves it — which can lose a claim and never gains one, and
//!   an obligation scoped to the dropped declaration is refused
//!   ([`MergeError::SupersededDeclarationScoped`]). The image keeps the
//!   earlier declaration's own facts (its linkage included), so a malformed
//!   one stays malformed for `validate_module` to name AS MERGED.
//! * **Nominal types are never unified by name.** A struct, enum, record or
//!   closure type of `src` maps onto a `dst` definition only when the
//!   remapped definition is literally equal to it (coinductively, so
//!   self-referential types dedup); otherwise it is a NEW definition, even
//!   under an equal name. `Ty::Handle` and `Ty::Dialect` are compared by
//!   their full structure, so `("Nat", "trust_bignum::Nat")` and
//!   `("Nat", "other::Nat")` stay two distinct types and a merged call that
//!   passes one where the other is expected is refused by `validate_module`
//!   exactly as within one module.
//! * **Positional tables** (`types`, `func_types`, `closure_types`) are
//!   APPENDED whole, in `src` order, so `src`'s own aliases survive;
//!   every REFERENCE to a row that equals a row `dst` held before the merge
//!   points at `dst`'s row, so equal types are one id across the merged
//!   image. A row whose content names a newly appended row is never deduped
//!   (it cannot equal a pre-existing row, and a dangling `dst` reference must
//!   not capture it). Globals are keyed by symbol instead (above).
//! * **Explicit-id tables** keep `src`'s numbering shifted past `dst`'s:
//!   a new struct / enum / record / obligation gets `base + src_id`, where
//!   `base` is one past the highest id `dst` uses, and new rows keep `src`'s
//!   table order. Functions are the exception: a new function gets the next
//!   DENSE id, handed out in `src` id order, because the interpreter and
//!   validators resolve calls by id and a sparse table falls back to a
//!   linear scan.
//! * **The drop-glue table** (amendment D) is carried, never dropped: each
//!   row's glue is remapped like a `Call` callee and its key like any inline
//!   type, and the merged table keeps its one canonical order. A second glue
//!   for one type, or one glue for two types, is
//!   [`MergeError::DropGlueConflict`] — input order never chooses a
//!   destructor; an identical row restated is one row.
//! * **Content-interned tables** (universes, predicates, imports, tuple
//!   layouts) merge by content. A `src` table that is not interned (two
//!   equal rows) is refused, not silently repaired.
//! * **Closure layouts** (wire v58) are keyed by closure-type ID: each row
//!   follows its closure type's remap, and a row landing on a type the
//!   merged image already lays out must be identical (one row), else
//!   [`MergeError::ConflictingDefinition`] names the differing field. A
//!   type's nominal `origin` (wire v58) is carried verbatim on its struct /
//!   enum definition and is part of the literal equality a `dst` match
//!   needs, so two definitions that differ only in origin stay two types.
//! * **Proof state.** With [`MergePolicy::carry_proof_state`], obligations,
//!   certificates, diagnostics and spec modules are carried and remapped
//!   (`function`, `site`, `ProofRef`, `ProofContext`, `InheritedFromCallee`,
//!   spec anchors). `ClausePlace::Value` bindings need no rewrite: the
//!   merger never renumbers a function's SSA values, so the per-function
//!   value map of roadmap WS4.4's NEW-1 is the identity here and no second
//!   value remapper exists. A carried `Certified` row is NOT re-earned by the
//!   merge — the validator re-checks it in the merged image, where a lineage
//!   bound to module-local ids may no longer replay. Without it, the merger
//!   strips `src`'s claims exactly as the WS4.6 linker did: summaries (a
//!   contract-only declaration keeps the claim-free EMPTY summary), every
//!   `ProofRef` and call-site `ProofContext`, and the obligation /
//!   certificate / diagnostic / spec-module tables; the counts are in
//!   [`Remap::stripped`].
//! * **Effect summaries** (wire v59, `FunctionSummary::effects`) are part
//!   of the summary: carried with it under
//!   [`MergePolicy::carry_proof_state`] and stripped with it otherwise (a
//!   stripped claim is `None`, UNRECORDED — a caller havocs, so nothing is
//!   invented). A `ParamPointee` place is positional in the function's own
//!   signature and is carried as is; a `Global` place follows the global
//!   remap, and the mapped `Places` list is re-sorted into its one canonical
//!   spelling (the remap is not monotone). The claim names the same storage
//!   in the image as in `src`: no place is dropped, none added. A
//!   non-canonical `src` set is [`MergeError::Malformed`], never repaired.
//!   As part of `summary`, two DECLARATIONS that differ only in effects are
//!   a [`MergeError::ConflictingDefinition`] naming `summary` under
//!   [`DuplicateDecl::RequireIdentical`], and the EARLIER declaration's
//!   effects stand under [`DuplicateDecl::FirstStands`] — never the later
//!   one's, never a union.
//! * **Reserved Trust disclosures** whose row text binds function ids
//!   (`fn:<index>` keys) are never relocated: carried only where no function
//!   id moves, else [`MergeError::UnrelocatableDisclosure`].
//! * **Source provenance** is DROPPED from every function of `src`
//!   ([`Remap::dropped_provenance`]): its seal hashes the containing module
//!   (F-078), so a relocated carrier would only fail
//!   `validate_source_provenance` in the merged image.
//! * **Codegen-license evidence** (wire v61, `GateEvidence`) is DROPPED from
//!   every function of `src` ([`Remap::dropped_gate_evidence`]); the license
//!   and its authority are carried. The evidence names an obligation by
//!   `src`'s id and the `function_body_digest` of a body whose function and
//!   type ids the merge renumbers (and whose drops may resolve through a
//!   merged drop-glue table), so it cannot hold as written, and a merger that
//!   re-stamped it would vouch for a license it never checked. An
//!   evidence-free license is the pre-evidence meaning: admitted by the
//!   default lanes, refused under `ValidationConfig::with_gate_evidence`
//!   (`UnevidencedGate`) until it is re-minted against the image. Licenses
//!   are compared WITHOUT their evidence for the duplicate rules, so an
//!   identical evidenced definition dedups and `dst`'s copy stands; `dst`'s
//!   evidence is never rewritten, and the validator recomputes it in the
//!   merged image (a `src` drop-glue row that now resolves one of its drops
//!   moves its digest: `GatedEvidenceMismatch`, a verdict about the join).
//! * **Completeness** claims combine: `Complete` with `Complete` is
//!   `Complete`, `Partial` rows union (exact duplicates once; a row naming a
//!   symbol the OTHER input defines is resolved and dropped, and if every
//!   row resolves the claim is `Complete`), and `None` (no claim)
//!   absorbs every claim. The identity element of the merge is therefore an
//!   empty module claiming `Some(Complete)`; a plain `Module::new` absorbs.
//! * **Files** merge STRUCTURALLY and no path string is ever read: a
//!   `Module.files` string is debug-only (the V3 identity blanks it, and the
//!   conformance tripwire `module_files_strings_are_debug_only` holds every
//!   reader to that), so the merged table, every span's file index and every
//!   verdict depend only on the tables' LENGTHS and on where spans occur.
//!   `src`'s table is appended whole, in order, and every `src` span points
//!   at its own appended row — never at a `dst` row that happens to spell the
//!   same path. A span of a module with an empty file table is file-less:
//!   when the merged image gains a table, the file-less side's spans are
//!   pointed at a placeholder row `""` ("unknown file") APPENDED for them,
//!   rather than at whatever real file happens to sit at their index.
//!   [`RetainedImage`] additionally carries immutable original inputs and
//!   actual canonical placement receipts: importing the SAME retained input
//!   again may reuse only its own recorded rows. Equal paths, equal content,
//!   or equal V3 digests do not establish that custody. Ordinary `merge_into`
//!   and distinct/file-less inputs retain the structural rules above.
//!
//! # Fail-closed
//!
//! On `Err`, `dst` is UNCHANGED: everything is computed against a shared
//! borrow of `dst` and committed only when the whole merge succeeds. A
//! dangling id in `src` is [`MergeError::Dangling`]; every `Remap` lookup
//! returns `Option`, so an unmapped id is a caller refusal, never a default.
//!
//! The merger validates nothing it does not need to remap: run
//! `validate_module` on the result. Merging a valid module into a valid
//! module adds no error class the inputs did not have beyond the ones the
//! format attaches to the JOIN itself (a cross-input call whose nominal types
//! were never one type, a `Certified` lineage bound to the old ids).

use std::collections::{BTreeMap, HashMap, HashSet};

mod retained;
pub use retained::RetainedImage;
use std::fmt;

use crate::validate::RESERVED_TRUST_INTERNAL_SPEC_MODULES;

use trust_ir::constant::Constant;
use trust_ir::dialect::{AttrEntry, AttrValue, DialectInst};
use trust_ir::inst::{BindingFrameDef, BindingSlot, Inst, PanicLocation, PanicSite, SwitchCase};
use trust_ir::node::InstrNode;
use trust_ir::proof::{
    ObligationDiagnostic, ObligationSite, ProofAnnotation, ProofCertificate, ProofContext,
    ProofEvidence, ProofObligation,
};
use trust_ir::value::GlobalId;
use trust_ir::{
    Block, BodyGate, ClosureLayoutDescriptor, ClosureTy, ClosureTyId, DropGlueConflict,
    DropGlueEntry, EffectPlace, EffectSet, EffectSummary, EnumDef, EnumId, EnumVariant, ExternRef,
    FatPtrKind, FieldDef, FuncAttrs, FuncId, FuncTy, FuncTyId, Function, FunctionSummary, Global,
    ImportId, InlinedAt, Linkage, Module, ModuleCompleteness, ParamAttrs, PassMode, Pred, PredId,
    ProofId, RecordDef, RecordId, ScopeData, SourceSpan, SpecAnchor, SpecModule,
    SpecProjectionTarget, StructDef, StructId, TupleLayoutDescriptor, Ty, TyId, TypedId, UnivId,
    UnloweredRow,
};

// ---------------------------------------------------------------------------
// Public surface
// ---------------------------------------------------------------------------

/// What [`merge_into`] does with two DEFINITIONS (bodied functions, or
/// initialized globals) of one symbol.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DuplicateDef {
    /// Two definitions of one symbol are [`MergeError::DuplicateDefinition`].
    Refuse,
    /// Two definitions of one symbol dedup only when FULLY equal after the
    /// remap; any difference is [`MergeError::ConflictingDefinition`].
    DedupIdentical,
}

/// What [`merge_into`] does with two DECLARATIONS (bodyless functions) of
/// one symbol. Either way they must agree on `ty` and `calling_conv`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DuplicateDecl {
    /// The two declarations must be identical in every field after the
    /// remap; any difference is [`MergeError::ConflictingDefinition`].
    RequireIdentical,
    /// The earlier declaration stands and the later one adds nothing beyond
    /// the ABI check (the WS4.6 linker rule; see the module docs).
    FirstStands,
}

/// The merge policy.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct MergePolicy {
    /// Two definitions of one symbol: refuse, or dedup when identical.
    pub on_duplicate_definition: DuplicateDef,
    /// Two declarations of one symbol: identical, or the earlier stands.
    pub on_duplicate_declaration: DuplicateDecl,
    /// Carry (and remap) `src`'s obligations, certificates, diagnostics, spec
    /// modules, summaries, `ProofRef`s and `ProofContext`s; when `false` they
    /// are stripped (see the module docs).
    pub carry_proof_state: bool,
    /// Carry `src`'s import table (content-interned into `dst`'s). When
    /// `false` the rows are dropped, and a carried reference to one
    /// (`FunctionSummary::backed_by`, `InheritedFromCallee::external`) is
    /// [`MergeError::ImportsNotCarried`].
    pub carry_imports: bool,
}

impl MergePolicy {
    /// An execution image (what `trust-ir run` links): identical duplicate
    /// definitions dedup, the earlier of two declarations stands, no proof
    /// claims, no imports.
    pub const EXECUTION_IMAGE: Self = Self {
        on_duplicate_definition: DuplicateDef::DedupIdentical,
        on_duplicate_declaration: DuplicateDecl::FirstStands,
        carry_proof_state: false,
        carry_imports: false,
    };

    /// A verification image: identical duplicates (definitions and
    /// declarations) dedup, proof state and imports carried (and re-checked
    /// by the validator in the merged image).
    pub const VERIFICATION_IMAGE: Self = Self {
        on_duplicate_definition: DuplicateDef::DedupIdentical,
        on_duplicate_declaration: DuplicateDecl::RequireIdentical,
        carry_proof_state: true,
        carry_imports: true,
    };
}

/// Why [`merge_into`] refused. `dst` is unchanged.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum MergeError {
    /// Detached source roots fail the existing module type-root rules. The
    /// actual typed validator diagnostics remain available to the consumer.
    InvalidTypeRoots {
        errors: Vec<crate::validate::ValidationError>,
    },
    /// `src` cites `id` in `table`, which `src` does not have.
    Dangling { table: &'static str, id: u32 },
    /// `src`'s `table` row `id` cannot be remapped as stored (a duplicate
    /// explicit id, a table that is not content-interned, a non-canonical
    /// interned row, a forward reference in an append-only table).
    Malformed {
        table: &'static str,
        id: u32,
        detail: &'static str,
    },
    /// Two definitions of `symbol` under [`DuplicateDef::Refuse`].
    DuplicateDefinition { symbol: String },
    /// Two entries for `symbol` that differ in `field` (the first differing
    /// field, in declaration order). A tuple layout conflict names
    /// `tuple layout <type>` as its symbol.
    ConflictingDefinition { symbol: String, field: &'static str },
    /// Both modules pin a target and the targets differ.
    TargetMismatch { dst: String, src: String },
    /// A declaration of `symbol` is superseded by a definition, and an
    /// obligation is scoped to the declaration.
    SupersededDeclarationScoped { symbol: String },
    /// A carried reference to an import while
    /// [`MergePolicy::carry_imports`] is `false`.
    ImportsNotCarried { location: String },
    /// A merged table outgrew its `u32` id space.
    IdSpaceExhausted { table: &'static str },
    /// A reserved Trust disclosure whose row text binds module-local
    /// function ids would be relocated (see the module docs).
    UnrelocatableDisclosure { name: String },
    /// `src`'s drop-glue row (glue `@glue`, type `ty`, both as remapped)
    /// contradicts the merged table: the type already has another glue, or
    /// the glue already destroys another type.
    DropGlueConflict {
        glue: String,
        ty: String,
        conflict: DropGlueConflict,
    },
}

impl fmt::Display for MergeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            MergeError::InvalidTypeRoots { errors } => {
                write!(f, "invalid extra source type roots: {errors:?}")
            }
            MergeError::Dangling { table, id } => {
                write!(f, "dangling id {id} in the {table} table")
            }
            MergeError::Malformed { table, id, detail } => {
                write!(f, "{table} row {id} cannot be merged: {detail}")
            }
            MergeError::DuplicateDefinition { symbol } => {
                write!(f, "duplicate definitions of @{symbol}")
            }
            MergeError::ConflictingDefinition { symbol, field } => {
                write!(f, "conflicting definitions of @{symbol}: {field} differs")
            }
            MergeError::TargetMismatch { dst, src } => {
                write!(f, "target mismatch: image is {dst}, module declares {src}")
            }
            MergeError::SupersededDeclarationScoped { symbol } => write!(
                f,
                "an obligation is scoped to the declaration of @{symbol}, which a definition supersedes"
            ),
            MergeError::ImportsNotCarried { location } => write!(
                f,
                "{location} cites an import, and the policy does not carry imports"
            ),
            MergeError::IdSpaceExhausted { table } => {
                write!(f, "the merged {table} table exceeds the u32 id space")
            }
            MergeError::UnrelocatableDisclosure { name } => write!(
                f,
                "spec module {name} binds module-local function ids in its row text, \
                 which the merge cannot relocate"
            ),
            MergeError::DropGlueConflict { glue, ty, conflict } => write!(
                f,
                "drop_glue row @{glue} {ty} conflicts with the merged image: {conflict}"
            ),
        }
    }
}

impl std::error::Error for MergeError {}

/// The proof state [`merge_into`] stripped from `src` (all zero when
/// [`MergePolicy::carry_proof_state`] is set, except `imports`, which counts
/// rows dropped because [`MergePolicy::carry_imports`] is unset). Counted per
/// INPUT row: a declaration and the definition that supersedes it each count.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct StrippedProofState {
    /// `Function.summary` rows (a contract-only declaration's summary is
    /// counted and replaced by the claim-free empty one).
    pub summaries: usize,
    /// `ProofAnnotation::ProofRef`s, function- and node-level.
    pub proof_refs: usize,
    /// Call-site `ProofContext`s.
    pub proof_contexts: usize,
    /// Module obligations.
    pub obligations: usize,
    /// Module certificates.
    pub certificates: usize,
    /// Obligation diagnostics.
    pub diagnostics: usize,
    /// Spec modules.
    pub spec_modules: usize,
    /// Import rows.
    pub imports: usize,
}

/// Where every id of `src` landed in `dst`. Every lookup returns `Option`: an
/// id `src` does not have is `None`, which a caller must treat as a refusal.
#[derive(Debug, Clone, Default)]
pub struct Remap {
    funcs: HashMap<FuncId, FuncId>,
    types: Vec<TyId>,
    func_types: Vec<FuncTyId>,
    structs: HashMap<StructId, StructId>,
    enums: HashMap<EnumId, EnumId>,
    records: HashMap<RecordId, RecordId>,
    closures: Vec<ClosureTyId>,
    globals: Vec<GlobalId>,
    preds: Vec<PredId>,
    univs: Vec<UnivId>,
    imports: Vec<ImportId>,
    proofs: HashMap<ProofId, ProofId>,
    file_indices: Vec<u32>,
    dropped_provenance: usize,
    dropped_gate_evidence: usize,
    stripped: StrippedProofState,
    resolved_unlowered: usize,
}

impl Remap {
    /// The merged id of `src` function `id`.
    #[must_use]
    pub fn func(&self, id: FuncId) -> Option<FuncId> {
        self.funcs.get(&id).copied()
    }
    /// The merged id `src` type row `id` is referenced by.
    #[must_use]
    pub fn ty(&self, id: TyId) -> Option<TyId> {
        self.types.get(id.as_usize()).copied()
    }
    /// The merged id `src` signature `id` is referenced by.
    #[must_use]
    pub fn func_ty(&self, id: FuncTyId) -> Option<FuncTyId> {
        self.func_types.get(id.as_usize()).copied()
    }
    /// The merged id of `src` struct `id`.
    #[must_use]
    pub fn struct_(&self, id: StructId) -> Option<StructId> {
        self.structs.get(&id).copied()
    }
    /// The merged id of `src` enum `id`.
    #[must_use]
    pub fn enum_(&self, id: EnumId) -> Option<EnumId> {
        self.enums.get(&id).copied()
    }
    /// The merged id of `src` record `id`.
    #[must_use]
    pub fn record(&self, id: RecordId) -> Option<RecordId> {
        self.records.get(&id).copied()
    }
    /// The merged id of `src` closure type `id`.
    #[must_use]
    pub fn closure(&self, id: ClosureTyId) -> Option<ClosureTyId> {
        self.closures.get(id.as_usize()).copied()
    }
    /// The merged id of `src` global `id`.
    #[must_use]
    pub fn global(&self, id: GlobalId) -> Option<GlobalId> {
        self.globals.get(id.as_usize()).copied()
    }
    /// The merged id of `src` predicate `id`.
    #[must_use]
    pub fn pred(&self, id: PredId) -> Option<PredId> {
        self.preds.get(id.as_usize()).copied()
    }
    /// The merged id of `src` universe `id`.
    #[must_use]
    pub fn univ(&self, id: UnivId) -> Option<UnivId> {
        self.univs.get(id.as_usize()).copied()
    }
    /// The merged id of `src` import `id` (`None` when imports were not
    /// carried).
    #[must_use]
    pub fn import(&self, id: ImportId) -> Option<ImportId> {
        self.imports.get(id.as_usize()).copied()
    }
    /// The merged id of `src` obligation `id` (`None` when proof state was
    /// not carried).
    #[must_use]
    pub fn proof(&self, id: ProofId) -> Option<ProofId> {
        self.proofs.get(&id).copied()
    }
    /// The merged index of `src` source file `index`. A module with an empty
    /// file table has no file `index`: its spans are file-less, and land on
    /// the placeholder entry when the merged image has a table.
    #[must_use]
    pub fn file(&self, index: u32) -> Option<u32> {
        self.file_indices.get(index as usize).copied()
    }
    /// How many functions of `src` carried a `source_provenance` the merger
    /// dropped (F-078: the seal hashes the containing module).
    #[must_use]
    pub fn dropped_provenance(&self) -> usize {
        self.dropped_provenance
    }
    /// How many functions of `src` carried codegen-license EVIDENCE
    /// (`BodyGate::Gated { evidence: Some(..) }`, wire v61) the merger
    /// dropped, keeping the license and its authority. The evidence cites an
    /// obligation by `src`'s id and the digest of a body whose function and
    /// type ids the merge renumbers, so it cannot hold in the image as
    /// written, and a merger re-stamping it would vouch for a license it did
    /// not check (re-mint it against the merged image).
    #[must_use]
    pub fn dropped_gate_evidence(&self) -> usize {
        self.dropped_gate_evidence
    }
    /// The proof state stripped from `src` (see [`StrippedProofState`]).
    #[must_use]
    pub fn stripped(&self) -> StrippedProofState {
        self.stripped
    }
    /// How many `Partial` completeness rows (of either side) named a symbol
    /// the merged image defines, and were dropped.
    #[must_use]
    pub fn resolved_unlowered(&self) -> usize {
        self.resolved_unlowered
    }
}

/// Merge `src` into `dst` under `policy`; see the module docs for the rules.
///
/// # Errors
///
/// A [`MergeError`]; `dst` is then unchanged.
pub fn merge_into(
    dst: &mut Module,
    src: &Module,
    policy: &MergePolicy,
) -> Result<Remap, MergeError> {
    let staged = Merger::new(dst, src, *policy)?.run()?;
    Ok(staged.commit(dst))
}

/// Ordinary canonical merge plus additional types in `src`'s namespace.
///
/// Roots use the existing exhaustive mapper AFTER all source tables have their
/// canonical placements. They add no signature, function, table row or licence;
/// the output module is exactly the ordinary merge's output. The source and
/// root values remain immutable. As with `merge_into`, whole-module validation
/// of the result is still required by its consumer. `dst` is unchanged on error.
pub fn merge_into_with_roots(
    dst: &mut Module,
    src: &Module,
    policy: &MergePolicy,
    roots: &[Ty],
) -> Result<(Remap, Vec<Ty>), MergeError> {
    let errors = crate::validate::validate_type_roots(src, roots);
    if !errors.is_empty() {
        return Err(MergeError::InvalidTypeRoots { errors });
    }
    let (staged, roots) = Merger::new(dst, src, *policy)?.run_with_roots(roots)?;
    Ok((staged.commit(dst), roots))
}

/// The reserved Trust disclosures whose rows bind NO module-local id, so the
/// merge may carry them across a relocation: the deferred-verification
/// notice is one crate-level sentence ("MUST NOT be treated as
/// borrow-checked"), and dropping it would LOSE that caveat. Every other
/// name of [`RESERVED_TRUST_INTERNAL_SPEC_MODULES`] is id-binding by default.
pub const ID_FREE_DISCLOSURES: &[&str] = &["@trust-internal::deferred-verification-disclosure-v1"];

// ---------------------------------------------------------------------------
// Internals
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, Copy)]
enum Memo<T> {
    Unvisited,
    /// Being remapped; references during the remap resolve to this id (the
    /// row's fresh id, or the candidate a tentative match assumes).
    Visiting(T),
    Done(T),
}

#[derive(Debug, Clone, Copy)]
enum Undo {
    Ty(usize),
    FuncTy(usize),
    Closure(usize),
    Struct(usize),
    Enum(usize),
    Record(usize),
}

fn checked_id<I: TypedId>(base: u32, offset: u64, table: &'static str) -> Result<I, MergeError> {
    u64::from(base)
        .checked_add(offset)
        .and_then(|raw| u32::try_from(raw).ok())
        .map(I::from_index)
        .ok_or(MergeError::IdSpaceExhausted { table })
}

fn file_index(base: u32, offset: usize) -> Result<u32, MergeError> {
    u32::try_from(offset)
        .ok()
        .and_then(|offset| base.checked_add(offset))
        .ok_or(MergeError::IdSpaceExhausted { table: "files" })
}

fn len_u32(len: usize, table: &'static str) -> Result<u32, MergeError> {
    u32::try_from(len).map_err(|_| MergeError::IdSpaceExhausted { table })
}

/// One past the highest id in use (0 for an empty table).
fn next_after(ids: impl Iterator<Item = u32>, table: &'static str) -> Result<u32, MergeError> {
    match ids.max() {
        None => Ok(0),
        Some(max) => max
            .checked_add(1)
            .ok_or(MergeError::IdSpaceExhausted { table }),
    }
}

/// Structural equality without allocating diagnostic strings. Nested
/// `Constant`s retain their bit-exact float equality, including NaN payloads.
fn same<T: PartialEq>(a: &T, b: &T) -> bool {
    a == b
}

/// Explicit-id table position index, refusing a duplicate id.
fn position_index<I: TypedId + Eq + std::hash::Hash>(
    ids: impl Iterator<Item = I>,
    table: &'static str,
) -> Result<HashMap<I, usize>, MergeError> {
    let mut map = HashMap::new();
    for (position, id) in ids.enumerate() {
        if map.insert(id, position).is_some() {
            return Err(MergeError::Malformed {
                table,
                id: id.index(),
                detail: "two rows carry this id",
            });
        }
    }
    Ok(map)
}

/// How `src` spans map onto the merged file table.
#[derive(Debug, Clone)]
enum FileMap {
    /// Both sides file-less (or `src` carries no span): spans unchanged.
    Unchanged,
    /// `src` is file-less and the merged image has a table: every `src` span
    /// lands on the placeholder entry.
    Placeholder(u32),
    /// `src` has a table: index `i` maps to `map[i]`.
    Table(Vec<u32>),
}

/// The pending edit to an existing `dst` function or a staged one.
enum Resolution {
    /// The existing entry stands; the incoming one equals it.
    KeepExisting,
    /// The existing entry stands; the incoming DECLARATION is superseded
    /// (by a definition, or by an earlier declaration under
    /// [`DuplicateDecl::FirstStands`]) and its other fields are dropped.
    Supersede,
    /// The incoming definition supersedes the existing declaration.
    Replace,
}

struct Merger<'a> {
    dst: &'a Module,
    src: &'a Module,
    policy: MergePolicy,

    ty_base: u32,
    functy_base: u32,
    closure_base: u32,
    struct_base: u32,
    enum_base: u32,
    record_base: u32,
    function_base: u32,

    src_struct_pos: HashMap<StructId, usize>,
    src_enum_pos: HashMap<EnumId, usize>,
    src_record_pos: HashMap<RecordId, usize>,

    ty_memo: Vec<Memo<TyId>>,
    functy_memo: Vec<Memo<FuncTyId>>,
    closure_memo: Vec<Memo<ClosureTyId>>,
    struct_memo: Vec<Memo<StructId>>,
    enum_memo: Vec<Memo<EnumId>>,
    record_memo: Vec<Memo<RecordId>>,
    journal: Vec<Undo>,

    ty_out: Vec<Option<Ty>>,
    functy_out: Vec<Option<FuncTy>>,
    closure_out: Vec<Option<ClosureTy>>,
    struct_out: Vec<Option<StructDef>>,
    enum_out: Vec<Option<EnumDef>>,
    record_out: Vec<Option<RecordDef>>,

    dst_ty_index: HashMap<&'a Ty, TyId>,
    dst_functy_index: HashMap<&'a [Ty], Vec<FuncTyId>>,
    dst_structs_by_name: HashMap<&'a str, Vec<usize>>,
    dst_enums_by_name: HashMap<&'a str, Vec<usize>>,
    dst_records_by_name: HashMap<&'a str, Vec<usize>>,

    univ_map: Vec<UnivId>,
    pred_map: Vec<PredId>,
    interned: Module,
    import_map: Option<Vec<ImportId>>,
    file_map: FileMap,
    // Only immutable retained-input custody may select an existing file row.
    // The ordinary entry point leaves this absent and remains structural.
    retained_files: Option<Vec<Option<u32>>>,
    new_files: Vec<String>,
    rewrite_dst_spans_to: Option<u32>,
    func_map: HashMap<FuncId, FuncId>,
    src_stored_closures: std::collections::BTreeSet<ClosureTyId>,
    dst_stored_closures: std::collections::BTreeSet<ClosureTyId>,
    global_map: Vec<GlobalId>,
    proof_map: HashMap<ProofId, ProofId>,

    dropped_provenance: usize,
    dropped_gate_evidence: usize,
    stripped: StrippedProofState,
}

/// Everything a successful merge writes into `dst`.
struct Staged {
    remap: Remap,
    appended_files: Vec<String>,
    rewrite_dst_spans_to: Option<u32>,
    universes: Vec<trust_ir::Universe>,
    predicates: Vec<Pred>,
    imports: Vec<trust_ir::ModuleImport>,
    types: Vec<Ty>,
    func_types: Vec<FuncTy>,
    closure_types: Vec<ClosureTy>,
    structs: Vec<StructDef>,
    enums: Vec<EnumDef>,
    records: Vec<RecordDef>,
    globals: Vec<Global>,
    replaced_functions: Vec<(usize, Function)>,
    functions: Vec<Function>,
    proof_obligations: Vec<ProofObligation>,
    proof_certificates: Vec<ProofCertificate>,
    obligation_diagnostics: Vec<ObligationDiagnostic>,
    spec_modules: Vec<SpecModule>,
    tuple_layouts: Vec<TupleLayoutDescriptor>,
    closure_layouts: Vec<ClosureLayoutDescriptor>,
    global_asm: Vec<String>,
    completeness: Option<ModuleCompleteness>,
    target_info: Option<trust_ir::TargetInfo>,
    /// The WHOLE merged drop-glue table (`dst`'s rows and `src`'s, in the
    /// one canonical order), replacing `dst`'s on commit.
    drop_glue: Vec<DropGlueEntry>,
    /// The WHOLE merged blob table (the union of `dst`'s rows and `src`'s by
    /// digest, in the one canonical order), replacing `dst`'s on commit.
    blobs: Vec<trust_ir::blob::Blob>,
}

impl<'a> Merger<'a> {
    fn new(dst: &'a Module, src: &'a Module, policy: MergePolicy) -> Result<Self, MergeError> {
        let mut dst_ty_index = HashMap::new();
        for (i, ty) in dst.types.iter().enumerate() {
            dst_ty_index
                .entry(ty)
                .or_insert(TyId::new(len_u32(i, "types")?));
        }
        let mut dst_functy_index: HashMap<&'a [Ty], Vec<FuncTyId>> = HashMap::new();
        for (i, ft) in dst.func_types.iter().enumerate() {
            dst_functy_index
                .entry(ft.params.as_slice())
                .or_default()
                .push(FuncTyId::new(len_u32(i, "func_types")?));
        }
        let mut dst_structs_by_name: HashMap<&'a str, Vec<usize>> = HashMap::new();
        for (i, def) in dst.structs.iter().enumerate() {
            dst_structs_by_name
                .entry(def.name.as_str())
                .or_default()
                .push(i);
        }
        let mut dst_enums_by_name: HashMap<&'a str, Vec<usize>> = HashMap::new();
        for (i, def) in dst.enums.iter().enumerate() {
            dst_enums_by_name
                .entry(def.name.as_str())
                .or_default()
                .push(i);
        }
        let mut dst_records_by_name: HashMap<&'a str, Vec<usize>> = HashMap::new();
        for (i, def) in dst.records.iter().enumerate() {
            dst_records_by_name
                .entry(def.name.as_str())
                .or_default()
                .push(i);
        }
        let mut interned = Module::new("");
        interned.universes = dst.universes.clone();
        interned.predicates = dst.predicates.clone();
        interned.imports = dst.imports.clone();
        Ok(Self {
            dst,
            src,
            policy,
            ty_base: len_u32(dst.types.len(), "types")?,
            functy_base: len_u32(dst.func_types.len(), "func_types")?,
            closure_base: len_u32(dst.closure_types.len(), "closure_types")?,
            struct_base: next_after(dst.structs.iter().map(|d| d.id.index()), "structs")?,
            enum_base: next_after(dst.enums.iter().map(|d| d.id.index()), "enums")?,
            record_base: next_after(dst.records.iter().map(|d| d.id.index()), "records")?,
            function_base: next_after(dst.functions.iter().map(|f| f.id.index()), "functions")?
                .max(len_u32(dst.functions.len(), "functions")?),
            src_struct_pos: position_index(src.structs.iter().map(|d| d.id), "structs")?,
            src_enum_pos: position_index(src.enums.iter().map(|d| d.id), "enums")?,
            src_record_pos: position_index(src.records.iter().map(|d| d.id), "records")?,
            ty_memo: vec![Memo::Unvisited; src.types.len()],
            functy_memo: vec![Memo::Unvisited; src.func_types.len()],
            closure_memo: vec![Memo::Unvisited; src.closure_types.len()],
            struct_memo: vec![Memo::Unvisited; src.structs.len()],
            enum_memo: vec![Memo::Unvisited; src.enums.len()],
            record_memo: vec![Memo::Unvisited; src.records.len()],
            journal: Vec::new(),
            ty_out: vec![None; src.types.len()],
            functy_out: vec![None; src.func_types.len()],
            closure_out: vec![None; src.closure_types.len()],
            struct_out: vec![None; src.structs.len()],
            enum_out: vec![None; src.enums.len()],
            record_out: vec![None; src.records.len()],
            dst_ty_index,
            dst_functy_index,
            dst_structs_by_name,
            dst_enums_by_name,
            dst_records_by_name,
            univ_map: Vec::new(),
            pred_map: Vec::new(),
            interned,
            import_map: None,
            file_map: FileMap::Unchanged,
            retained_files: None,
            new_files: Vec::new(),
            rewrite_dst_spans_to: None,
            func_map: HashMap::new(),
            src_stored_closures: src.closure_storage_types(),
            dst_stored_closures: dst.closure_storage_types(),
            global_map: Vec::new(),
            proof_map: HashMap::new(),
            dropped_provenance: 0,
            dropped_gate_evidence: 0,
            stripped: StrippedProofState::default(),
        })
    }

    fn run(self) -> Result<Staged, MergeError> {
        self.run_with_roots(&[]).map(|(staged, _)| staged)
    }

    fn run_with_roots(mut self, roots: &[Ty]) -> Result<(Staged, Vec<Ty>), MergeError> {
        // The exhaustive module destructure: a new `Module` field is a
        // compile error until it is merged below.
        let Module {
            name: _,
            functions,
            structs,
            enums,
            records,
            closure_types,
            globals,
            func_types,
            types,
            proof_obligations,
            proof_certificates,
            target_info,
            files,
            obligation_diagnostics,
            spec_modules,
            universes,
            predicates,
            global_asm,
            imports,
            tuple_layouts,
            completeness,
            drop_glue,
            closure_layouts,
            blobs,
        } = self.src;

        let target_info = self.merge_target(target_info.as_ref())?;
        self.map_files(files)?;
        self.map_universes(universes)?;
        self.map_predicates(predicates)?;
        self.map_imports(imports)?;
        self.assign_function_ids(functions)?;
        if self.policy.carry_proof_state {
            self.assign_proof_ids(proof_obligations)?;
        }

        // Type tables, eagerly and in `src` order. A tentative nominal match
        // that fails rolls back only rows it touched while they were
        // unvisited, which the remaining passes then redo.
        for i in 0..types.len() {
            self.ty_id(TyId::new(len_u32(i, "types")?))?;
        }
        for i in 0..func_types.len() {
            self.functy_id(FuncTyId::new(len_u32(i, "func_types")?))?;
        }
        for i in 0..closure_types.len() {
            self.closure_id(ClosureTyId::new(len_u32(i, "closure_types")?))?;
        }
        for def in structs {
            self.struct_id(def.id)?;
        }
        for def in enums {
            self.enum_id(def.id)?;
        }
        for def in records {
            self.record_id(def.id)?;
        }
        debug_assert!(self.journal_is_settled());
        self.journal.clear();

        let staged_globals = self.merge_globals(globals)?;
        let (replaced_functions, new_functions) = self.merge_functions(functions)?;
        self.guard_id_binding_disclosures(spec_modules, &replaced_functions, &new_functions)?;

        let (obligations, certificates, diagnostics, specs) = if self.policy.carry_proof_state {
            (
                self.remap_obligations(proof_obligations)?,
                self.remap_certificates(proof_certificates)?,
                self.remap_diagnostics(obligation_diagnostics)?,
                self.remap_spec_modules(spec_modules)?,
            )
        } else {
            self.stripped.obligations += proof_obligations.len();
            self.stripped.certificates += proof_certificates.len();
            self.stripped.diagnostics += obligation_diagnostics.len();
            self.stripped.spec_modules += spec_modules.len();
            (Vec::new(), Vec::new(), Vec::new(), Vec::new())
        };

        let layouts = self.merge_tuple_layouts(tuple_layouts)?;
        let closure_layouts = self.merge_closure_layouts(closure_layouts)?;
        let drop_glue = self.merge_drop_glue(drop_glue)?;
        let blobs = self.merge_blobs(blobs)?;
        let (completeness, resolved_unlowered) = self.merge_completeness(completeness.as_ref());

        // Every source table was mapped eagerly in its original order. Extra
        // inline roots now use those final placements; they cannot seed a
        // different table allocation order or introduce a synthetic carrier.
        let roots = self.tys(roots)?;
        if !self.journal_is_settled() {
            return Err(MergeError::Malformed {
                table: "extra type roots",
                id: 0,
                detail: "canonical source placement is not complete",
            });
        }
        let staged = self.finish(
            target_info,
            staged_globals,
            replaced_functions,
            new_functions,
            obligations,
            certificates,
            diagnostics,
            specs,
            layouts,
            closure_layouts,
            global_asm.clone(),
            completeness,
            resolved_unlowered,
            drop_glue,
            blobs,
        )?;
        Ok((staged, roots))
    }

    fn journal_is_settled(&self) -> bool {
        self.ty_memo.iter().all(|m| matches!(m, Memo::Done(_)))
            && self.functy_memo.iter().all(|m| matches!(m, Memo::Done(_)))
            && self.closure_memo.iter().all(|m| matches!(m, Memo::Done(_)))
            && self.struct_memo.iter().all(|m| matches!(m, Memo::Done(_)))
            && self.enum_memo.iter().all(|m| matches!(m, Memo::Done(_)))
            && self.record_memo.iter().all(|m| matches!(m, Memo::Done(_)))
    }

    // -- module-level scalars ------------------------------------------------

    fn merge_target(
        &self,
        src: Option<&trust_ir::TargetInfo>,
    ) -> Result<Option<trust_ir::TargetInfo>, MergeError> {
        match (&self.dst.target_info, src) {
            (Some(d), Some(s)) if d != s => Err(MergeError::TargetMismatch {
                dst: format!("{d:?}"),
                src: format!("{s:?}"),
            }),
            (None, Some(s)) => Ok(Some(s.clone())),
            (d, _) => Ok(d.clone()),
        }
    }

    // -- files ---------------------------------------------------------------

    /// Extend the file table STRUCTURALLY (see the module docs): rows are
    /// appended — `src`'s whole table in order, plus a placeholder `""` for a
    /// file-less side's spans when the image gains a table — and no path
    /// string of either side is read or compared. Only the two tables'
    /// lengths and the presence of spans decide the ordinary result. The
    /// private retained-input path can reuse a row only after replaying its
    /// actual immutable original-input/canonical-placement history.
    fn map_files(&mut self, files: &[String]) -> Result<(), MergeError> {
        let dst_fileless = self.dst.files.is_empty();
        let base = len_u32(self.dst.files.len(), "files")?;
        let mut appended: Vec<String> = Vec::new();
        if files.is_empty() {
            if !dst_fileless && module_has_spans(self.src) {
                self.file_map = FileMap::Placeholder(file_index(base, 0)?);
                appended.push(String::new());
            }
        } else {
            if dst_fileless && module_has_spans(self.dst) {
                self.rewrite_dst_spans_to = Some(file_index(base, 0)?);
                appended.push(String::new());
            }
            let mut map = Vec::with_capacity(files.len());
            for (i, file) in files.iter().enumerate() {
                let retained = self
                    .retained_files
                    .as_ref()
                    .and_then(|rows| rows.get(i))
                    .copied()
                    .flatten();
                if let Some(id) = retained {
                    if id >= base {
                        return Err(MergeError::Dangling {
                            table: "retained files",
                            id,
                        });
                    }
                    map.push(id);
                } else {
                    map.push(file_index(base, appended.len())?);
                    appended.push(file.clone());
                }
            }
            self.file_map = FileMap::Table(map);
        }
        self.new_files = appended;
        Ok(())
    }

    fn span(&self, span: &SourceSpan) -> Result<SourceSpan, MergeError> {
        let SourceSpan { file, line, col } = *span;
        let file = match &self.file_map {
            FileMap::Unchanged => file,
            FileMap::Placeholder(p) => *p,
            FileMap::Table(map) => *map.get(file as usize).ok_or(MergeError::Dangling {
                table: "files",
                id: file,
            })?,
        };
        Ok(SourceSpan { file, line, col })
    }

    // -- content-interned tables ---------------------------------------------

    fn map_universes(&mut self, universes: &[trust_ir::Universe]) -> Result<(), MergeError> {
        for (i, universe) in universes.iter().enumerate() {
            let id = len_u32(i, "universes")?;
            if !universe.is_canonical() {
                return Err(MergeError::Malformed {
                    table: "universes",
                    id,
                    detail: "not canonical",
                });
            }
            if universes[..i].contains(universe) {
                return Err(MergeError::Malformed {
                    table: "universes",
                    id,
                    detail: "the table is not content-interned",
                });
            }
            let mapped = self
                .interned
                .intern_universe(universe.clone())
                .map_err(|_| MergeError::IdSpaceExhausted { table: "universes" })?
                .ok_or(MergeError::Malformed {
                    table: "universes",
                    id,
                    detail: "cannot be interned",
                })?;
            self.univ_map.push(mapped);
        }
        Ok(())
    }

    fn map_predicates(&mut self, predicates: &[Pred]) -> Result<(), MergeError> {
        for (i, pred) in predicates.iter().enumerate() {
            let id = len_u32(i, "predicates")?;
            if !pred.is_canonical() {
                return Err(MergeError::Malformed {
                    table: "predicates",
                    id,
                    detail: "not canonical",
                });
            }
            if predicates[..i].contains(pred) {
                return Err(MergeError::Malformed {
                    table: "predicates",
                    id,
                    detail: "the table is not content-interned",
                });
            }
            let child = |c: &PredId, map: &[PredId]| -> Result<PredId, MergeError> {
                if c.as_usize() >= i {
                    return Err(MergeError::Malformed {
                        table: "predicates",
                        id,
                        detail: "a connective cites a non-antecedent predicate",
                    });
                }
                Ok(map[c.as_usize()])
            };
            let remapped = match pred {
                Pred::Interval { lo, hi } => Pred::Interval { lo: *lo, hi: *hi },
                Pred::FiniteSet(items) => Pred::FiniteSet(items.clone()),
                Pred::InUniverse(u, space) => Pred::InUniverse(
                    *self
                        .univ_map
                        .get(u.as_usize())
                        .ok_or(MergeError::Dangling {
                            table: "universes",
                            id: u.index(),
                        })?,
                    *space,
                ),
                Pred::NonZero => Pred::NonZero,
                Pred::NonNull => Pred::NonNull,
                Pred::Conj(children) => Pred::Conj(
                    children
                        .iter()
                        .map(|c| child(c, &self.pred_map))
                        .collect::<Result<_, _>>()?,
                ),
                Pred::Disj(children) => Pred::Disj(
                    children
                        .iter()
                        .map(|c| child(c, &self.pred_map))
                        .collect::<Result<_, _>>()?,
                ),
                Pred::Top => Pred::Top,
                Pred::Bottom => Pred::Bottom,
            };
            let mapped = self
                .interned
                .intern_pred(remapped)
                .map_err(|_| MergeError::IdSpaceExhausted {
                    table: "predicates",
                })?
                .ok_or(MergeError::Malformed {
                    table: "predicates",
                    id,
                    detail: "cannot be interned",
                })?;
            self.pred_map.push(mapped);
        }
        Ok(())
    }

    fn map_imports(&mut self, imports: &[trust_ir::ModuleImport]) -> Result<(), MergeError> {
        if !self.policy.carry_imports {
            self.stripped.imports += imports.len();
            return Ok(());
        }
        let mut map = Vec::with_capacity(imports.len());
        for (i, row) in imports.iter().enumerate() {
            if imports[..i].contains(row) {
                return Err(MergeError::Malformed {
                    table: "imports",
                    id: len_u32(i, "imports")?,
                    detail: "the table is not content-interned",
                });
            }
            map.push(
                self.interned
                    .intern_import(row.clone())
                    .map_err(|_| MergeError::IdSpaceExhausted { table: "imports" })?,
            );
        }
        self.import_map = Some(map);
        Ok(())
    }

    fn import(
        &self,
        id: ImportId,
        location: impl FnOnce() -> String,
    ) -> Result<ImportId, MergeError> {
        let Some(map) = &self.import_map else {
            return Err(MergeError::ImportsNotCarried {
                location: location(),
            });
        };
        map.get(id.as_usize()).copied().ok_or(MergeError::Dangling {
            table: "imports",
            id: id.index(),
        })
    }

    fn extern_ref(
        &self,
        r: &ExternRef,
        location: impl FnOnce() -> String,
    ) -> Result<ExternRef, MergeError> {
        let ExternRef {
            module,
            symbol,
            obligation,
        } = r;
        Ok(ExternRef {
            module: self.import(*module, location)?,
            symbol: symbol.clone(),
            // The far module's id space: never remapped here.
            obligation: *obligation,
        })
    }

    // -- id assignment ---------------------------------------------------------

    fn assign_function_ids(&mut self, functions: &[Function]) -> Result<(), MergeError> {
        let mut by_name: HashMap<&str, FuncId> = HashMap::new();
        for f in &self.dst.functions {
            by_name.entry(f.name.as_str()).or_insert(f.id);
        }
        let mut next = self.function_base;
        let mut seen = HashSet::new();
        // New ids are dense, handed out in `src` ID order, so a module whose
        // ids are a permutation of `0..n` keeps them under the identity merge.
        let mut by_id: Vec<&Function> = functions.iter().collect();
        by_id.sort_by_key(|f| f.id.index());
        for f in by_id {
            if !seen.insert(f.id) {
                return Err(MergeError::Malformed {
                    table: "functions",
                    id: f.id.index(),
                    detail: "two rows carry this id",
                });
            }
            let id = match by_name.get(f.name.as_str()) {
                Some(id) => *id,
                None => {
                    let id = FuncId::new(next);
                    next = next
                        .checked_add(1)
                        .ok_or(MergeError::IdSpaceExhausted { table: "functions" })?;
                    by_name.insert(f.name.as_str(), id);
                    id
                }
            };
            self.func_map.insert(f.id, id);
        }
        Ok(())
    }

    fn func(&self, id: FuncId) -> Result<FuncId, MergeError> {
        self.func_map.get(&id).copied().ok_or(MergeError::Dangling {
            table: "functions",
            id: id.index(),
        })
    }

    fn assign_proof_ids(&mut self, obligations: &[ProofObligation]) -> Result<(), MergeError> {
        let base = next_after(
            self.dst.proof_obligations.iter().map(|o| o.id.index()),
            "proof_obligations",
        )?;
        for o in obligations {
            let mapped = checked_id::<ProofId>(base, u64::from(o.id.index()), "proof_obligations")?;
            if self.proof_map.insert(o.id, mapped).is_some() {
                return Err(MergeError::Malformed {
                    table: "proof_obligations",
                    id: o.id.index(),
                    detail: "two rows carry this id",
                });
            }
        }
        Ok(())
    }

    fn proof(&self, id: ProofId) -> Result<ProofId, MergeError> {
        self.proof_map
            .get(&id)
            .copied()
            .ok_or(MergeError::Dangling {
                table: "proof_obligations",
                id: id.index(),
            })
    }

    // -- the tentative-match journal -------------------------------------------

    fn mark(&self) -> usize {
        self.journal.len()
    }

    fn rollback(&mut self, mark: usize) {
        while self.journal.len() > mark {
            match self.journal.pop().expect("journal entries above the mark") {
                Undo::Ty(i) => {
                    self.ty_memo[i] = Memo::Unvisited;
                    self.ty_out[i] = None;
                }
                Undo::FuncTy(i) => {
                    self.functy_memo[i] = Memo::Unvisited;
                    self.functy_out[i] = None;
                }
                Undo::Closure(i) => {
                    self.closure_memo[i] = Memo::Unvisited;
                    self.closure_out[i] = None;
                }
                Undo::Struct(i) => {
                    self.struct_memo[i] = Memo::Unvisited;
                    self.struct_out[i] = None;
                }
                Undo::Enum(i) => {
                    self.enum_memo[i] = Memo::Unvisited;
                    self.enum_out[i] = None;
                }
                Undo::Record(i) => {
                    self.record_memo[i] = Memo::Unvisited;
                    self.record_out[i] = None;
                }
            }
        }
    }

    // -- "is this id one this merge appends?" ----------------------------------

    fn ty_is_fresh(&self, ty: &Ty) -> bool {
        match ty {
            Ty::Storage(_) => true,
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
            | Ty::Isize
            | Ty::Usize
            | Ty::Char
            | Ty::Error
            | Ty::F16
            | Ty::F32
            | Ty::F64
            | Ty::Bool
            | Ty::Ptr
            | Ty::Unit
            | Ty::Never
            | Ty::Dialect(_)
            | Ty::Handle(_) => false,
            // Level R has no extension: `NoExt` is uninhabited.
            Ty::Ext(e) => e.unreachable(),
            Ty::Vector(elem, _) => self.ty_is_fresh(elem),
            // The tensor region: the element is an inline child.
            Ty::Tensor(elem, _) => self.ty_is_fresh(elem),
            Ty::FatPtr(kind) => match kind {
                FatPtrKind::Slice(elem) => elem.index() >= self.ty_base,
                FatPtrKind::Str
                | FatPtrKind::TraitObject { .. }
                | FatPtrKind::ContainerLen
                | FatPtrKind::ContainerVtable => false,
            },
            Ty::Struct(id) => id.index() >= self.struct_base,
            Ty::Enum(id) => id.index() >= self.enum_base,
            Ty::Record(id) => id.index() >= self.record_base,
            Ty::Closure(id) => id.index() >= self.closure_base,
            Ty::Func(id) => id.index() >= self.functy_base,
            Ty::FnItem(id) => id.index() >= self.function_base,
            Ty::Array(elem, _) | Ty::Set(elem, _) | Ty::Sequence(elem) => {
                elem.index() >= self.ty_base
            }
            Ty::Refine(base, _) => base.index() >= self.ty_base,
            Ty::Tuple(elems) => elems.iter().any(|t| self.ty_is_fresh(t)),
            Ty::Ref(inner)
            | Ty::RefMut(inner)
            | Ty::PtrConst(inner)
            | Ty::PtrMut(inner)
            | Ty::Rc(inner) => self.ty_is_fresh(inner),
        }
    }

    fn tys_are_fresh(&self, tys: &[Ty]) -> bool {
        tys.iter().any(|t| self.ty_is_fresh(t))
    }

    // -- positional rows -------------------------------------------------------

    fn ty_id(&mut self, id: TyId) -> Result<TyId, MergeError> {
        let i = id.as_usize();
        match self.ty_memo.get(i) {
            Some(Memo::Done(m) | Memo::Visiting(m)) => return Ok(*m),
            Some(Memo::Unvisited) => {}
            None => {
                return Err(MergeError::Dangling {
                    table: "types",
                    id: id.index(),
                });
            }
        }
        let fresh = checked_id::<TyId>(self.ty_base, i as u64, "types")?;
        self.ty_memo[i] = Memo::Visiting(fresh);
        self.journal.push(Undo::Ty(i));
        let src = self.src;
        let row = self.ty(&src.types[i])?;
        let mapped = if self.ty_is_fresh(&row) {
            fresh
        } else {
            self.dst_ty_index.get(&row).copied().unwrap_or(fresh)
        };
        self.ty_out[i] = Some(row);
        self.ty_memo[i] = Memo::Done(mapped);
        Ok(mapped)
    }

    fn functy_id(&mut self, id: FuncTyId) -> Result<FuncTyId, MergeError> {
        let i = id.as_usize();
        match self.functy_memo.get(i) {
            Some(Memo::Done(m) | Memo::Visiting(m)) => return Ok(*m),
            Some(Memo::Unvisited) => {}
            None => {
                return Err(MergeError::Dangling {
                    table: "func_types",
                    id: id.index(),
                });
            }
        }
        let fresh = checked_id::<FuncTyId>(self.functy_base, i as u64, "func_types")?;
        self.functy_memo[i] = Memo::Visiting(fresh);
        self.journal.push(Undo::FuncTy(i));
        let src = self.src;
        let FuncTy {
            params,
            returns,
            abi,
            is_vararg,
        } = &src.func_types[i];
        let row = FuncTy {
            abi: abi.clone(),
            params: self.tys(params)?,
            returns: self.tys(returns)?,
            is_vararg: *is_vararg,
        };
        let mapped = if self.tys_are_fresh(&row.params) || self.tys_are_fresh(&row.returns) {
            fresh
        } else {
            self.dst_functy_index
                .get(row.params.as_slice())
                .and_then(|candidates| {
                    candidates
                        .iter()
                        .copied()
                        .find(|c| self.dst.func_types[c.as_usize()] == row)
                })
                .unwrap_or(fresh)
        };
        self.functy_out[i] = Some(row);
        self.functy_memo[i] = Memo::Done(mapped);
        Ok(mapped)
    }

    /// Closure types are unnamed nominal rows: a tentative match against
    /// every pre-existing `dst` closure type of the same shape, else fresh.
    fn closure_id(&mut self, id: ClosureTyId) -> Result<ClosureTyId, MergeError> {
        let i = id.as_usize();
        match self.closure_memo.get(i) {
            Some(Memo::Done(m) | Memo::Visiting(m)) => return Ok(*m),
            Some(Memo::Unvisited) => {}
            None => {
                return Err(MergeError::Dangling {
                    table: "closure_types",
                    id: id.index(),
                });
            }
        }
        let (src, dst) = (self.src, self.dst);
        let def = &src.closure_types[i];
        for (pos, candidate) in dst.closure_types.iter().enumerate() {
            if candidate.captures.len() != def.captures.len() {
                continue;
            }
            let assumed = ClosureTyId::new(len_u32(pos, "closure_types")?);
            let source_origin = src
                .closure_layout_descriptor(id)
                .map_err(|_| MergeError::Malformed {
                    table: "closure_layouts",
                    id: id.index(),
                    detail: "invalid source descriptor",
                })?
                .and_then(|row| row.origin.as_ref());
            let destination_origin = dst
                .closure_layout_descriptor(assumed)
                .map_err(|_| MergeError::Malformed {
                    table: "closure_layouts",
                    id: assumed.index(),
                    detail: "invalid destination descriptor",
                })?
                .and_then(|row| row.origin.as_ref());
            if source_origin != destination_origin {
                continue;
            }
            // Capture-only storage has a statically checked target. Equal
            // shape alone must not merge two distinct callable environments.
            if self.src_stored_closures.contains(&id) || self.dst_stored_closures.contains(&assumed)
            {
                let compatible = match (
                    src.closure_storage_binding(id),
                    dst.closure_storage_binding(assumed),
                ) {
                    (Ok(source), Ok(destination)) => {
                        self.func(source.target)? == destination.target
                            && source.layout.size == destination.layout.size
                            && source.layout.align == destination.layout.align
                            && source.layout.capture_offsets == destination.layout.capture_offsets
                    }
                    _ => false,
                };
                if !compatible {
                    continue;
                }
            }
            let mark = self.mark();
            self.closure_memo[i] = Memo::Visiting(assumed);
            self.journal.push(Undo::Closure(i));
            let row = self.closure_row(def)?;
            if row == *candidate && !self.closure_is_fresh(&row) {
                self.closure_out[i] = Some(row);
                self.closure_memo[i] = Memo::Done(assumed);
                return Ok(assumed);
            }
            self.rollback(mark);
        }
        let fresh = checked_id::<ClosureTyId>(self.closure_base, i as u64, "closure_types")?;
        self.closure_memo[i] = Memo::Visiting(fresh);
        self.journal.push(Undo::Closure(i));
        let row = self.closure_row(def)?;
        self.closure_out[i] = Some(row);
        self.closure_memo[i] = Memo::Done(fresh);
        Ok(fresh)
    }

    fn closure_row(&mut self, def: &ClosureTy) -> Result<ClosureTy, MergeError> {
        let ClosureTy { func, captures } = def;
        Ok(ClosureTy {
            func: self.functy_id(*func)?,
            captures: self.tys(captures)?,
        })
    }

    fn closure_is_fresh(&self, row: &ClosureTy) -> bool {
        row.func.index() >= self.functy_base || self.tys_are_fresh(&row.captures)
    }

    // -- nominal named definitions ---------------------------------------------

    fn struct_id(&mut self, id: StructId) -> Result<StructId, MergeError> {
        let Some(&i) = self.src_struct_pos.get(&id) else {
            return Err(MergeError::Dangling {
                table: "structs",
                id: id.index(),
            });
        };
        match self.struct_memo[i] {
            Memo::Done(m) | Memo::Visiting(m) => return Ok(m),
            Memo::Unvisited => {}
        }
        let (src, dst) = (self.src, self.dst);
        let def = &src.structs[i];
        let candidates = self
            .dst_structs_by_name
            .get(def.name.as_str())
            .cloned()
            .unwrap_or_default();
        for pos in candidates {
            let candidate = &dst.structs[pos];
            let mark = self.mark();
            self.struct_memo[i] = Memo::Visiting(candidate.id);
            self.journal.push(Undo::Struct(i));
            let row = self.struct_row(def, candidate.id)?;
            if row == *candidate && !self.struct_is_fresh(&row) {
                self.struct_out[i] = Some(row);
                self.struct_memo[i] = Memo::Done(candidate.id);
                return Ok(candidate.id);
            }
            self.rollback(mark);
        }
        let fresh = checked_id::<StructId>(self.struct_base, u64::from(id.index()), "structs")?;
        self.struct_memo[i] = Memo::Visiting(fresh);
        self.journal.push(Undo::Struct(i));
        let row = self.struct_row(def, fresh)?;
        self.struct_out[i] = Some(row);
        self.struct_memo[i] = Memo::Done(fresh);
        Ok(fresh)
    }

    fn struct_row(&mut self, def: &StructDef, id: StructId) -> Result<StructDef, MergeError> {
        let StructDef {
            id: _,
            name,
            fields,
            size,
            align,
            repr,
            origin,
        } = def;
        Ok(StructDef {
            id,
            name: name.clone(),
            fields: self.fields(fields)?,
            size: *size,
            align: *align,
            repr: *repr,
            // Id-free (a rustc DefPathHash / Clean decl key): carried as is,
            // and part of the literal equality a `dst` match needs.
            origin: origin.clone(),
        })
    }

    fn fields(&mut self, fields: &[FieldDef]) -> Result<Vec<FieldDef>, MergeError> {
        fields
            .iter()
            .map(|field| {
                let FieldDef { name, ty, offset } = field;
                Ok(FieldDef {
                    name: name.clone(),
                    ty: self.ty(ty)?,
                    offset: *offset,
                })
            })
            .collect()
    }

    fn struct_is_fresh(&self, row: &StructDef) -> bool {
        row.fields.iter().any(|f| self.ty_is_fresh(&f.ty))
    }

    fn enum_id(&mut self, id: EnumId) -> Result<EnumId, MergeError> {
        let Some(&i) = self.src_enum_pos.get(&id) else {
            return Err(MergeError::Dangling {
                table: "enums",
                id: id.index(),
            });
        };
        match self.enum_memo[i] {
            Memo::Done(m) | Memo::Visiting(m) => return Ok(m),
            Memo::Unvisited => {}
        }
        let (src, dst) = (self.src, self.dst);
        let def = &src.enums[i];
        let candidates = self
            .dst_enums_by_name
            .get(def.name.as_str())
            .cloned()
            .unwrap_or_default();
        for pos in candidates {
            let candidate = &dst.enums[pos];
            let mark = self.mark();
            self.enum_memo[i] = Memo::Visiting(candidate.id);
            self.journal.push(Undo::Enum(i));
            let row = self.enum_row(def, candidate.id)?;
            if row == *candidate && !self.enum_is_fresh(&row) {
                self.enum_out[i] = Some(row);
                self.enum_memo[i] = Memo::Done(candidate.id);
                return Ok(candidate.id);
            }
            self.rollback(mark);
        }
        let fresh = checked_id::<EnumId>(self.enum_base, u64::from(id.index()), "enums")?;
        self.enum_memo[i] = Memo::Visiting(fresh);
        self.journal.push(Undo::Enum(i));
        let row = self.enum_row(def, fresh)?;
        self.enum_out[i] = Some(row);
        self.enum_memo[i] = Memo::Done(fresh);
        Ok(fresh)
    }

    fn enum_row(&mut self, def: &EnumDef, id: EnumId) -> Result<EnumDef, MergeError> {
        let EnumDef {
            id: _,
            name,
            variants,
            discriminants,
            repr,
            layout,
            origin,
        } = def;
        let variants = variants
            .iter()
            .map(|variant| {
                let EnumVariant {
                    name,
                    fields,
                    field_names,
                } = variant;
                Ok(EnumVariant {
                    name: name.clone(),
                    fields: self.tys(fields)?,
                    field_names: field_names.clone(),
                })
            })
            .collect::<Result<_, MergeError>>()?;
        Ok(EnumDef {
            id,
            name: name.clone(),
            variants,
            discriminants: discriminants.clone(),
            repr: *repr,
            layout: layout.clone(),
            origin: origin.clone(),
        })
    }

    fn enum_is_fresh(&self, row: &EnumDef) -> bool {
        row.variants.iter().any(|v| self.tys_are_fresh(&v.fields))
    }

    fn record_id(&mut self, id: RecordId) -> Result<RecordId, MergeError> {
        let Some(&i) = self.src_record_pos.get(&id) else {
            return Err(MergeError::Dangling {
                table: "records",
                id: id.index(),
            });
        };
        match self.record_memo[i] {
            Memo::Done(m) | Memo::Visiting(m) => return Ok(m),
            Memo::Unvisited => {}
        }
        let (src, dst) = (self.src, self.dst);
        let def = &src.records[i];
        let candidates = self
            .dst_records_by_name
            .get(def.name.as_str())
            .cloned()
            .unwrap_or_default();
        for pos in candidates {
            let candidate = &dst.records[pos];
            let mark = self.mark();
            self.record_memo[i] = Memo::Visiting(candidate.id);
            self.journal.push(Undo::Record(i));
            let row = self.record_row(def, candidate.id)?;
            if row == *candidate && !self.record_is_fresh(&row) {
                self.record_out[i] = Some(row);
                self.record_memo[i] = Memo::Done(candidate.id);
                return Ok(candidate.id);
            }
            self.rollback(mark);
        }
        let fresh = checked_id::<RecordId>(self.record_base, u64::from(id.index()), "records")?;
        self.record_memo[i] = Memo::Visiting(fresh);
        self.journal.push(Undo::Record(i));
        let row = self.record_row(def, fresh)?;
        self.record_out[i] = Some(row);
        self.record_memo[i] = Memo::Done(fresh);
        Ok(fresh)
    }

    fn record_row(&mut self, def: &RecordDef, id: RecordId) -> Result<RecordDef, MergeError> {
        let RecordDef {
            id: _,
            name,
            fields,
        } = def;
        Ok(RecordDef {
            id,
            name: name.clone(),
            fields: self.fields(fields)?,
        })
    }

    fn record_is_fresh(&self, row: &RecordDef) -> bool {
        row.fields.iter().any(|f| self.ty_is_fresh(&f.ty))
    }

    // -- inline types and constants --------------------------------------------

    fn tys(&mut self, tys: &[Ty]) -> Result<Vec<Ty>, MergeError> {
        tys.iter().map(|ty| self.ty(ty)).collect()
    }

    fn ty(&mut self, ty: &Ty) -> Result<Ty, MergeError> {
        Ok(match ty {
            Ty::Storage(layout) => Ty::Storage(*layout),
            Ty::I8 => Ty::I8,
            Ty::I16 => Ty::I16,
            Ty::I32 => Ty::I32,
            Ty::I64 => Ty::I64,
            Ty::I128 => Ty::I128,
            Ty::U8 => Ty::U8,
            Ty::U16 => Ty::U16,
            Ty::U32 => Ty::U32,
            Ty::U64 => Ty::U64,
            Ty::U128 => Ty::U128,
            Ty::Isize => Ty::Isize,
            Ty::Usize => Ty::Usize,
            Ty::Char => Ty::Char,
            Ty::Error => Ty::Error,
            Ty::F16 => Ty::F16,
            Ty::F32 => Ty::F32,
            Ty::F64 => Ty::F64,
            Ty::Bool => Ty::Bool,
            Ty::Ptr => Ty::Ptr,
            Ty::Unit => Ty::Unit,
            Ty::Never => Ty::Never,
            // Nominal by their FULL content: carried verbatim, so equal only
            // to an identical `(namespace, name, version)` /
            // `(name, runtime)` — never unified by name.
            Ty::Dialect(d) => Ty::Dialect(d.clone()),
            Ty::Handle(h) => Ty::Handle(h.clone()),
            Ty::Vector(elem, lanes) => Ty::Vector(Box::new(self.ty(elem)?), *lanes),
            // The tensor region: the element is an inline child.
            Ty::Tensor(elem, rank) => Ty::Tensor(Box::new(self.ty(elem)?), *rank),
            Ty::FatPtr(kind) => Ty::FatPtr(match kind {
                FatPtrKind::Slice(elem) => FatPtrKind::Slice(self.ty_id(*elem)?),
                FatPtrKind::Str => FatPtrKind::Str,
                // A content-derived identity (`stable_trait_object_id`), not
                // a module table index: carried verbatim.
                FatPtrKind::TraitObject { trait_id } => FatPtrKind::TraitObject {
                    trait_id: *trait_id,
                },
                FatPtrKind::ContainerLen => FatPtrKind::ContainerLen,
                FatPtrKind::ContainerVtable => FatPtrKind::ContainerVtable,
            }),
            Ty::Struct(id) => Ty::Struct(self.struct_id(*id)?),
            Ty::Array(elem, len) => Ty::Array(self.ty_id(*elem)?, *len),
            Ty::Tuple(elems) => Ty::Tuple(self.tys(elems)?),
            Ty::Enum(id) => Ty::Enum(self.enum_id(*id)?),
            Ty::Func(id) => Ty::Func(self.functy_id(*id)?),
            Ty::FnItem(id) => Ty::FnItem(self.func(*id)?),
            Ty::Ref(inner) => Ty::Ref(Box::new(self.ty(inner)?)),
            Ty::RefMut(inner) => Ty::RefMut(Box::new(self.ty(inner)?)),
            Ty::PtrConst(inner) => Ty::PtrConst(Box::new(self.ty(inner)?)),
            Ty::PtrMut(inner) => Ty::PtrMut(Box::new(self.ty(inner)?)),
            Ty::Rc(inner) => Ty::Rc(Box::new(self.ty(inner)?)),
            Ty::Set(elem, repr) => Ty::Set(self.ty_id(*elem)?, *repr),
            Ty::Sequence(elem) => Ty::Sequence(self.ty_id(*elem)?),
            Ty::Record(id) => Ty::Record(self.record_id(*id)?),
            Ty::Closure(id) => Ty::Closure(self.closure_id(*id)?),
            // Level R has no extension: `NoExt` is uninhabited.
            Ty::Ext(e) => e.unreachable(),
            Ty::Refine(base, pred) => {
                // Refinements do not nest (one spelling per fact): a base
                // row that is itself a refinement is refused here, as the
                // runner's linker always did, rather than relocated.
                if matches!(self.src.types.get(base.as_usize()), Some(Ty::Refine(..))) {
                    return Err(MergeError::Malformed {
                        table: "types",
                        id: base.index(),
                        detail: "a refinement's base is itself a refinement",
                    });
                }
                Ty::Refine(
                    self.ty_id(*base)?,
                    *self
                        .pred_map
                        .get(pred.as_usize())
                        .ok_or(MergeError::Dangling {
                            table: "predicates",
                            id: pred.index(),
                        })?,
                )
            }
        })
    }

    fn constant(&mut self, value: &Constant) -> Result<Constant, MergeError> {
        Ok(match value {
            Constant::Int(v) => Constant::Int(*v),
            Constant::U128(v) => Constant::U128(*v),
            Constant::Bytes { data, utf8 } => Constant::Bytes {
                data: data.clone(),
                utf8: *utf8,
            },
            Constant::Float(v) => Constant::Float(*v),
            Constant::Bool(v) => Constant::Bool(*v),
            Constant::PhantomData => Constant::PhantomData,
            Constant::Uninit => Constant::Uninit,
            // Resolved by NAME against the merged image: verbatim.
            Constant::SymbolAddr { symbol, addend } => Constant::SymbolAddr {
                symbol: symbol.clone(),
                addend: *addend,
            },
            Constant::Aggregate(items) => Constant::Aggregate(self.constants(items)?),
            Constant::Array(items) => Constant::Array(self.constants(items)?),
            Constant::Splat { elem, len } => Constant::Splat {
                elem: Box::new(self.constant(elem)?),
                len: *len,
            },
            Constant::Vector(items) => Constant::Vector(self.constants(items)?),
            Constant::Sequence(items) => Constant::Sequence(self.constants(items)?),
            Constant::Set(items) => Constant::Set(self.constants(items)?),
            Constant::Record(fields) => Constant::Record(
                fields
                    .iter()
                    .map(|(name, value)| Ok((name.clone(), self.constant(value)?)))
                    .collect::<Result<_, MergeError>>()?,
            ),
            Constant::Closure { func, captures } => Constant::Closure {
                func: self.func(*func)?,
                captures: self.constants(captures)?,
            },
            Constant::FnDef(func) => Constant::FnDef(self.func(*func)?),
            Constant::FnItem(func) => Constant::FnItem(self.func(*func)?),
            // A digest names bytes, not an id: verbatim (the tables union).
            Constant::TensorBlob { digest, dims } => Constant::TensorBlob {
                digest: *digest,
                dims: dims.clone(),
            },
            // Level R has no extension: `NoExt` is uninhabited.
            Constant::Ext(e) => e.unreachable(),
        })
    }

    fn constants(&mut self, values: &[Constant]) -> Result<Vec<Constant>, MergeError> {
        values.iter().map(|value| self.constant(value)).collect()
    }

    // -- instructions ------------------------------------------------------------

    /// One tensor map node (PKG-U13c): its types remapped, its lanes verbatim.
    fn tensor_map_node(
        &mut self,
        node: &trust_ir::TensorMapNode<trust_ir::level::NoExt>,
    ) -> Result<trust_ir::TensorMapNode<trust_ir::level::NoExt>, MergeError> {
        use trust_ir::TensorMapNode as N;
        Ok(match node {
            N::BinOp { op, ty, lhs, rhs } => N::BinOp {
                op: *op,
                ty: self.ty(ty)?,
                lhs: *lhs,
                rhs: *rhs,
            },
            N::UnOp { op, ty, operand } => N::UnOp {
                op: *op,
                ty: self.ty(ty)?,
                operand: *operand,
            },
            N::ICmp { op, ty, lhs, rhs } => N::ICmp {
                op: *op,
                ty: self.ty(ty)?,
                lhs: *lhs,
                rhs: *rhs,
            },
            N::Select {
                ty,
                cond,
                then_lane,
                else_lane,
            } => N::Select {
                ty: self.ty(ty)?,
                cond: *cond,
                then_lane: *then_lane,
                else_lane: *else_lane,
            },
            N::Cast {
                op,
                src_ty,
                dst_ty,
                operand,
            } => N::Cast {
                op: *op,
                src_ty: self.ty(src_ty)?,
                dst_ty: self.ty(dst_ty)?,
                operand: *operand,
            },
        })
    }

    #[allow(clippy::too_many_lines)]
    fn inst(&mut self, inst: &Inst) -> Result<Inst, MergeError> {
        Ok(match inst {
            Inst::BinOp { op, ty, lhs, rhs } => Inst::BinOp {
                op: *op,
                ty: self.ty(ty)?,
                lhs: *lhs,
                rhs: *rhs,
            },
            Inst::UnOp { op, ty, operand } => Inst::UnOp {
                op: *op,
                ty: self.ty(ty)?,
                operand: *operand,
            },
            Inst::Overflow { op, ty, lhs, rhs } => Inst::Overflow {
                op: *op,
                ty: self.ty(ty)?,
                lhs: *lhs,
                rhs: *rhs,
            },
            Inst::ICmp { op, ty, lhs, rhs } => Inst::ICmp {
                op: *op,
                ty: self.ty(ty)?,
                lhs: *lhs,
                rhs: *rhs,
            },
            Inst::FCmp { op, ty, lhs, rhs } => Inst::FCmp {
                op: *op,
                ty: self.ty(ty)?,
                lhs: *lhs,
                rhs: *rhs,
            },
            Inst::Cast {
                op,
                src_ty,
                dst_ty,
                operand,
            } => Inst::Cast {
                op: *op,
                src_ty: self.ty(src_ty)?,
                dst_ty: self.ty(dst_ty)?,
                operand: *operand,
            },
            Inst::Load {
                ty,
                ptr,
                volatile,
                align,
            } => Inst::Load {
                ty: self.ty(ty)?,
                ptr: *ptr,
                volatile: *volatile,
                align: *align,
            },
            Inst::Store {
                ty,
                ptr,
                value,
                volatile,
                align,
            } => Inst::Store {
                ty: self.ty(ty)?,
                ptr: *ptr,
                value: *value,
                volatile: *volatile,
                align: *align,
            },
            Inst::Alloca { ty, count, align } => Inst::Alloca {
                ty: self.ty(ty)?,
                count: *count,
                align: *align,
            },
            Inst::Drop { ty, ptr } => Inst::Drop {
                ty: self.ty(ty)?,
                ptr: *ptr,
            },
            Inst::HeapAlloc {
                ty,
                count,
                align,
                origin,
            } => Inst::HeapAlloc {
                ty: self.ty(ty)?,
                count: *count,
                align: *align,
                origin: *origin,
            },
            Inst::GEP {
                pointee_ty,
                base,
                indices,
                inbounds,
            } => Inst::GEP {
                pointee_ty: self.ty(pointee_ty)?,
                base: *base,
                indices: indices.clone(),
                inbounds: *inbounds,
            },
            Inst::PtrData { ptr_ty, ptr } => Inst::PtrData {
                ptr_ty: self.ty(ptr_ty)?,
                ptr: *ptr,
            },
            Inst::PtrMetadata {
                ptr_ty,
                metadata_ty,
                ptr,
            } => Inst::PtrMetadata {
                ptr_ty: self.ty(ptr_ty)?,
                metadata_ty: self.ty(metadata_ty)?,
                ptr: *ptr,
            },
            Inst::PtrFromParts {
                ptr_ty,
                metadata_ty,
                data,
                metadata,
            } => Inst::PtrFromParts {
                ptr_ty: self.ty(ptr_ty)?,
                metadata_ty: self.ty(metadata_ty)?,
                data: *data,
                metadata: *metadata,
            },
            Inst::AtomicLoad { ty, ptr, ordering } => Inst::AtomicLoad {
                ty: self.ty(ty)?,
                ptr: *ptr,
                ordering: *ordering,
            },
            Inst::AtomicStore {
                ty,
                ptr,
                value,
                ordering,
            } => Inst::AtomicStore {
                ty: self.ty(ty)?,
                ptr: *ptr,
                value: *value,
                ordering: *ordering,
            },
            Inst::AtomicRMW {
                op,
                ty,
                ptr,
                value,
                ordering,
            } => Inst::AtomicRMW {
                op: *op,
                ty: self.ty(ty)?,
                ptr: *ptr,
                value: *value,
                ordering: *ordering,
            },
            Inst::CmpXchg {
                ty,
                ptr,
                expected,
                desired,
                success,
                failure,
                weak,
            } => Inst::CmpXchg {
                ty: self.ty(ty)?,
                ptr: *ptr,
                expected: *expected,
                desired: *desired,
                success: *success,
                failure: *failure,
                weak: *weak,
            },
            Inst::Fence { ordering } => Inst::Fence {
                ordering: *ordering,
            },
            Inst::Br { target, args } => Inst::Br {
                target: *target,
                args: args.clone(),
            },
            Inst::CondBr {
                cond,
                then_target,
                then_args,
                else_target,
                else_args,
            } => Inst::CondBr {
                cond: *cond,
                then_target: *then_target,
                then_args: then_args.clone(),
                else_target: *else_target,
                else_args: else_args.clone(),
            },
            Inst::Switch {
                value,
                default,
                default_args,
                cases,
                exhaustive_enum_unreachable,
            } => Inst::Switch {
                value: *value,
                default: *default,
                default_args: default_args.clone(),
                cases: cases
                    .iter()
                    .map(|case| {
                        let SwitchCase {
                            value,
                            target,
                            args,
                        } = case;
                        Ok(SwitchCase {
                            value: self.constant(value)?,
                            target: *target,
                            args: args.clone(),
                        })
                    })
                    .collect::<Result<_, MergeError>>()?,
                exhaustive_enum_unreachable: *exhaustive_enum_unreachable,
            },
            // The fact cites an obligation by module-local id; a merge
            // renumbers obligations, so the citation is rewritten with them.
            Inst::BoxDeref {
                ptr_ty,
                pointee,
                operand,
                fact,
            } => {
                let trust_ir::box_validity::BoxPointee::Sized { ty } = pointee;
                let mut fact = fact.clone();
                for entry in &mut fact.evidence {
                    if let trust_ir::box_validity::ValidityEvidence::Obligation { obligation } =
                        &mut entry.evidence
                    {
                        *obligation = self.proof(*obligation)?;
                    }
                }
                Inst::BoxDeref {
                    ptr_ty: self.ty(ptr_ty)?,
                    pointee: trust_ir::box_validity::BoxPointee::Sized { ty: self.ty(ty)? },
                    operand: *operand,
                    fact,
                }
            }
            Inst::MakeClosure { ty, func, captures } => Inst::MakeClosure {
                ty: self.closure_id(*ty)?,
                func: self.func(*func)?,
                captures: captures.clone(),
            },
            Inst::Call { callee, args } => Inst::Call {
                callee: self.func(*callee)?,
                args: args.clone(),
            },
            Inst::CallIndirect {
                callee,
                sig,
                args,
                calling_conv,
            } => Inst::CallIndirect {
                callee: *callee,
                sig: self.functy_id(*sig)?,
                args: args.clone(),
                calling_conv: *calling_conv,
            },
            Inst::Return { values } => Inst::Return {
                values: values.clone(),
            },
            Inst::ExtractField {
                ty,
                aggregate,
                field,
            } => Inst::ExtractField {
                ty: self.ty(ty)?,
                aggregate: *aggregate,
                field: *field,
            },
            Inst::InsertField {
                ty,
                aggregate,
                field,
                value,
            } => Inst::InsertField {
                ty: self.ty(ty)?,
                aggregate: *aggregate,
                field: *field,
                value: *value,
            },
            Inst::ExtractElement { ty, array, index } => Inst::ExtractElement {
                ty: self.ty(ty)?,
                array: *array,
                index: *index,
            },
            Inst::InsertElement {
                ty,
                array,
                index,
                value,
            } => Inst::InsertElement {
                ty: self.ty(ty)?,
                array: *array,
                index: *index,
                value: *value,
            },
            Inst::Const { ty, value } => Inst::Const {
                ty: self.ty(ty)?,
                value: self.constant(value)?,
            },
            Inst::NullPtr => Inst::NullPtr,
            Inst::GlobalAddr { global } => Inst::GlobalAddr {
                global: self.global_ref(*global)?,
            },
            Inst::Undef { ty } => Inst::Undef { ty: self.ty(ty)? },
            Inst::Assume { cond } => Inst::Assume { cond: *cond },
            // Amendment P: a panic site names a function (its entry) and, for
            // a static location, a global — both module ids, remapped exactly
            // as a `Call` callee and a `GlobalAddr` are.
            Inst::Assert { cond, kind, site } => Inst::Assert {
                cond: *cond,
                kind: *kind,
                site: site
                    .as_ref()
                    .map(|site| self.panic_site(site))
                    .transpose()?,
            },
            Inst::AssertInvoke {
                cond,
                kind,
                site,
                normal_dest,
                normal_args,
                unwind_dest,
            } => Inst::AssertInvoke {
                cond: *cond,
                kind: *kind,
                site: self.panic_site(site)?,
                normal_dest: *normal_dest,
                normal_args: normal_args.clone(),
                unwind_dest: *unwind_dest,
            },
            Inst::Unreachable => Inst::Unreachable,
            Inst::Copy { ty, operand } => Inst::Copy {
                ty: self.ty(ty)?,
                operand: *operand,
            },
            Inst::Select {
                ty,
                cond,
                then_val,
                else_val,
            } => Inst::Select {
                ty: self.ty(ty)?,
                cond: *cond,
                then_val: *then_val,
                else_val: *else_val,
            },
            Inst::SeqMapAddK { ty, seq, k } => Inst::SeqMapAddK {
                ty: self.ty(ty)?,
                seq: *seq,
                k: *k,
            },
            Inst::SeqMapNot { ty, seq } => Inst::SeqMapNot {
                ty: self.ty(ty)?,
                seq: *seq,
            },
            Inst::SeqMap { ty, seq, fwd } => Inst::SeqMap {
                ty: self.ty(ty)?,
                seq: *seq,
                fwd: self.func(*fwd)?,
            },
            Inst::Borrow { ptr } => Inst::Borrow { ptr: *ptr },
            Inst::BorrowMut { ptr } => Inst::BorrowMut { ptr: *ptr },
            Inst::EndBorrow { borrow_ptr } => Inst::EndBorrow {
                borrow_ptr: *borrow_ptr,
            },
            Inst::Retain { ptr } => Inst::Retain { ptr: *ptr },
            Inst::Release { ptr } => Inst::Release { ptr: *ptr },
            Inst::IsUnique { ptr } => Inst::IsUnique { ptr: *ptr },
            Inst::Dealloc { ptr } => Inst::Dealloc { ptr: *ptr },
            Inst::MemCopy {
                dst,
                src,
                bytes,
                overlap,
            } => Inst::MemCopy {
                dst: *dst,
                src: *src,
                bytes: *bytes,
                overlap: *overlap,
            },
            Inst::MemSet { dst, byte, bytes } => Inst::MemSet {
                dst: *dst,
                byte: *byte,
                bytes: *bytes,
            },
            Inst::OpenFrame { def } => {
                let BindingFrameDef { id, name, slots } = def;
                Inst::OpenFrame {
                    def: BindingFrameDef {
                        id: *id,
                        name: name.clone(),
                        slots: slots
                            .iter()
                            .map(|slot| {
                                let BindingSlot { name, ty } = slot;
                                Ok(BindingSlot {
                                    name: name.clone(),
                                    ty: self.ty(ty)?,
                                })
                            })
                            .collect::<Result<_, MergeError>>()?,
                    },
                }
            }
            Inst::BindSlot { frame, slot, value } => Inst::BindSlot {
                frame: *frame,
                slot: *slot,
                value: *value,
            },
            Inst::LoadSlot { frame, slot, ty } => Inst::LoadSlot {
                frame: *frame,
                slot: *slot,
                ty: self.ty(ty)?,
            },
            Inst::CloseFrame { frame } => Inst::CloseFrame { frame: *frame },
            Inst::CoroSuspend {
                frame,
                state_slot,
                next_state,
                value,
            } => Inst::CoroSuspend {
                frame: *frame,
                state_slot: *state_slot,
                next_state: *next_state,
                value: *value,
            },
            Inst::Invoke {
                callee,
                args,
                normal_dest,
                normal_args,
                unwind_dest,
            } => Inst::Invoke {
                callee: self.func(*callee)?,
                args: args.clone(),
                normal_dest: *normal_dest,
                normal_args: normal_args.clone(),
                unwind_dest: *unwind_dest,
            },
            // Backend LSDA type indices, not a module table: verbatim.
            Inst::LandingPad {
                is_cleanup,
                catch_type_indices,
            } => Inst::LandingPad {
                is_cleanup: *is_cleanup,
                catch_type_indices: catch_type_indices.clone(),
            },
            Inst::Resume { exn } => Inst::Resume { exn: *exn },
            Inst::DialectOp(op) => {
                let DialectInst {
                    dialect,
                    op,
                    operands,
                    result_tys,
                    attrs,
                    version,
                } = op.as_ref();
                Inst::DialectOp(Box::new(DialectInst {
                    dialect: dialect.clone(),
                    op: op.clone(),
                    operands: operands.clone(),
                    result_tys: self.tys(result_tys)?,
                    attrs: attrs
                        .iter()
                        .map(|entry| {
                            let AttrEntry { name, value } = entry;
                            Ok(AttrEntry {
                                name: name.clone(),
                                value: match value {
                                    AttrValue::I64(v) => AttrValue::I64(*v),
                                    AttrValue::U64(v) => AttrValue::U64(*v),
                                    AttrValue::F64(v) => AttrValue::F64(*v),
                                    AttrValue::Bool(v) => AttrValue::Bool(*v),
                                    AttrValue::Str(v) => AttrValue::Str(v.clone()),
                                    AttrValue::Bytes(v) => AttrValue::Bytes(v.clone()),
                                    // A type-valued attribute names module
                                    // tables like any inline type.
                                    AttrValue::Ty(ty) => AttrValue::Ty(self.ty(ty)?),
                                },
                            })
                        })
                        .collect::<Result<_, MergeError>>()?,
                    version: *version,
                }))
            }
            Inst::MakeAggregate {
                ty,
                variant,
                fields,
            } => Inst::MakeAggregate {
                ty: self.ty(ty)?,
                variant: *variant,
                fields: fields.clone(),
            },
            Inst::ArraySplat { ty, value } => Inst::ArraySplat {
                ty: self.ty(ty)?,
                value: *value,
            },
            // The tensor region: only the inline result type names module
            // tables; operands and axis pairs are carried verbatim.
            Inst::TensorContract {
                ty,
                lhs,
                rhs,
                batch,
                contract,
            } => Inst::TensorContract {
                ty: self.ty(ty)?,
                lhs: *lhs,
                rhs: *rhs,
                batch: batch.clone(),
                contract: contract.clone(),
            },
            // PKG-U13c: the inline types name module tables; operands, lanes,
            // axes and index nodes are carried verbatim.
            Inst::TensorMap { ty, args, body } => Inst::TensorMap {
                ty: self.ty(ty)?,
                args: args.clone(),
                body: body
                    .iter()
                    .map(|node| self.tensor_map_node(node))
                    .collect::<Result<_, _>>()?,
            },
            Inst::TensorReduce {
                ty,
                src,
                op,
                axes,
                order,
            } => Inst::TensorReduce {
                ty: self.ty(ty)?,
                src: *src,
                op: *op,
                axes: axes.clone(),
                order: *order,
            },
            Inst::TensorView {
                ty,
                src,
                params,
                exprs,
                shape,
                index,
                fill,
            } => Inst::TensorView {
                ty: self.ty(ty)?,
                src: *src,
                params: params.clone(),
                exprs: exprs.clone(),
                shape: shape.clone(),
                index: index.clone(),
                fill: *fill,
            },
            // PKG-U13d: the inline result type names module tables; the
            // operands are carried verbatim, as every value id here is.
            Inst::TensorGather { ty, data, coords } => Inst::TensorGather {
                ty: self.ty(ty)?,
                data: *data,
                coords: coords.clone(),
            },
            Inst::TensorScatter {
                ty,
                init,
                src,
                coords,
            } => Inst::TensorScatter {
                ty: self.ty(ty)?,
                init: *init,
                src: *src,
                coords: coords.clone(),
            },
            // The call-unwind boundary: `Call` / `CallIndirect` twins that
            // state the callee cannot unwind; the ids are remapped as theirs.
            Inst::CallCannotUnwind { callee, args } => Inst::CallCannotUnwind {
                callee: self.func(*callee)?,
                args: args.clone(),
            },
            Inst::CallIndirectCannotUnwind {
                callee,
                sig,
                args,
                calling_conv,
            } => Inst::CallIndirectCannotUnwind {
                callee: *callee,
                sig: self.functy_id(*sig)?,
                args: args.clone(),
                calling_conv: *calling_conv,
            },
            // Amendment D: `Drop`'s inline type plus `Invoke`'s block-local
            // successors.
            Inst::DropInvoke {
                ty,
                ptr,
                normal_dest,
                normal_args,
                unwind_dest,
            } => Inst::DropInvoke {
                ty: self.ty(ty)?,
                ptr: *ptr,
                normal_dest: *normal_dest,
                normal_args: normal_args.clone(),
                unwind_dest: *unwind_dest,
            },
            // Amendment D, Part 2: `CallIndirect`'s module-local signature id
            // plus `Invoke`'s block-local successors.
            Inst::InvokeIndirect {
                callee,
                sig,
                args,
                calling_conv,
                normal_dest,
                normal_args,
                unwind_dest,
            } => Inst::InvokeIndirect {
                callee: *callee,
                sig: self.functy_id(*sig)?,
                args: args.clone(),
                calling_conv: *calling_conv,
                normal_dest: *normal_dest,
                normal_args: normal_args.clone(),
                unwind_dest: *unwind_dest,
            },
        })
    }

    fn panic_site(&self, site: &PanicSite) -> Result<PanicSite, MergeError> {
        let PanicSite { entry, location } = site;
        Ok(PanicSite {
            entry: self.func(*entry)?,
            location: match location {
                PanicLocation::Global(global) => PanicLocation::Global(self.global_ref(*global)?),
                // A value of the enclosing function: SSA values are never
                // renumbered by the merge.
                PanicLocation::Value(value) => PanicLocation::Value(*value),
            },
        })
    }

    // -- proof surface on functions and nodes ------------------------------------

    fn annotations(
        &mut self,
        proofs: &[ProofAnnotation],
    ) -> Result<Vec<ProofAnnotation>, MergeError> {
        let mut out = Vec::with_capacity(proofs.len());
        for annotation in proofs {
            match annotation {
                ProofAnnotation::ProofRef(id) => {
                    if self.policy.carry_proof_state {
                        out.push(ProofAnnotation::ProofRef(self.proof(*id)?));
                    } else {
                        self.stripped.proof_refs += 1;
                    }
                }
                // Claim-style metadata names no module table.
                other => out.push(other.clone()),
            }
        }
        Ok(out)
    }

    fn proof_context(
        &mut self,
        context: Option<&ProofContext>,
    ) -> Result<Option<ProofContext>, MergeError> {
        let Some(ProofContext {
            assumes,
            establishes,
        }) = context
        else {
            return Ok(None);
        };
        if !self.policy.carry_proof_state {
            self.stripped.proof_contexts += 1;
            return Ok(None);
        }
        Ok(Some(ProofContext {
            assumes: assumes
                .iter()
                .map(|id| self.proof(*id))
                .collect::<Result<_, _>>()?,
            establishes: establishes
                .iter()
                .map(|id| self.proof(*id))
                .collect::<Result<_, _>>()?,
        }))
    }

    fn node(&mut self, node: &InstrNode) -> Result<InstrNode, MergeError> {
        let InstrNode {
            inst,
            results,
            proofs,
            span,
            proof_context,
            scope,
        } = node;
        Ok(InstrNode {
            inst: self.inst(inst)?,
            results: results.clone(),
            proofs: self.annotations(proofs)?,
            span: span.as_ref().map(|s| self.span(s)).transpose()?,
            proof_context: self.proof_context(proof_context.as_ref())?,
            // Function-local: bodies are never renumbered.
            scope: *scope,
        })
    }

    fn param_attrs(&mut self, attrs: &ParamAttrs) -> Result<ParamAttrs, MergeError> {
        let ParamAttrs {
            dereferenceable,
            nonnull,
            align,
            noalias,
            readonly,
            byval,
            sret,
            ext,
            pass,
        } = attrs;
        Ok(ParamAttrs {
            dereferenceable: *dereferenceable,
            nonnull: *nonnull,
            align: *align,
            noalias: *noalias,
            readonly: *readonly,
            byval: *byval,
            sret: *sret,
            ext: *ext,
            pass: match pass {
                None => None,
                Some(PassMode::Ignore) => Some(PassMode::Ignore),
                Some(PassMode::Direct) => Some(PassMode::Direct),
                Some(PassMode::Pair) => Some(PassMode::Pair),
                Some(PassMode::Cast { pieces }) => Some(PassMode::Cast {
                    pieces: self.tys(pieces)?,
                }),
                Some(PassMode::Indirect { on_stack }) => Some(PassMode::Indirect {
                    on_stack: *on_stack,
                }),
            },
        })
    }

    fn func_attrs(&mut self, attrs: &FuncAttrs) -> Result<FuncAttrs, MergeError> {
        let FuncAttrs {
            readonly,
            readnone,
            inlinehint,
            cold,
            params,
            naked,
            target_features,
            ret,
        } = attrs;
        Ok(FuncAttrs {
            readonly: *readonly,
            readnone: *readnone,
            inlinehint: *inlinehint,
            cold: *cold,
            params: params
                .iter()
                .map(|p| self.param_attrs(p))
                .collect::<Result<_, _>>()?,
            naked: *naked,
            target_features: target_features.clone(),
            ret: self.param_attrs(ret)?,
        })
    }

    fn summary(&mut self, func: &Function) -> Result<Option<FunctionSummary>, MergeError> {
        let Some(summary) = &func.summary else {
            return Ok(None);
        };
        if !self.policy.carry_proof_state {
            // WS4.6: the image carries no claims. A contract-only declaration
            // (bodyless, non-External linkage) is valid only BECAUSE it
            // carries a summary, so it keeps the claim-free EMPTY one rather
            // than turning the merge's own edit into `EmptyFunction`.
            self.stripped.summaries += 1;
            let contract_only_declaration = func.blocks.is_empty()
                && !matches!(func.linkage, Linkage::External | Linkage::ExternalWeak);
            return Ok(contract_only_declaration.then(FunctionSummary::default));
        }
        let FunctionSummary {
            requires,
            ensures,
            params,
            proved,
            decreases,
            backed_by,
            effects,
        } = summary;
        Ok(Some(FunctionSummary {
            // Clause bindings name params, result slots, the world (the v59
            // `WorldPre` / `WorldPost` epochs included) and function-local SSA
            // values — none of them a module table.
            requires: requires.clone(),
            ensures: ensures.clone(),
            params: params.clone(),
            proved: *proved,
            decreases: decreases.clone(),
            backed_by: backed_by
                .as_ref()
                .map(|r| self.extern_ref(r, || format!("the summary of @{}", func.name)))
                .transpose()?,
            effects: effects
                .as_ref()
                .map(|e| self.effect_summary(e, func.id))
                .transpose()?,
        }))
    }

    /// A v59 effect summary (WS1.14) in the merged image: the SAME claim
    /// about the same storage. Every flag and every `Nothing` / `Everything`
    /// side is carried verbatim; a `Places` side maps place by place — a
    /// `ParamPointee` index is positional in the function's own signature,
    /// which the merge never changes, and a `Global` follows the global
    /// remap — so the claim is never widened (no place dropped) and never
    /// narrowed or invented (no place added). `None` stays `None`.
    fn effect_summary(
        &self,
        effects: &EffectSummary,
        func: FuncId,
    ) -> Result<EffectSummary, MergeError> {
        let EffectSummary {
            reads,
            writes,
            allocates,
            frees,
            may_unwind,
            io,
        } = effects;
        Ok(EffectSummary {
            reads: self.effect_set(reads, func)?,
            writes: self.effect_set(writes, func)?,
            allocates: *allocates,
            frees: *frees,
            may_unwind: *may_unwind,
            io: *io,
        })
    }

    /// One side of an effect summary. A `Places` list has ONE spelling
    /// (non-empty, strictly ascending), and the global remap is not monotone
    /// — `src`'s globals land after `dst`'s, or on a `dst` global of the same
    /// symbol, wherever that sits — so the mapped list is re-sorted into the
    /// canonical spelling of its image (two `src` globals of one symbol are
    /// one storage in the image, and one place). A non-canonical `src` list
    /// has no canonical image the merge could pick without repairing it, so
    /// it is refused as `Malformed`, never silently canonicalized; every
    /// decoder refuses one on read, so only an in-memory module can carry it.
    fn effect_set(&self, set: &EffectSet, func: FuncId) -> Result<EffectSet, MergeError> {
        match set {
            EffectSet::Nothing => Ok(EffectSet::Nothing),
            EffectSet::Everything => Ok(EffectSet::Everything),
            EffectSet::Places(places) => {
                if !set.is_canonical() {
                    return Err(MergeError::Malformed {
                        table: "functions",
                        id: func.index(),
                        detail: "an effect set of the summary is not canonical",
                    });
                }
                let mapped = places
                    .iter()
                    .map(|place| {
                        Ok(match place {
                            EffectPlace::ParamPointee { index } => {
                                EffectPlace::ParamPointee { index: *index }
                            }
                            EffectPlace::Global(global) => {
                                EffectPlace::Global(self.global_ref(*global)?)
                            }
                        })
                    })
                    .collect::<Result<Vec<_>, MergeError>>()?;
                Ok(EffectSet::of(mapped))
            }
        }
    }

    fn function(&mut self, func: &Function, id: FuncId) -> Result<Function, MergeError> {
        let Function {
            id: _,
            name,
            ty,
            entry,
            blocks,
            proofs,
            calling_conv,
            linkage,
            attrs,
            summary: _,
            producer,
            value_names,
            scopes,
            source_provenance,
            body_gate,
            display_path,
            section,
            visibility,
            retained,
        } = func;
        if source_provenance.is_some() {
            self.dropped_provenance += 1;
        }
        let body_gate = license_without_evidence(body_gate.as_ref());
        if body_gate.as_ref() != func.body_gate.as_ref() {
            self.dropped_gate_evidence += 1;
        }
        let summary = self.summary(func)?;
        let mut merged_blocks = Vec::with_capacity(blocks.len());
        for block in blocks {
            let Block { id, params, body } = block;
            merged_blocks.push(Block {
                id: *id,
                params: params
                    .iter()
                    .map(|(value, ty)| Ok((*value, self.ty(ty)?)))
                    .collect::<Result<_, MergeError>>()?,
                body: body
                    .iter()
                    .map(|node| self.node(node))
                    .collect::<Result<_, _>>()?,
            });
        }
        let scopes = match scopes {
            None => None,
            Some(scopes) => Some(
                scopes
                    .iter()
                    .map(|scope| {
                        let ScopeData {
                            parent,
                            span,
                            inlined_at,
                        } = scope;
                        Ok(ScopeData {
                            parent: *parent,
                            span: span.as_ref().map(|s| self.span(s)).transpose()?,
                            inlined_at: match inlined_at {
                                None => None,
                                Some(InlinedAt { span, callee }) => Some(InlinedAt {
                                    span: self.span(span)?,
                                    callee: callee.clone(),
                                }),
                            },
                        })
                    })
                    .collect::<Result<_, MergeError>>()?,
            ),
        };
        Ok(Function {
            id,
            name: name.clone(),
            ty: self.functy_id(*ty)?,
            entry: *entry,
            blocks: merged_blocks,
            proofs: self.annotations(proofs)?,
            calling_conv: *calling_conv,
            linkage: *linkage,
            attrs: self.func_attrs(attrs)?,
            summary,
            producer: producer.clone(),
            value_names: value_names.clone(),
            scopes,
            // F-078: the seal hashes the containing module; dropped (counted).
            source_provenance: None,
            // Wire v61: the license and its authority are carried; its
            // evidence is dropped (counted, `Remap::dropped_gate_evidence`).
            body_gate,
            display_path: display_path.clone(),
            section: section.clone(),
            visibility: *visibility,
            retained: *retained,
        })
    }

    // -- globals -----------------------------------------------------------------

    fn global_ref(&self, id: GlobalId) -> Result<GlobalId, MergeError> {
        self.global_map
            .get(id.as_usize())
            .copied()
            .ok_or(MergeError::Dangling {
                table: "globals",
                id: id.index(),
            })
    }

    fn global(&mut self, global: &Global) -> Result<Global, MergeError> {
        let Global {
            name,
            ty,
            mutable,
            initializer,
            linkage,
            tls,
            align,
            section,
            visibility,
            retained,
        } = global;
        Ok(Global {
            name: name.clone(),
            ty: self.ty(ty)?,
            mutable: *mutable,
            initializer: initializer.as_ref().map(|c| self.constant(c)).transpose()?,
            linkage: *linkage,
            tls: *tls,
            align: *align,
            section: section.clone(),
            visibility: *visibility,
            retained: *retained,
        })
    }

    /// Globals are keyed by symbol: a `src` global equal to a `dst` one is
    /// that global; a different one under the same symbol is a conflict.
    fn merge_globals(&mut self, globals: &[Global]) -> Result<Vec<Global>, MergeError> {
        let dst = self.dst;
        let mut by_name: HashMap<&str, usize> = HashMap::new();
        for (i, g) in dst.globals.iter().enumerate() {
            by_name.entry(g.name.as_str()).or_insert(i);
        }
        let base = len_u32(dst.globals.len(), "globals")?;
        let mut staged: Vec<Global> = Vec::new();
        let mut staged_by_name: HashMap<String, usize> = HashMap::new();
        for global in globals {
            let incoming = self.global(global)?;
            let existing = match by_name.get(incoming.name.as_str()) {
                Some(&pos) => Some((&dst.globals[pos], len_u32(pos, "globals")?)),
                None => match staged_by_name.get(&incoming.name) {
                    Some(&k) => Some((&staged[k], file_index(base, k)?)),
                    None => None,
                },
            };
            let mapped = match existing {
                Some((existing, id)) => {
                    self.resolve_global(existing, &incoming)?;
                    id
                }
                None => {
                    let id = file_index(base, staged.len())
                        .map_err(|_| MergeError::IdSpaceExhausted { table: "globals" })?;
                    staged_by_name.insert(incoming.name.clone(), staged.len());
                    staged.push(incoming);
                    id
                }
            };
            self.global_map.push(GlobalId::new(mapped));
        }
        Ok(staged)
    }

    fn resolve_global(&self, existing: &Global, incoming: &Global) -> Result<(), MergeError> {
        if self.policy.on_duplicate_definition == DuplicateDef::Refuse
            && (existing.initializer.is_some() || incoming.initializer.is_some())
        {
            return Err(MergeError::DuplicateDefinition {
                symbol: incoming.name.clone(),
            });
        }
        match global_difference(existing, incoming) {
            None => Ok(()),
            Some(field) => Err(MergeError::ConflictingDefinition {
                symbol: incoming.name.clone(),
                field,
            }),
        }
    }

    // -- functions -----------------------------------------------------------------

    /// A signature row of the merged image: `dst`'s own below the base, the
    /// staged `src` row above it.
    fn merged_func_type(&self, id: FuncTyId) -> Option<&FuncTy> {
        match id.index().checked_sub(self.functy_base) {
            None => self.dst.func_types.get(id.as_usize()),
            Some(k) => self.functy_out.get(k as usize).and_then(Option::as_ref),
        }
    }

    /// Two signature ids of the merged image state one signature: equal ids,
    /// or two rows of equal content. The signature table is positional and
    /// not interned (`Module::add_func_type` appends), so equal signatures
    /// routinely sit at two ids — a `src` reference lands on the FIRST equal
    /// `dst` row while a `dst` function may name an alias. Comparing ids
    /// alone would refuse two identical definitions, or a declaration and its
    /// definition, over an alias.
    fn same_signature(&self, a: FuncTyId, b: FuncTyId) -> bool {
        a == b
            || matches!(
                (self.merged_func_type(a), self.merged_func_type(b)),
                (Some(x), Some(y)) if x == y
            )
    }

    /// The ABI two entries of one symbol both state: the signature (by
    /// content) and the calling convention. `Err` names the differing field.
    fn same_abi(&self, a: &Function, b: &Function) -> Result<(), &'static str> {
        if !self.same_signature(a.ty, b.ty) {
            return Err("ty");
        }
        if a.calling_conv != b.calling_conv {
            return Err("calling_conv");
        }
        Ok(())
    }

    fn resolve_function(
        &self,
        existing: &Function,
        incoming: &Function,
    ) -> Result<Resolution, MergeError> {
        let conflict = |field| MergeError::ConflictingDefinition {
            symbol: incoming.name.clone(),
            field,
        };
        match (!existing.blocks.is_empty(), !incoming.blocks.is_empty()) {
            (true, true) => {
                if self.policy.on_duplicate_definition == DuplicateDef::Refuse {
                    return Err(MergeError::DuplicateDefinition {
                        symbol: incoming.name.clone(),
                    });
                }
                match function_difference(existing, incoming, |a, b| self.same_signature(a, b)) {
                    None => Ok(Resolution::KeepExisting),
                    Some(field) => Err(conflict(field)),
                }
            }
            (false, false) => {
                match function_difference(existing, incoming, |a, b| self.same_signature(a, b)) {
                    None => Ok(Resolution::KeepExisting),
                    Some(field) => match self.policy.on_duplicate_declaration {
                        DuplicateDecl::RequireIdentical => Err(conflict(field)),
                        DuplicateDecl::FirstStands => {
                            // The earlier declaration stands: the ABI both
                            // state must agree; the later one's other fields
                            // are dropped.
                            self.same_abi(existing, incoming).map_err(conflict)?;
                            Ok(Resolution::Supersede)
                        }
                    },
                }
            }
            (existing_bodied, _) => {
                // A declaration resolved by a definition: the ABI both state
                // must agree; the declaration's other fields are dropped.
                self.same_abi(existing, incoming).map_err(conflict)?;
                Ok(if existing_bodied {
                    Resolution::Supersede
                } else {
                    Resolution::Replace
                })
            }
        }
    }

    /// Place every remapped `src` function. Returns the `dst` positions to
    /// overwrite (a declaration superseded by a `src` definition) and the
    /// functions to append.
    #[allow(clippy::type_complexity)]
    fn merge_functions(
        &mut self,
        functions: &[Function],
    ) -> Result<(Vec<(usize, Function)>, Vec<Function>), MergeError> {
        let dst = self.dst;
        let mut dst_pos: HashMap<FuncId, usize> = HashMap::new();
        for (i, f) in dst.functions.iter().enumerate() {
            dst_pos.entry(f.id).or_insert(i);
        }
        // Each slot remembers which `src` function (if any) it came from, so a
        // superseded declaration is attributed to its side.
        let mut replaced: BTreeMap<usize, (Function, FuncId)> = BTreeMap::new();
        let mut appended: Vec<(Function, FuncId)> = Vec::new();
        let mut appended_pos: HashMap<FuncId, usize> = HashMap::new();
        let mut superseded_dst: Vec<(FuncId, String)> = Vec::new();
        let mut superseded_src: Vec<(FuncId, String)> = Vec::new();

        for func in functions {
            let id = self.func(func.id)?;
            let incoming = self.function(func, id)?;
            if let Some(&pos) = dst_pos.get(&id) {
                let (existing, origin) = match replaced.get(&pos) {
                    Some((f, src_id)) => (f, Some(*src_id)),
                    None => (&dst.functions[pos], None),
                };
                match self.resolve_function(existing, &incoming)? {
                    Resolution::KeepExisting => {}
                    Resolution::Supersede => {
                        superseded_src.push((func.id, incoming.name.clone()));
                    }
                    Resolution::Replace => {
                        match origin {
                            Some(src_id) => superseded_src.push((src_id, existing.name.clone())),
                            None => superseded_dst.push((id, existing.name.clone())),
                        }
                        replaced.insert(pos, (incoming, func.id));
                    }
                }
            } else if let Some(&k) = appended_pos.get(&id) {
                let (existing, src_id) = &appended[k];
                match self.resolve_function(existing, &incoming)? {
                    Resolution::KeepExisting => {}
                    Resolution::Supersede => {
                        superseded_src.push((func.id, incoming.name.clone()));
                    }
                    Resolution::Replace => {
                        superseded_src.push((*src_id, existing.name.clone()));
                        appended[k] = (incoming, func.id);
                    }
                }
            } else {
                appended_pos.insert(id, appended.len());
                appended.push((incoming, func.id));
            }
        }

        let scoped_to = |o: &ProofObligation, f: FuncId| {
            o.function == Some(f) || o.site.is_some_and(|site| site.function == f)
        };
        for (id, symbol) in &superseded_dst {
            if dst.proof_obligations.iter().any(|o| scoped_to(o, *id)) {
                return Err(MergeError::SupersededDeclarationScoped {
                    symbol: symbol.clone(),
                });
            }
        }
        if self.policy.carry_proof_state {
            for (id, symbol) in &superseded_src {
                if self.src.proof_obligations.iter().any(|o| scoped_to(o, *id)) {
                    return Err(MergeError::SupersededDeclarationScoped {
                        symbol: symbol.clone(),
                    });
                }
            }
        }
        Ok((
            replaced.into_iter().map(|(pos, (f, _))| (pos, f)).collect(),
            appended.into_iter().map(|(f, _)| f).collect(),
        ))
    }

    // -- proof state -----------------------------------------------------------------

    fn remap_obligations(
        &mut self,
        obligations: &[ProofObligation],
    ) -> Result<Vec<ProofObligation>, MergeError> {
        obligations
            .iter()
            .map(|o| {
                let ProofObligation {
                    id,
                    kind,
                    status,
                    description,
                    formula,
                    function,
                    source,
                    site,
                    spec,
                } = o;
                Ok(ProofObligation {
                    id: self.proof(*id)?,
                    kind: kind.clone(),
                    status: *status,
                    description: description.clone(),
                    // Clause bindings: see the module docs (NEW-1 identity).
                    formula: formula.clone(),
                    function: function.map(|f| self.func(f)).transpose()?,
                    source: source.clone(),
                    site: match site {
                        None => None,
                        Some(ObligationSite {
                            function,
                            block,
                            inst_index,
                        }) => Some(ObligationSite {
                            function: self.func(*function)?,
                            block: *block,
                            inst_index: *inst_index,
                        }),
                    },
                    spec: spec.clone(),
                })
            })
            .collect()
    }

    fn evidence(&self, evidence: &ProofEvidence) -> Result<ProofEvidence, MergeError> {
        Ok(match evidence {
            ProofEvidence::SmtProof(bytes) => ProofEvidence::SmtProof(bytes.clone()),
            ProofEvidence::LeanProof(text) => ProofEvidence::LeanProof(text.clone()),
            ProofEvidence::KaniHarness(text) => ProofEvidence::KaniHarness(text.clone()),
            ProofEvidence::GammaCrownBound {
                epsilon,
                verified_layers,
            } => ProofEvidence::GammaCrownBound {
                epsilon: *epsilon,
                verified_layers: *verified_layers,
            },
            ProofEvidence::TranslationValidation {
                rule_name,
                smt_hash,
            } => ProofEvidence::TranslationValidation {
                rule_name: rule_name.clone(),
                smt_hash: *smt_hash,
            },
            ProofEvidence::Trusted(text) => ProofEvidence::Trusted(text.clone()),
            ProofEvidence::InheritedFromCallee {
                callee,
                obligation,
                external,
            } => ProofEvidence::InheritedFromCallee {
                callee: self.func(*callee)?,
                obligation: self.proof(*obligation)?,
                external: external
                    .as_ref()
                    .map(|r| {
                        self.extern_ref(r, || {
                            format!(
                                "the inheritance certificate of obligation {}",
                                obligation.index()
                            )
                        })
                    })
                    .transpose()?,
            },
            // The lineage digest is identity binding over the module as it
            // was; the validator re-derives and re-checks it in the merged
            // image. Carried verbatim — never re-stamped here.
            ProofEvidence::CleanCic {
                term,
                context,
                lineage,
                kernel_recheck,
            } => ProofEvidence::CleanCic {
                term: term.clone(),
                context: context.clone(),
                lineage: *lineage,
                kernel_recheck: kernel_recheck.clone(),
            },
        })
    }

    fn remap_certificates(
        &self,
        certificates: &[ProofCertificate],
    ) -> Result<Vec<ProofCertificate>, MergeError> {
        certificates
            .iter()
            .map(|c| {
                let ProofCertificate {
                    obligation,
                    prover,
                    evidence,
                    assurance,
                } = c;
                Ok(ProofCertificate {
                    obligation: self.proof(*obligation)?,
                    prover: prover.clone(),
                    evidence: self.evidence(evidence)?,
                    assurance: *assurance,
                })
            })
            .collect()
    }

    fn remap_diagnostics(
        &self,
        diagnostics: &[ObligationDiagnostic],
    ) -> Result<Vec<ObligationDiagnostic>, MergeError> {
        diagnostics
            .iter()
            .map(|d| {
                let ObligationDiagnostic {
                    obligation,
                    severity,
                    message,
                    location,
                    detail,
                } = d;
                Ok(ObligationDiagnostic {
                    obligation: self.proof(*obligation)?,
                    severity: *severity,
                    message: message.clone(),
                    location: location.as_ref().map(|s| self.span(s)).transpose()?,
                    detail: detail.clone(),
                })
            })
            .collect()
    }

    fn remap_spec_modules(&self, specs: &[SpecModule]) -> Result<Vec<SpecModule>, MergeError> {
        let mut out: Vec<SpecModule> = Vec::new();
        for spec in specs {
            let SpecModule {
                name,
                vars,
                actions,
                invariants,
                anchors,
                waivers,
                proofs,
                origin,
                enforcement,
                temporal,
            } = spec;
            let anchors = anchors
                .iter()
                .map(|anchor| {
                    let SpecAnchor {
                        machine,
                        action,
                        rust_symbol,
                        span,
                        project,
                        function,
                        projection_target,
                    } = anchor;
                    Ok(SpecAnchor {
                        machine: machine.clone(),
                        action: action.clone(),
                        rust_symbol: rust_symbol.clone(),
                        span: span.clone(),
                        project: project.clone(),
                        function: function.map(|f| self.func(f)).transpose()?,
                        projection_target: match projection_target {
                            None => None,
                            Some(SpecProjectionTarget::Function(f)) => {
                                Some(SpecProjectionTarget::Function(self.func(*f)?))
                            }
                            Some(SpecProjectionTarget::TemporalFieldPathsV1) => {
                                Some(SpecProjectionTarget::TemporalFieldPathsV1)
                            }
                            Some(SpecProjectionTarget::ExternalUnresolved) => {
                                Some(SpecProjectionTarget::ExternalUnresolved)
                            }
                        },
                    })
                })
                .collect::<Result<_, MergeError>>()?;
            let remapped = SpecModule {
                name: name.clone(),
                // Spec variables, invariants and temporal properties bind
                // spec-local indices only.
                vars: vars.clone(),
                actions: actions.clone(),
                invariants: invariants.clone(),
                anchors,
                waivers: waivers.clone(),
                proofs: proofs.clone(),
                origin: origin.clone(),
                enforcement: *enforcement,
                temporal: temporal.clone(),
            };
            let duplicate = self
                .dst
                .spec_modules
                .iter()
                .chain(&out)
                .any(|existing| same(existing, &remapped));
            if !duplicate {
                out.push(remapped);
            }
        }
        Ok(out)
    }

    // -- tuple layouts -------------------------------------------------------------

    /// The merged row a reference id names: a `dst` row, or the staged
    /// content of the `src` row appended at that position.
    fn row(&self, id: TyId) -> Option<&Ty> {
        match id.index().checked_sub(self.ty_base) {
            None => self.dst.types.get(id.as_usize()),
            Some(offset) => self
                .ty_out
                .get(offset as usize)
                .and_then(|row| row.as_ref()),
        }
    }

    fn merge_tuple_layouts(
        &mut self,
        layouts: &[TupleLayoutDescriptor],
    ) -> Result<Vec<TupleLayoutDescriptor>, MergeError> {
        let mut out: Vec<TupleLayoutDescriptor> = Vec::new();
        for (i, layout) in layouts.iter().enumerate() {
            let TupleLayoutDescriptor {
                tuple_type,
                size,
                align,
                field_offsets,
            } = layout;
            let tuple_type = self.ty_id(*tuple_type)?;
            let remapped = TupleLayoutDescriptor {
                tuple_type,
                size: *size,
                align: *align,
                field_offsets: field_offsets.clone(),
            };
            let row = self.row(tuple_type).cloned();
            let equal_type = |other: TyId| row.is_some() && self.row(other).cloned() == row;
            if out.iter().any(|d| equal_type(d.tuple_type)) {
                return Err(MergeError::Malformed {
                    table: "tuple_layouts",
                    id: len_u32(i, "tuple_layouts")?,
                    detail: "a second descriptor for an equal tuple type",
                });
            }
            if let Some(existing) = self
                .dst
                .tuple_layouts
                .iter()
                .find(|d| equal_type(d.tuple_type))
            {
                let field = if existing.size != remapped.size {
                    Some("size")
                } else if existing.align != remapped.align {
                    Some("align")
                } else if existing.field_offsets != remapped.field_offsets {
                    Some("field_offsets")
                } else {
                    None
                };
                if let Some(field) = field {
                    return Err(MergeError::ConflictingDefinition {
                        symbol: format!("tuple layout ty.{}", tuple_type.index()),
                        field,
                    });
                }
                continue;
            }
            out.push(remapped);
        }
        Ok(out)
    }

    /// Closure layouts (wire v58) are keyed by closure-type ID, at most one
    /// row per type. Each row's `closure` is remapped like any reference, so
    /// a `src` closure type unified with an equal `dst` row lands on that
    /// row: a `dst` (or earlier `src`) row for the same merged type must then
    /// be identical — else [`MergeError::ConflictingDefinition`] naming the
    /// differing field, never "keep the first" — and an identical one is one
    /// row. A `src` table that names one of its OWN closure types twice is
    /// refused as [`MergeError::Malformed`], not repaired.
    fn merge_closure_layouts(
        &mut self,
        layouts: &[ClosureLayoutDescriptor],
    ) -> Result<Vec<ClosureLayoutDescriptor>, MergeError> {
        let mut out: Vec<ClosureLayoutDescriptor> = Vec::new();
        let mut seen_src: HashSet<ClosureTyId> = HashSet::new();
        for (i, layout) in layouts.iter().enumerate() {
            let ClosureLayoutDescriptor {
                origin,
                closure,
                size,
                align,
                capture_offsets,
            } = layout;
            if !seen_src.insert(*closure) {
                return Err(MergeError::Malformed {
                    table: "closure_layouts",
                    id: len_u32(i, "closure_layouts")?,
                    detail: "a second descriptor for one closure type",
                });
            }
            let remapped = ClosureLayoutDescriptor {
                origin: origin.clone(),
                closure: self.closure_id(*closure)?,
                size: *size,
                align: *align,
                capture_offsets: capture_offsets.clone(),
            };
            let existing = self
                .dst
                .closure_layouts
                .iter()
                .chain(out.iter())
                .find(|d| d.closure == remapped.closure);
            if let Some(existing) = existing {
                let field = if existing.origin != remapped.origin {
                    Some("origin")
                } else if existing.size != remapped.size {
                    Some("size")
                } else if existing.align != remapped.align {
                    Some("align")
                } else if existing.capture_offsets != remapped.capture_offsets {
                    Some("capture_offsets")
                } else {
                    None
                };
                if let Some(field) = field {
                    return Err(MergeError::ConflictingDefinition {
                        symbol: format!("closure layout closure.{}", remapped.closure.index()),
                        field,
                    });
                }
                continue;
            }
            out.push(remapped);
        }
        Ok(out)
    }

    // -- reserved disclosures ----------------------------------------------------------

    /// The Trust compiler's reserved in-band disclosures
    /// ([`RESERVED_TRUST_INTERNAL_SPEC_MODULES`]) are spec modules whose ROW
    /// TEXT binds module-local function ids: a clean-origin row is keyed
    /// `fn:<FuncId index>`, a contract row `fn:<index>:<kind>:<i>` with a
    /// `"func_id"` inside its JSON. No field of [`SpecModule`] is an id, so
    /// the exhaustive destructure cannot see them, and the merger cannot
    /// relocate opaque text. Carried across a relocation such a row would
    /// attribute its claim to whatever function the merged image keeps at
    /// that index (a superseded declaration's row to the definition, a
    /// dangling row to an appended function). So it is carried only where
    /// what it names cannot move:
    ///
    /// * a `src` disclosure only into a `dst` with no functions, under the
    ///   identity function remap (its ids are then the merged ids);
    /// * a `dst` disclosure keeps its ids (`dst` ids never move), so it is
    ///   refused only when the merge changes a function it may name: when it
    ///   replaces a `dst` function whose id a row key names, or — whenever
    ///   the merge adds or replaces any function — when a row key does not
    ///   parse as `fn:<canonical index>` or names no `dst` function (a
    ///   dangling row an appended function could capture).
    ///
    /// Anything else is [`MergeError::UnrelocatableDisclosure`]. A reserved
    /// disclosure that binds NO id ([`ID_FREE_DISCLOSURES`]) is carried like
    /// any spec module; every other reserved name — including one added
    /// later — is treated as id-binding.
    fn guard_id_binding_disclosures(
        &self,
        src_specs: &[SpecModule],
        replaced: &[(usize, Function)],
        appended: &[Function],
    ) -> Result<(), MergeError> {
        let binds_ids = |spec: &SpecModule| {
            RESERVED_TRUST_INTERNAL_SPEC_MODULES.contains(&spec.name.as_str())
                && !ID_FREE_DISCLOSURES.contains(&spec.name.as_str())
        };
        if !replaced.is_empty() || !appended.is_empty() {
            let dst_ids: HashSet<FuncId> = self.dst.functions.iter().map(|f| f.id).collect();
            let replaced_ids: HashSet<FuncId> = replaced.iter().map(|(_, f)| f.id).collect();
            for spec in self.dst.spec_modules.iter().filter(|s| binds_ids(s)) {
                let safe = spec.invariants.iter().all(|row| {
                    disclosure_key_function(&row.name)
                        .is_some_and(|id| dst_ids.contains(&id) && !replaced_ids.contains(&id))
                });
                if !safe {
                    return Err(MergeError::UnrelocatableDisclosure {
                        name: spec.name.clone(),
                    });
                }
            }
        }
        if self.policy.carry_proof_state {
            let relocation_free =
                self.dst.functions.is_empty() && self.func_map.iter().all(|(from, to)| from == to);
            if !relocation_free && let Some(spec) = src_specs.iter().find(|s| binds_ids(s)) {
                return Err(MergeError::UnrelocatableDisclosure {
                    name: spec.name.clone(),
                });
            }
        }
        Ok(())
    }

    // -- drop glue -------------------------------------------------------------------

    /// Amendment D: the drop-glue table is CARRIED, never dropped (a dropped
    /// table turns every resolved drop back into an unresolved one, which
    /// both engines refuse). Each `src` row's glue is remapped like a `Call`
    /// callee and its key like any inline type, then inserted through
    /// [`Module::set_drop_glue`], which keeps the one canonical order and
    /// REFUSES a second glue for one type or a second type for one glue —
    /// so input order never chooses which destructor a drop runs. Re-stating
    /// an identical row is accepted.
    fn merge_drop_glue(
        &mut self,
        entries: &[DropGlueEntry],
    ) -> Result<Vec<DropGlueEntry>, MergeError> {
        let mut table = Module::new("");
        table.drop_glue = self.dst.drop_glue.clone();
        for entry in entries {
            let DropGlueEntry { glue, ty } = entry;
            let glue = self.func(*glue)?;
            let ty = self.ty(ty)?;
            let symbol = self
                .src
                .functions
                .iter()
                .find(|f| f.id == entry.glue)
                .map_or_else(
                    || format!("func.{}", entry.glue.index()),
                    |f| f.name.clone(),
                );
            table.set_drop_glue(ty.clone(), glue).map_err(|conflict| {
                MergeError::DropGlueConflict {
                    glue: symbol,
                    ty: ty.to_string(),
                    conflict,
                }
            })?;
        }
        Ok(table.drop_glue)
    }

    // -- blobs -----------------------------------------------------------------------

    /// PKG-U13e: the blob table is the UNION of both tables by digest, in the
    /// one canonical order, so identical bytes stay stored once. A digest
    /// names no id, so nothing is remapped and a `Constant::TensorBlob` is
    /// carried verbatim. Fail closed: a `src` row whose bytes do not hash to
    /// its digest, or that `dst` already holds with other bytes, is refused,
    /// so input order never chooses which bytes a digest names.
    fn merge_blobs(
        &mut self,
        rows: &[trust_ir::blob::Blob],
    ) -> Result<Vec<trust_ir::blob::Blob>, MergeError> {
        let mut table = Module::new("");
        table.blobs = self.dst.blobs.clone();
        for (i, row) in rows.iter().enumerate() {
            if !row.digest_matches() {
                return Err(MergeError::Malformed {
                    table: "blobs",
                    id: len_u32(i, "blobs")?,
                    detail: "its bytes do not hash to its digest",
                });
            }
            if table
                .blob(&row.digest)
                .is_some_and(|held| held.data != row.data)
            {
                return Err(MergeError::Malformed {
                    table: "blobs",
                    id: len_u32(i, "blobs")?,
                    detail: "the destination holds its digest with other bytes",
                });
            }
            table.intern_blob(row.data.clone());
        }
        Ok(table.blobs)
    }

    // -- completeness --------------------------------------------------------------

    fn merge_completeness(
        &self,
        src: Option<&ModuleCompleteness>,
    ) -> (Option<ModuleCompleteness>, usize) {
        let rows = |c: &ModuleCompleteness| -> Vec<UnloweredRow> {
            match c {
                ModuleCompleteness::Complete => Vec::new(),
                ModuleCompleteness::Partial(rows) => rows.clone(),
            }
        };
        let (Some(d), Some(s)) = (&self.dst.completeness, src) else {
            // `None` is NO CLAIM, and absorbs: a merged image is complete
            // only if every input said so.
            return (None, 0);
        };
        // A row is resolved when the OTHER input defines its symbol. A row
        // naming a symbol its own module defines was already refused there
        // (`UnloweredRowNamesDefinition`) and stays, so the merge never
        // hides that verdict.
        let dst_defined: HashSet<&str> = self
            .dst
            .functions
            .iter()
            .filter(|f| !f.blocks.is_empty())
            .map(|f| f.name.as_str())
            .collect();
        let src_defined: HashSet<&str> = self
            .src
            .functions
            .iter()
            .filter(|f| !f.blocks.is_empty())
            .map(|f| f.name.as_str())
            .collect();
        let mut merged: Vec<UnloweredRow> = Vec::new();
        let mut resolved = 0;
        let sides = [
            (rows(d), &src_defined, &dst_defined),
            (rows(s), &dst_defined, &src_defined),
        ];
        for (side_rows, other, own) in sides {
            for row in side_rows {
                let symbol = row.symbol.as_str();
                if other.contains(symbol) && !own.contains(symbol) {
                    resolved += 1;
                } else if !merged.contains(&row) {
                    merged.push(row);
                }
            }
        }
        // An input that spelled the refused empty `Partial`
        // (`EmptyPartialClaim`) claimed partiality without naming what is
        // missing. The merged image keeps exactly that spelling: replacing it
        // with the other input's rows (or with `Complete`) would claim MORE
        // than the input did — that the named rows are ALL that is missing —
        // and would hide the input's verdict.
        let empty_partial_input = [d, s]
            .iter()
            .any(|c| matches!(c, ModuleCompleteness::Partial(rows) if rows.is_empty()));
        if empty_partial_input {
            return (Some(ModuleCompleteness::Partial(Vec::new())), resolved);
        }
        // One spelling: an empty `Partial` is refused, and every row being
        // resolved IS completeness.
        if merged.is_empty() {
            (Some(ModuleCompleteness::Complete), resolved)
        } else {
            (Some(ModuleCompleteness::Partial(merged)), resolved)
        }
    }

    // -- assembly ------------------------------------------------------------------

    #[allow(clippy::too_many_arguments)]
    fn finish(
        self,
        target_info: Option<trust_ir::TargetInfo>,
        globals: Vec<Global>,
        replaced_functions: Vec<(usize, Function)>,
        functions: Vec<Function>,
        proof_obligations: Vec<ProofObligation>,
        proof_certificates: Vec<ProofCertificate>,
        obligation_diagnostics: Vec<ObligationDiagnostic>,
        spec_modules: Vec<SpecModule>,
        tuple_layouts: Vec<TupleLayoutDescriptor>,
        closure_layouts: Vec<ClosureLayoutDescriptor>,
        global_asm: Vec<String>,
        completeness: Option<ModuleCompleteness>,
        resolved_unlowered: usize,
        drop_glue: Vec<DropGlueEntry>,
        blobs: Vec<trust_ir::blob::Blob>,
    ) -> Result<Staged, MergeError> {
        fn done<T: Copy>(memo: &[Memo<T>], table: &'static str) -> Result<Vec<T>, MergeError> {
            memo.iter()
                .enumerate()
                .map(|(i, m)| match m {
                    Memo::Done(id) => Ok(*id),
                    Memo::Unvisited | Memo::Visiting(_) => Err(MergeError::Malformed {
                        table,
                        id: u32::try_from(i).unwrap_or(u32::MAX),
                        detail: "left unresolved by the merge (internal)",
                    }),
                })
                .collect()
        }
        fn rows<T>(out: Vec<Option<T>>, table: &'static str) -> Result<Vec<T>, MergeError> {
            out.into_iter()
                .enumerate()
                .map(|(i, row)| {
                    row.ok_or(MergeError::Malformed {
                        table,
                        id: u32::try_from(i).unwrap_or(u32::MAX),
                        detail: "left unresolved by the merge (internal)",
                    })
                })
                .collect()
        }
        /// The new definitions, in `src` table order (so a merge into the
        /// identity element keeps `src`'s order as well as its ids).
        fn fresh<T, I: TypedId>(memo: &[Memo<I>], out: Vec<Option<T>>, base: u32) -> Vec<T> {
            memo.iter()
                .zip(out)
                .filter_map(|(m, row)| match (m, row) {
                    (Memo::Done(id), Some(row)) if id.index() >= base => Some(row),
                    _ => None,
                })
                .collect()
        }

        let src = self.src;
        let types = done(&self.ty_memo, "types")?;
        let func_types = done(&self.functy_memo, "func_types")?;
        let closures = done(&self.closure_memo, "closure_types")?;
        let struct_ids = done(&self.struct_memo, "structs")?;
        let enum_ids = done(&self.enum_memo, "enums")?;
        let record_ids = done(&self.record_memo, "records")?;

        let remap = Remap {
            funcs: self.func_map.clone(),
            types,
            func_types,
            structs: src.structs.iter().map(|d| d.id).zip(struct_ids).collect(),
            enums: src.enums.iter().map(|d| d.id).zip(enum_ids).collect(),
            records: src.records.iter().map(|d| d.id).zip(record_ids).collect(),
            closures,
            globals: self.global_map.clone(),
            preds: self.pred_map.clone(),
            univs: self.univ_map.clone(),
            imports: self.import_map.clone().unwrap_or_default(),
            proofs: self.proof_map.clone(),
            file_indices: match &self.file_map {
                FileMap::Table(map) => map.clone(),
                FileMap::Unchanged | FileMap::Placeholder(_) => Vec::new(),
            },
            dropped_provenance: self.dropped_provenance,
            dropped_gate_evidence: self.dropped_gate_evidence,
            stripped: self.stripped,
            resolved_unlowered,
        };

        let structs = fresh(&self.struct_memo, self.struct_out, self.struct_base);
        let enums = fresh(&self.enum_memo, self.enum_out, self.enum_base);
        let records = fresh(&self.record_memo, self.record_out, self.record_base);
        Ok(Staged {
            remap,
            appended_files: self.new_files,
            rewrite_dst_spans_to: self.rewrite_dst_spans_to,
            universes: self.interned.universes,
            predicates: self.interned.predicates,
            imports: self.interned.imports,
            types: rows(self.ty_out, "types")?,
            func_types: rows(self.functy_out, "func_types")?,
            closure_types: rows(self.closure_out, "closure_types")?,
            structs,
            enums,
            records,
            globals,
            replaced_functions,
            functions,
            proof_obligations,
            proof_certificates,
            obligation_diagnostics,
            spec_modules,
            tuple_layouts,
            closure_layouts,
            global_asm,
            completeness,
            target_info,
            drop_glue,
            blobs,
        })
    }
}

impl Staged {
    fn commit(self, dst: &mut Module) -> Remap {
        if let Some(placeholder) = self.rewrite_dst_spans_to {
            for_each_span_mut(dst, |span| span.file = placeholder);
        }
        dst.files.extend(self.appended_files);
        dst.universes = self.universes;
        dst.predicates = self.predicates;
        dst.imports = self.imports;
        dst.types.extend(self.types);
        dst.func_types.extend(self.func_types);
        dst.closure_types.extend(self.closure_types);
        dst.structs.extend(self.structs);
        dst.enums.extend(self.enums);
        dst.records.extend(self.records);
        dst.globals.extend(self.globals);
        for (pos, func) in self.replaced_functions {
            dst.functions[pos] = func;
        }
        dst.functions.extend(self.functions);
        dst.proof_obligations.extend(self.proof_obligations);
        dst.proof_certificates.extend(self.proof_certificates);
        dst.obligation_diagnostics
            .extend(self.obligation_diagnostics);
        dst.spec_modules.extend(self.spec_modules);
        dst.tuple_layouts.extend(self.tuple_layouts);
        dst.closure_layouts.extend(self.closure_layouts);
        dst.global_asm.extend(self.global_asm);
        dst.completeness = self.completeness;
        dst.target_info = self.target_info;
        dst.drop_glue = self.drop_glue;
        dst.blobs = self.blobs;
        self.remap
    }
}

/// The function a reserved disclosure row key names: `fn:<index>` or
/// `fn:<index>:<rest>`, the index in canonical decimal (the minters'
/// spelling, and the one the validator accepts). Anything else is `None`.
fn disclosure_key_function(key: &str) -> Option<FuncId> {
    let digits = key.strip_prefix("fn:")?.split(':').next()?;
    let canonical = !digits.is_empty()
        && digits.bytes().all(|b| b.is_ascii_digit())
        && (digits == "0" || !digits.starts_with('0'));
    canonical
        .then(|| digits.parse::<u32>().ok())
        .flatten()
        .map(FuncId::new)
}

/// A codegen license with its v61 evidence removed: `Gated` keeps its
/// authority, `Ungated` and `None` are unchanged (never laundered into
/// another licensing state).
fn license_without_evidence(gate: Option<&BodyGate>) -> Option<BodyGate> {
    gate.map(|gate| match gate {
        BodyGate::Gated { authority, .. } => BodyGate::Gated {
            authority: authority.clone(),
            evidence: None,
        },
        BodyGate::Ungated => BodyGate::Ungated,
    })
}

/// The first field (declaration order) in which two same-symbol functions
/// differ, `id` and the dropped `source_provenance` aside (the license is
/// compared without its evidence, which the merger drops). Signatures are
/// compared by `same_signature` (content, not id; see
/// [`Merger::same_signature`]).
fn function_difference(
    a: &Function,
    b: &Function,
    same_signature: impl Fn(FuncTyId, FuncTyId) -> bool,
) -> Option<&'static str> {
    let Function {
        id: _,
        name: a_name,
        ty: a_ty,
        entry: a_entry,
        blocks: a_blocks,
        proofs: a_proofs,
        calling_conv: a_calling_conv,
        linkage: a_linkage,
        attrs: a_attrs,
        summary: a_summary,
        producer: a_producer,
        value_names: a_value_names,
        scopes: a_scopes,
        source_provenance: _,
        body_gate: a_body_gate,
        display_path: a_display_path,
        section: a_section,
        visibility: a_visibility,
        retained: a_retained,
    } = a;
    let Function {
        id: _,
        name: b_name,
        ty: b_ty,
        entry: b_entry,
        blocks: b_blocks,
        proofs: b_proofs,
        calling_conv: b_calling_conv,
        linkage: b_linkage,
        attrs: b_attrs,
        summary: b_summary,
        producer: b_producer,
        value_names: b_value_names,
        scopes: b_scopes,
        source_provenance: _,
        body_gate: b_body_gate,
        display_path: b_display_path,
        section: b_section,
        visibility: b_visibility,
        retained: b_retained,
    } = b;
    let checks: [(&'static str, bool); 17] = [
        ("name", a_name == b_name),
        ("ty", same_signature(*a_ty, *b_ty)),
        ("entry", a_entry == b_entry),
        ("blocks", same(a_blocks, b_blocks)),
        ("proofs", same(a_proofs, b_proofs)),
        ("calling_conv", a_calling_conv == b_calling_conv),
        ("linkage", a_linkage == b_linkage),
        ("attrs", same(a_attrs, b_attrs)),
        ("summary", same(a_summary, b_summary)),
        ("producer", a_producer == b_producer),
        ("value_names", a_value_names == b_value_names),
        ("scopes", a_scopes == b_scopes),
        // The license, compared without its v61 evidence: the merger drops a
        // `src` function's evidence, so the evidence-free image of an
        // identical evidenced definition is the same definition, and `dst`'s
        // copy (evidence included) stands for the validator to recompute in
        // the merged image.
        (
            "body_gate",
            license_without_evidence(a_body_gate.as_ref())
                == license_without_evidence(b_body_gate.as_ref()),
        ),
        ("display_path", a_display_path == b_display_path),
        ("section", a_section == b_section),
        ("visibility", a_visibility == b_visibility),
        ("retained", a_retained == b_retained),
    ];
    checks
        .into_iter()
        .find_map(|(field, equal)| (!equal).then_some(field))
}

/// The first field (declaration order) in which two same-symbol globals
/// differ.
fn global_difference(a: &Global, b: &Global) -> Option<&'static str> {
    let Global {
        name: a_name,
        ty: a_ty,
        mutable: a_mutable,
        initializer: a_initializer,
        linkage: a_linkage,
        tls: a_tls,
        align: a_align,
        section: a_section,
        visibility: a_visibility,
        retained: a_retained,
    } = a;
    let Global {
        name: b_name,
        ty: b_ty,
        mutable: b_mutable,
        initializer: b_initializer,
        linkage: b_linkage,
        tls: b_tls,
        align: b_align,
        section: b_section,
        visibility: b_visibility,
        retained: b_retained,
    } = b;
    let checks: [(&'static str, bool); 10] = [
        ("name", a_name == b_name),
        ("ty", a_ty == b_ty),
        ("mutable", a_mutable == b_mutable),
        ("initializer", same(a_initializer, b_initializer)),
        ("linkage", a_linkage == b_linkage),
        ("tls", a_tls == b_tls),
        ("align", a_align == b_align),
        ("section", a_section == b_section),
        ("visibility", a_visibility == b_visibility),
        ("retained", a_retained == b_retained),
    ];
    checks
        .into_iter()
        .find_map(|(field, equal)| (!equal).then_some(field))
}

fn module_has_spans(module: &Module) -> bool {
    module.functions.iter().any(|f| {
        f.blocks
            .iter()
            .any(|b| b.body.iter().any(|n| n.span.is_some()))
            || f.scopes.as_ref().is_some_and(|scopes| {
                scopes
                    .iter()
                    .any(|s| s.span.is_some() || s.inlined_at.is_some())
            })
    }) || module
        .obligation_diagnostics
        .iter()
        .any(|d| d.location.is_some())
}

/// Every `SourceSpan` a module carries (node spans, scope spans, inlining
/// call sites, diagnostic locations) — the same set the validator range
/// checks against `Module::files`.
fn for_each_span_mut(module: &mut Module, mut visit: impl FnMut(&mut SourceSpan)) {
    for f in &mut module.functions {
        for block in &mut f.blocks {
            for node in &mut block.body {
                if let Some(span) = &mut node.span {
                    visit(span);
                }
            }
        }
        if let Some(scopes) = &mut f.scopes {
            for scope in scopes {
                if let Some(span) = &mut scope.span {
                    visit(span);
                }
                if let Some(link) = &mut scope.inlined_at {
                    visit(&mut link.span);
                }
            }
        }
    }
    for d in &mut module.obligation_diagnostics {
        if let Some(span) = &mut d.location {
            visit(span);
        }
    }
}

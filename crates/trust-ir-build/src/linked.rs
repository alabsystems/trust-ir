// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! LINKED VALIDATION: the import-closure walk that turns every import row,
//! every cross-crate call edge and every proof-bearing cross-crate row of a
//! module into a RE-EARNED verdict.
//!
//! [`crate::validate_module`] validates one module and takes its
//! [`trust_ir::Module::imports`] on faith: a `backed_by` citation or an
//! `external: Some` inheritance is checked to RESOLVE (the import exists, the
//! reference names an obligation) and nothing more. That is the right floor
//! for a format build holding a single artifact, and it is exactly the surface
//! a laundering producer would use. [`validate_linked_module`] is the closure
//! over it:
//!
//! 1. EVERY row of `Module::imports` — cited by a proof-bearing row or not
//!    (WS1.7 / WS4.8, `docs/SPEC_RATIFICATIONS.md` §6; unconditional, there is
//!    no scope knob) — is resolved through an
//!    [`ImportResolver`] and authenticated against the DEPENDENCY MODULE's
//!    digest under the ROW's [`trust_ir::IdentityScheme`]
//!    ([`trust_ir::Module::stable_digest_under`];
//!    [`trust_ir::Module::verify_import_hashed`]
//!    over a [`trust_ir::HashedModule`], whose digest is computed over the
//!    module it holds by construction — never a name, never a caller-asserted
//!    digest);
//! 2. the dependency is itself validated, recursively, under the same rules,
//!    memoized by digest so a diamond validates its shared leaf once, with a
//!    cycle guard and a depth cap;
//! 3. every reference is resolved across the authenticated edge
//!    ([`trust_ir::Module::resolve_extern_ref`]) and its site-specific claim is
//!    re-checked: a `backed_by` summary must restate the far contract EXACTLY
//!    against a `proved` far summary, and the far obligation it cites must be
//!    GROUNDED in the dependency and state one of the restated clauses of the
//!    role its kind backs, and — for a far definition — EVERY restated clause
//!    must be stated by a grounded far row (WS1.3); an inheritance certificate must
//!    discharge the obligation its evidence restates, name a far obligation the
//!    dependency GROUNDED (kernel-tier replay or an authenticated inheritance of
//!    its own — a `Trusted` row or a bare `Discharged` label never), and
//!    restate it with the same kind and formula;
//! 4. (L9) EVERY coverage bound the dependency RECORDED for the far discharge
//!    must be at least as strong as what the local claim needs
//!    ([`coverage_supports`]): an importer must not gain unbounded standing
//!    from a depth-1 bounded check, and
//!    [`trust_ir::proof::CoverageBound::Unrecorded`] is not a wildcard.
//!    The demand is met only when every recorded bound supplies it — a
//!    weakest-link reading, so a producer cannot license a claim its
//!    grounding discharge never covered by ADDING an inflated sibling
//!    certificate. Two states are counted rather than refused, both by
//!    [`LinkedValidationReport::coverage_unrecorded`] and named in
//!    [`LinkedValidationReport::coverage_summary`]: a far record absent
//!    ENTIRELY (the pre-v41 grandfather state) and a local row that records
//!    no grade of its own, so nothing was compared. Neither is read as
//!    agreement, and the counter spans the whole closure, not just the root.
//!
//!    **What L9 is not.** It compares the dependency's OWN recorded
//!    `assurance` against the local demand, and it structurally cannot
//!    re-derive that record: an [`ImportResolver`] yields a bare
//!    [`trust_ir::Module`], never the
//!    `trust_ir::request::NativeVerificationBundle` a bound is projected
//!    from, so "is this the coverage the evidence actually achieved?" is
//!    [`crate::coverage_assurance_report`]'s separate rule over a different
//!    table, and a root verifier that needs it must run that pass with the
//!    bundle in hand. L9 closes the LAUNDERING edge — coverage does not grow
//!    across an import — not the far producer's honesty about its own
//!    discharge;
//! 5. (L10) every CALL EDGE into an authenticated dependency is resolved
//!    across it ([`trust_ir::Module::resolve_extern_ref`] with no obligation:
//!    symbol, export linkage, interposability, producer and
//!    [`trust_ir::signatures_compatible`]). A call edge is a body-less
//!    declaration that either names the far entity with a claim-free
//!    `backed_by` (`ExternRef { obligation: None }`, the explicit spelling),
//!    or carries no `backed_by` and whose link symbol an authenticated
//!    dependency DEFINES and exports (the implicit one). A symbol defined and
//!    exported by two or more distinct dependency artifacts is
//!    [`ValidationError::AmbiguousImportedSymbol`]; any other failure is
//!    [`ValidationError::UnauthenticatedImport`] with `site: "call"` —
//!    including a declaration bound to a dependency's DATA export and a
//!    `Constant::SymbolAddr` of a dependency function with no local
//!    declaration (a call edge nothing could signature-check). The edge is
//!    resolved at [`trust_ir::ExternRefSite::CallEdge`], which relies on no
//!    obligation and admits a local `ExternalWeak` import. A
//!    declaration no authenticated dependency exports is an FFI extern
//!    (libc, a runtime) or a dependency the producer never recorded: legal,
//!    and COUNTED in [`LinkedValidationReport::unbound_declarations`] so the
//!    residue is visible, never silent;
//! 6. (L11, WS3.3) every IMPORT-BACKED HANDLE DECLARATION — a body-less,
//!    non-pinned declaration whose signature reaches a v43 `Ty::Handle` and
//!    whose summary carries a `backed_by` (the DG-26 binding spelling:
//!    `ExternRef { module, symbol: <own name>, obligation: None }`) — is
//!    resolved at [`trust_ir::ExternRefSite::HandleDeclaration`] through
//!    [`trust_ir::Module::resolve_handle_declaration`]: R1–R6 with R4
//!    HARDENED to a far DEFINITION that is not an `AvailableExternally` copy,
//!    or a far declaration the dependency's own verdict authenticated as a
//!    handle declaration. The body the binding bottoms out in must also be
//!    the only one a DIRECT import exports under the symbol (the shadow
//!    rule: a re-declaration is not an exporter, so the call-edge ambiguity
//!    rule cannot see a rogue definition beside a chain). The outcome is what rule 6
//!    (`HandleForeignDeclaration`) consults; only this walk can admit such a
//!    declaration, so `validate_module`, the authority tier and plain codegen
//!    keep refusing it (fail closed). A consumer that compiles such a root
//!    uses [`validate_linked_module_with_config`] with `codegen` set;
//! 7. (L12, WS3.9) NOMINAL TYPE IDENTITY agrees across the WHOLE CLOSURE: a
//!    v58 [`trust_ir::ty::TypeOrigin`] key stamped on definitions of any TWO
//!    modules the walk validates — root and dependency, two siblings, or two
//!    modules that meet only through a transitive import — must name
//!    structurally equal definitions ([`trust_ir::imports::ty_structurally_eq_across`]),
//!    or the pair is [`ValidationError::TypeOriginConflict`], reported on the
//!    root with both modules named. The rule is refuse-only: a key one module
//!    carries alone, two DIFFERENT keys, and an unkeyed definition are each
//!    not a finding, and nothing is admitted because of a key. Closure-wide
//!    because a program links every module of its closure, so one entity
//!    with two shapes anywhere in it makes neither shape usable — a check
//!    confined to an importer and its direct rows would miss two siblings;
//! 8. the module validator then runs under
//!    `ImportPolicy::Authenticated`, with a [`trust_ir::proof::ModuleProofAuthority`]
//!    that admits exactly the authenticated inheritance certificates into the
//!    `Discharged` tier — never into the kernel tier, so an inherited proof can
//!    ground its own restatement and nothing else.
//!
//! Every refusal is a named [`ValidationError`]; `None` is never a wildcard
//! (an unresolvable import, an absent digest, an unscoped obligation, an
//! unrecorded producer, an empty `obligation` each refuse the claim that would
//! need them). Nothing here touches the wire.
//!
//! **What the walk cannot see.** It authenticates every row a module RECORDS
//! and every call edge that binds, by symbol, into a recorded dependency. It
//! cannot make a producer RECORD a row: a module that calls a dependency
//! symbol without interning an import for it reads as an FFI extern, and is
//! counted in [`LinkedValidationReport::unbound_declarations`] rather than
//! refused. Closing that half needs producers that intern a row per
//! dependency (WS5 / F-093).

use std::collections::{BTreeMap, BTreeSet};
use std::rc::Rc;

use trust_ir::imports::ty_structurally_eq_across;
use trust_ir::inst::Inst;
use trust_ir::proof::{
    CoverageBound, ModuleProofAuthority, ProofCertificate, ProofCertificateRef, ProofDigest,
    ProofEvidence, ProofObligation,
};
use trust_ir::ty::{Ty, TypeOrigin};
use trust_ir::value::{FuncId, ImportId, ProofId};
use trust_ir::{
    Constant, ExternRef, ExternRefSite, FunctionSummary, HashedModule, IdentityScheme, Linkage,
    Module, ModuleImport, Producer,
};

use crate::validate::{
    ContractClauseRole, ImportPolicy, ValidationConfig, ValidationError,
    extend_with_config_codegen_errors, validate_module_filtered,
};

/// The deepest import chain [`validate_linked_module`] follows before refusing
/// with [`ValidationError::ImportClosureTooDeep`]. The root is depth 0.
pub const MAX_IMPORT_DEPTH: usize = 64;

/// Supplies the dependency module an import names.
///
/// A resolver is a LOOKUP, never an authority: whatever it returns is
/// authenticated against the import's recorded digest before anything is
/// relied on, so a resolver that returns the wrong module (or the importer
/// itself) produces a named refusal rather than a false verdict.
pub trait ImportResolver<'a> {
    /// The candidate module for `import`, or `None` when the resolver holds
    /// none — reported as [`ValidationError::ImportUnavailable`].
    fn resolve(&self, import: &ModuleImport) -> Option<&'a Module>;
}

impl<'a, F> ImportResolver<'a> for F
where
    F: Fn(&ModuleImport) -> Option<&'a Module>,
{
    fn resolve(&self, import: &ModuleImport) -> Option<&'a Module> {
        self(import)
    }
}

/// A set of candidate dependency modules keyed by their identity digests
/// under EVERY [`trust_ir::IdentityScheme`] — the portable V3
/// [`trust_ir::Module::stable_digest`] and the legacy V2 digest — and NOTHING
/// else: [`ModuleImport::name`] is ignored on lookup, because two modules may
/// share a name and a proof is about exactly one of them.
///
/// Keying on both is what lets one set serve a V3 row and a pre-v44 V2 row
/// naming the same artifact. The two digests live under different domains, so
/// a V2 digest can never select a module through its V3 key or vice versa;
/// [`ImportResolver::resolve`] also looks up only the row's own scheme.
/// Digests are computed once per scheme, at insertion.
#[derive(Debug, Default, Clone)]
pub struct ModuleSet<'a> {
    by_digest: BTreeMap<(IdentityScheme, ProofDigest), &'a Module>,
}

impl<'a> ModuleSet<'a> {
    /// Index `modules` by stable digest.
    pub fn new(modules: impl IntoIterator<Item = &'a Module>) -> Self {
        let mut set = Self::default();
        for module in modules {
            set.insert(module);
        }
        set
    }

    /// Index `module` under every identity scheme, returning its
    /// [`trust_ir::Module::stable_digest`] (the current scheme). Two modules
    /// with one digest under a scheme are one module under it; the first
    /// inserted is kept.
    pub fn insert(&mut self, module: &'a Module) -> ProofDigest {
        for scheme in IdentityScheme::ALL {
            self.by_digest
                .entry((scheme, module.stable_digest_under(scheme)))
                .or_insert(module);
        }
        module.stable_digest()
    }

    /// Decode one binary module into the caller-owned `store` — through the
    /// canonical reader, so an unknown tag or a trailing byte refuses at load —
    /// and return its stable digest. Build the set afterwards with
    /// `ModuleSet::new(store.iter())`; the set borrows the store, which is why
    /// decoding cannot insert directly.
    #[cfg(feature = "binary")]
    pub fn decode_into(
        store: &mut Vec<Module>,
        bytes: &[u8],
    ) -> Result<ProofDigest, trust_ir::binary::BinaryError> {
        let module = trust_ir::binary::deserialize_module(bytes)?;
        let digest = module.stable_digest();
        store.push(module);
        Ok(digest)
    }

    /// The module whose [`trust_ir::Module::stable_digest`] (the current
    /// scheme) is `digest`, if any.
    #[must_use]
    pub fn get(&self, digest: &ProofDigest) -> Option<&'a Module> {
        self.get_under(IdentityScheme::CURRENT, digest)
    }

    /// The module whose digest under `scheme` is `digest`, if any.
    #[must_use]
    pub fn get_under(&self, scheme: IdentityScheme, digest: &ProofDigest) -> Option<&'a Module> {
        self.by_digest.get(&(scheme, *digest)).copied()
    }

    /// Number of distinct modules held (by current-scheme digest).
    #[must_use]
    pub fn len(&self) -> usize {
        self.by_digest
            .keys()
            .filter(|(scheme, _)| *scheme == IdentityScheme::CURRENT)
            .count()
    }

    /// Whether the set holds no module.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.by_digest.is_empty()
    }
}

impl<'a> ImportResolver<'a> for ModuleSet<'a> {
    fn resolve(&self, import: &ModuleImport) -> Option<&'a Module> {
        self.get_under(import.scheme, &import.digest)
    }
}

/// The outcome the linked validator recorded for one proof-bearing site of a
/// module, consumed by `ImportPolicy::Authenticated`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum SiteOutcome {
    /// Re-earned: the module validator treats the site as backed.
    Authenticated,
    /// Refused with `detail`; the module validator reports
    /// [`ValidationError::UnauthenticatedImport`] for the site.
    Refused(String),
    /// Refused, and the linked validator already reported a more specific
    /// error for the site (an import-level failure, or
    /// [`ValidationError::ExternInheritanceRestatementMismatch`]); the module
    /// validator adds nothing.
    Reported,
}

/// What [`validate_linked_module`] authenticated for ONE module: the digests
/// its import rows were re-earned against, and the per-site outcomes the
/// module validator consults under `ImportPolicy::Authenticated`.
#[derive(Debug, Clone, Default)]
pub struct AuthenticatedImports {
    /// Import rows that authenticated — EVERY row of the table, cited or not
    /// — with the digest they were verified under (equal to the recorded one
    /// by construction).
    digests: BTreeMap<ImportId, ProofDigest>,
    /// Per summary owner: the `backed_by` outcome.
    backed_by: BTreeMap<u32, SiteOutcome>,
    /// Per inheritance certificate: the outcome.
    inherited: BTreeMap<ProofCertificateRef, SiteOutcome>,
    /// The inheritance certificates that authenticated — what the linked
    /// proof authority admits into the `Discharged` tier.
    admitted: BTreeSet<ProofCertificateRef>,
    /// Per import-backed handle declaration (L11, WS3.3): the outcome rule 6
    /// consults. Keyed by the declaration's `FuncId` index.
    handle_declarations: BTreeMap<u32, SiteOutcome>,
    /// Per AUTHENTICATED import-backed handle declaration: the
    /// current-scheme digest of the module whose DEFINITION its binding
    /// bottoms out in (directly, or through a chain of authenticated
    /// re-declarations). An importer re-binding to this declaration compares
    /// it against every direct exporter of the symbol.
    handle_declaration_bodies: BTreeMap<u32, ProofDigest>,
}

#[cfg(test)]
mod observed_effect_admission_tests;
#[cfg(test)]
mod observed_effect_body_tests;
#[cfg(test)]
mod observed_handle_foreign_tests;
#[cfg(test)]
mod observed_inheritance_fixtures;
mod observed_inherited_outcome;
mod observed_summary_outcome;
#[cfg(test)]
mod observed_summary_whole_tests;

impl AuthenticatedImports {
    /// Import rows that authenticated, cited or not, with their digests.
    #[must_use]
    pub fn digests(&self) -> &BTreeMap<ImportId, ProofDigest> {
        &self.digests
    }

    /// Summary owners whose `backed_by` citation re-earned `proved`.
    pub fn authenticated_backed_by(&self) -> impl Iterator<Item = FuncId> + '_ {
        self.backed_by
            .iter()
            .filter(|(_, outcome)| **outcome == SiteOutcome::Authenticated)
            .map(|(function, _)| FuncId::new(*function))
    }

    /// Inheritance certificates whose cross-crate claim re-earned.
    #[must_use]
    pub fn authenticated_inheritances(&self) -> &BTreeSet<ProofCertificateRef> {
        &self.admitted
    }

    /// Import-backed handle declarations (L11) whose binding to a dependency
    /// definition — or to an authenticated handle declaration of the
    /// dependency — re-earned. These, and no other non-pinned declaration
    /// reaching a handle, are admitted by rule 6 under the linked walk.
    pub fn authenticated_handle_declarations(&self) -> impl Iterator<Item = FuncId> + '_ {
        self.handle_declarations
            .iter()
            .filter(|(_, outcome)| **outcome == SiteOutcome::Authenticated)
            .map(|(function, _)| FuncId::new(*function))
    }

    /// The current-scheme digest of the module defining the body an
    /// authenticated handle declaration's binding bottoms out in.
    fn handle_declaration_body(&self, function: FuncId) -> Option<ProofDigest> {
        self.handle_declaration_bodies
            .get(&function.index())
            .copied()
    }

    pub(crate) fn handle_declaration_outcome(&self, function: FuncId) -> Option<&SiteOutcome> {
        self.handle_declarations.get(&function.index())
    }

    pub(crate) fn backed_by_outcome(&self, function: FuncId) -> Option<&SiteOutcome> {
        self.backed_by.get(&function.index())
    }

    pub(crate) fn inherited_outcome(
        &self,
        certificate: &ProofCertificateRef,
    ) -> Option<&SiteOutcome> {
        self.inherited.get(certificate)
    }

    fn record_backed_by(&mut self, function: FuncId, outcome: SiteOutcome) {
        self.backed_by.insert(function.index(), outcome);
    }

    fn record_inherited(&mut self, certificate: &ProofCertificate, outcome: SiteOutcome) {
        let reference = certificate.lineage_ref();
        if outcome == SiteOutcome::Authenticated {
            self.admitted.insert(reference.clone());
        }
        self.inherited.insert(reference, outcome);
    }
}

/// A body-less declaration that no authenticated dependency defines and
/// exports, and that names no import through `backed_by`.
///
/// Legal — an FFI extern (libc, a runtime) looks exactly like this — but NOT
/// authenticated: nothing checked what the linker will bind the symbol to.
/// It is also the shape of a call into a dependency the producer never
/// recorded an import row for, which is why
/// [`LinkedValidationReport::unbound_declarations`] reports it rather than
/// staying silent.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct UnboundDeclaration {
    /// `Module::name` of the module carrying the declaration.
    pub module: String,
    /// The declaration's link symbol (`Function::name`).
    pub symbol: String,
}

/// The verdict of [`validate_linked_module`] on a root module and its import
/// closure.
#[derive(Debug)]
pub struct LinkedValidationReport<'a> {
    root: &'a Module,
    errors: Vec<ValidationError>,
    authenticated: AuthenticatedImports,
    replayed: BTreeSet<ProofCertificateRef>,
    coverage: CoverageTally,
    handle_registry_is_pinned: bool,
    call_edges: CallEdgeTally,
}

impl<'a> LinkedValidationReport<'a> {
    /// Whether EVERY module of the closure was validated under the pinned
    /// handle-runtime registry ([`ValidationConfig::handle_registry_is_pinned`]).
    /// The walk has exactly one config, so this is one bit for the whole
    /// closure. Reported regardless of the verdict; `false` means a
    /// caller-supplied registry — a caller-owned TCB extension — decided which
    /// handle entry points are trusted, and a consumer that compiles the root
    /// MUST check it.
    #[must_use]
    pub fn handle_registry_is_pinned(&self) -> bool {
        self.handle_registry_is_pinned
    }

    /// Every error, root and closure. Closure errors arrive folded into
    /// [`ValidationError::ImportedModuleInvalid`] on the citing import.
    pub fn errors(&self) -> &[ValidationError] {
        &self.errors
    }

    /// Whether the root and its whole cited closure validated.
    pub fn is_ok(&self) -> bool {
        self.errors.is_empty()
    }

    /// The exact root module, only when the complete linked pass succeeded.
    pub fn validated_root(&self) -> Option<&'a Module> {
        self.errors.is_empty().then_some(self.root)
    }

    /// The root's import rows — every row, cited or not — and the digests
    /// they were authenticated against, only when the complete linked pass
    /// succeeded.
    pub fn authenticated_imports(&self) -> Option<&BTreeMap<ImportId, ProofDigest>> {
        self.errors
            .is_empty()
            .then_some(&self.authenticated.digests)
    }

    /// The root's inheritance certificates whose cross-crate claim re-earned —
    /// the rows the linked proof authority admitted into the `Discharged`
    /// tier — only when the complete linked pass succeeded. These are NOT
    /// kernel-tier authority; see [`Self::replayed_certificate_refs`].
    pub fn authenticated_certificate_refs(&self) -> Option<&BTreeSet<ProofCertificateRef>> {
        self.errors
            .is_empty()
            .then_some(&self.authenticated.admitted)
    }

    /// The root's kernel-tier certificate references, exactly as
    /// [`crate::ModuleValidationReport::replayed_certificate_refs`] reports
    /// them, only when the complete linked pass succeeded.
    pub fn replayed_certificate_refs(&self) -> Option<&BTreeSet<ProofCertificateRef>> {
        self.errors.is_empty().then_some(&self.replayed)
    }

    /// Per-site detail of what was authenticated on the root, only when the
    /// complete linked pass succeeded.
    pub fn authenticated(&self) -> Option<&AuthenticatedImports> {
        self.errors.is_empty().then_some(&self.authenticated)
    }

    /// CLOSURE cross-crate sites whose far discharge RECORDED coverage at
    /// least as strong as the local claim needs (linked rule L9).
    ///
    /// Every module the walk validated, root and dependencies, counted once
    /// per distinct module (the digest memo dedups a diamond's shared leaf).
    /// Root-only would be the unsound scoping: a dependency's UNRECORDED site
    /// is not an error, so it can never arrive folded into
    /// [`ValidationError::ImportedModuleInvalid`], and the root's own claim
    /// chains through that dependency's unqualified `proved`.
    #[must_use]
    pub fn coverage_supported(&self) -> usize {
        self.coverage.supported
    }

    /// CLOSURE cross-crate sites whose coverage was NOT ESTABLISHED — the
    /// far obligation has no certificate recording a bound (the pre-v41
    /// grandfather state), or the LOCAL row records no grade of its own, so
    /// there was nothing to compare.
    ///
    /// **Not a refusal and not agreement.** Nothing in the fleet stamps
    /// `ProofCertificate::assurance` yet, so refusing this would fail every
    /// module produced today; reading its silence as support would be the
    /// unsound half of the same choice. It is counted so the choice is
    /// visible, exactly as `CoverageAssuranceReport::undetermined` is.
    ///
    /// Both states land here for the same reason: nothing positive was
    /// established about how much of the input space the cited discharge
    /// covered. Counting a no-grade LOCAL row as `coverage_supported` would
    /// relocate the forge this rule closes — absence read as agreement — from
    /// the far row onto the near one and into the tally.
    ///
    /// A caller that needs every cross-crate claim's coverage ESTABLISHED
    /// admits only on
    ///
    /// ```text
    /// report.is_ok() && report.coverage_unrecorded() == 0
    /// ```
    ///
    /// Dropping the second conjunct admits an unqualified `proved` summary
    /// whose dependency recorded nothing about how much of the input space
    /// its discharge covered. Note what the conjunction does NOT establish:
    /// that a recorded bound is FAITHFUL to the evidence behind it — see the
    /// module docs' "what L9 is not".
    #[must_use]
    pub fn coverage_unrecorded(&self) -> usize {
        self.coverage.unrecorded
    }

    /// CLOSURE cross-crate sites REFUSED by L9, each already named by its own
    /// [`ValidationError::ImportCoverageBelowClaim`].
    ///
    /// Reported separately so [`Self::coverage_summary`]'s denominator is the
    /// real site count: a refusal folded into neither the numerator nor the
    /// total would let a one-supported-one-refused module print as complete.
    #[must_use]
    pub fn coverage_refused(&self) -> usize {
        self.coverage.refused
    }

    /// One line a report or CLI can print. It says UNRECORDED and REFUSED out
    /// loud, so neither absence nor a refusal can be rendered as agreement.
    #[must_use]
    pub fn coverage_summary(&self) -> String {
        let sites = self.coverage.supported + self.coverage.unrecorded + self.coverage.refused;
        format!(
            "cross-crate coverage: {} of {} proof-bearing cross-crate site{} supported by a \
             recorded far bound, {} left UNRECORDED (not agreement — admit only at 0), {} \
             REFUSED as below the local claim",
            self.coverage.supported,
            sites,
            if sites == 1 { "" } else { "s" },
            self.coverage.unrecorded,
            self.coverage.refused,
        )
    }

    /// CLOSURE call edges (L10) resolved across an authenticated import:
    /// symbol, export linkage, producer and signature all agreed. Counted
    /// once per distinct module, like the coverage tally. An authenticated
    /// import-backed handle declaration (L11) is a call edge too, resolved at
    /// the stricter handle site, and is counted here.
    #[must_use]
    pub fn authenticated_call_edges(&self) -> usize {
        self.call_edges.authenticated
    }

    /// CLOSURE body-less declarations bound to NO authenticated dependency
    /// (L10): FFI externs, or calls into a dependency the producer never
    /// recorded a row for. Not a refusal and not agreement — nothing checked
    /// what the linker binds them to. Reported whether or not the pass
    /// succeeded, so the residue is visible on a green verdict too.
    #[must_use]
    pub fn unbound_declarations(&self) -> &[UnboundDeclaration] {
        &self.call_edges.unbound
    }

    /// One line a report or CLI can print for L10. It names the unbound
    /// declarations out loud, so an FFI extern is never rendered as an
    /// authenticated edge.
    #[must_use]
    pub fn call_edge_summary(&self) -> String {
        let unbound = &self.call_edges.unbound;
        let mut line = format!(
            "cross-crate call edges: {} authenticated against a supplied dependency, {} body-less \
             declaration{} bound to NO supplied dependency (FFI extern or unrecorded import — \
             not authenticated)",
            self.call_edges.authenticated,
            unbound.len(),
            if unbound.len() == 1 { "" } else { "s" },
        );
        if !unbound.is_empty() {
            let named: Vec<String> = unbound
                .iter()
                .map(|decl| format!("{}::{}", decl.module, decl.symbol))
                .collect();
            line.push_str(": ");
            line.push_str(&named.join(", "));
        }
        line
    }

    pub fn into_errors(self) -> Vec<ValidationError> {
        self.errors
    }
}

/// Validate `root` and authenticate every import row, every cross-crate call
/// edge and every proof-bearing cross-crate row it carries against the
/// dependency modules `resolver` supplies, recursively.
///
/// Every row is authenticated UNCONDITIONALLY (DG-78): there is no option
/// that restricts the walk to cited rows, because such a knob would be a way
/// back to unauthenticated import rows. An import row whose dependency the
/// resolver cannot supply is therefore refused even when nothing cites it.
///
/// `authority` is the [`ModuleProofAuthority`] every module in the closure is
/// validated under (the same capability [`crate::validate_module_with_authority`]
/// takes). Pass [`trust_ir::proof::RejectingModuleProofAuthority`] for a
/// consumer that can replay nothing itself; kernel-tier `Certified` rows still
/// re-check in-process.
///
/// See the module docs for the algorithm; the per-import check order is
/// normative and each failure names itself.
///
/// This is [`validate_linked_module_with_config`] under
/// `ValidationConfig::pinned().with_authority(authority)`: the pinned handle
/// registry, no dialect schemas, no codegen layers.
pub fn validate_linked_module<'a>(
    root: &'a Module,
    resolver: &dyn ImportResolver<'a>,
    authority: &dyn ModuleProofAuthority,
) -> LinkedValidationReport<'a> {
    validate_linked_module_with_config(
        root,
        resolver,
        &ValidationConfig::pinned().with_authority(authority),
    )
}

/// [`validate_linked_module`] under an explicit handle-runtime `registry`
/// (roadmap WS1.5, the registry half of F-009): exactly
/// [`validate_linked_module_with_config`] under
/// `ValidationConfig::pinned().with_authority(authority).with_handle_registry(registry)`,
/// so one registry decides for the whole closure.
///
/// A registry other than [`crate::HandleRegistry::pinned`] is a caller-owned
/// TCB extension: every row it adds is an entry point the caller vouches for,
/// and [`LinkedValidationReport::handle_registry_is_pinned`] records that.
pub fn validate_linked_module_with<'a>(
    root: &'a Module,
    resolver: &dyn ImportResolver<'a>,
    authority: &dyn ModuleProofAuthority,
    registry: &crate::validate::HandleRegistry,
) -> LinkedValidationReport<'a> {
    validate_linked_module_with_config(
        root,
        resolver,
        &ValidationConfig::pinned()
            .with_authority(authority)
            .with_handle_registry(registry),
    )
}

/// [`validate_linked_module`] under an explicit [`ValidationConfig`]: its
/// authority, handle registry, dialect schemas and codegen intent.
///
/// # One config for the whole closure
///
/// Every module the walk validates — the root and each cited dependency,
/// recursively — runs under THIS config. There is no per-dependency config:
/// a dependency cannot be admitted under a laxer registry than the root, and
/// with `codegen` set every module in the closure must also pass the codegen
/// layers (a dependency that fails them arrives folded into
/// [`ValidationError::ImportedModuleInvalid`]). A consumer that wants the
/// codegen layers on the root only composes
/// [`crate::validate_linked_module_with_config`] without codegen with
/// [`crate::codegen_license_errors`] / [`crate::codegen_lowerability_errors`]
/// / [`crate::codegen_global_asm_errors`] on the root.
///
/// The config's single-module import policy is irrelevant here: the walk
/// always runs its own authenticated policy.
///
/// # No verdict leaks between walks
///
/// The per-digest memo lives in this call's context and dies with it, so a
/// dependency verdict earned under a permissive registry is never reused by a
/// later walk under [`ValidationConfig::pinned`].
/// [`LinkedValidationReport::handle_registry_is_pinned`] records which
/// registry decided.
pub fn validate_linked_module_with_config<'a>(
    root: &'a Module,
    resolver: &dyn ImportResolver<'a>,
    config: &ValidationConfig<'_>,
) -> LinkedValidationReport<'a> {
    let mut ctx = LinkContext {
        resolver,
        config,
        memo: BTreeMap::new(),
        stack: Vec::new(),
        coverage: CoverageTally::default(),
        call_edges: CallEdgeTally::default(),
        type_origins: BTreeMap::new(),
        type_origin_conflicts: Vec::new(),
    };
    // The walk is keyed on the root's digest (memo, cycle guard, every import
    // row's authentication). A root with no wire identity has none to key on:
    // refuse it by name instead of panicking inside `stable_digest`. Nothing
    // is authenticated and nothing is replayed.
    if let Some(error) = crate::validate::wire_identity_blocker(root) {
        return LinkedValidationReport {
            root,
            errors: vec![error],
            authenticated: AuthenticatedImports::default(),
            replayed: BTreeSet::new(),
            coverage: ctx.coverage,
            handle_registry_is_pinned: config.handle_registry_is_pinned(),
            call_edges: ctx.call_edges,
        };
    }
    let root_digest = root.stable_digest();
    ctx.stack.push((root_digest, root.name.clone()));
    let verdict = validate_one(root, &mut ctx, 0);
    ctx.stack.pop();
    // L12 is a verdict on the CLOSURE, so its refusals are the root's: a
    // dependency that agrees with itself is not made invalid by a sibling.
    let mut errors = verdict.errors.clone();
    errors.extend(ctx.type_origin_conflicts);
    LinkedValidationReport {
        root,
        errors,
        authenticated: verdict.authenticated.clone(),
        replayed: verdict.replayed.clone(),
        // CLOSURE-wide, not `verdict.coverage`: see `coverage_supported`.
        coverage: ctx.coverage,
        handle_registry_is_pinned: config.handle_registry_is_pinned(),
        call_edges: ctx.call_edges,
    }
}

/// Running tally of L10 outcomes across the import closure.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
struct CallEdgeTally {
    /// Call edges resolved across an authenticated import.
    authenticated: usize,
    /// Declarations no authenticated dependency exports.
    unbound: Vec<UnboundDeclaration>,
}

/// The verdict on one module in the closure, shared through the memo.
struct ModuleVerdict {
    errors: Vec<ValidationError>,
    /// Obligations this module GROUNDED: kernel-tier replayed ∪ discharged by
    /// an authenticated inheritance. What an importer may inherit from.
    ground: BTreeSet<ProofId>,
    /// Kernel-tier certificate refs, as the module validator reports them.
    replayed: BTreeSet<ProofCertificateRef>,
    authenticated: AuthenticatedImports,
}

struct LinkContext<'a, 'r> {
    resolver: &'r dyn ImportResolver<'a>,
    /// The ONE config every module of the closure is validated under.
    config: &'r ValidationConfig<'r>,
    /// Completed verdicts keyed by the module's ACTUAL stable digest, local
    /// to one walk (never shared across calls, so no verdict earned under one
    /// config is reused under another). The value holds the [`HashedModule`],
    /// so a memo hit re-runs the per-edge checks against a digest that was
    /// COMPUTED over that module — the type admits no other.
    ///
    /// Keyed by `(scheme, digest)`: an edge looks up the digest under its
    /// ROW's scheme, and every validated module is entered under each scheme
    /// its hashed handle has computed, so a diamond whose two edges record
    /// the shared leaf under different schemes still validates it once.
    memo: BTreeMap<(IdentityScheme, ProofDigest), (HashedModule<'a>, Rc<ModuleVerdict>)>,
    /// Modules currently being validated, root first: `(digest, name)`, the
    /// digest under [`IdentityScheme::CURRENT`] whatever scheme the edge that
    /// reached the module recorded, so a cycle closed through rows of mixed
    /// schemes is still detected as the cycle it is.
    stack: Vec<(ProofDigest, String)>,
    /// L9 outcomes for EVERY module the walk validates, accumulated across
    /// the closure. Lives here rather than on [`ModuleVerdict`] because the
    /// memo guarantees each distinct module is validated exactly once, so a
    /// diamond's shared leaf contributes its sites once; and because a
    /// dependency's UNRECORDED site is not an error and therefore has no
    /// other route to the root's report.
    coverage: CoverageTally,
    /// L10 outcomes for every module the walk validates, closure-wide for the
    /// same reason as `coverage`: an unbound declaration is not an error.
    call_edges: CallEdgeTally,
    /// L12: the FIRST module of the walk to claim each nominal type key, with
    /// the definition it stamped it on. Closure-wide, because a program links
    /// every module of its closure: two modules that share no import edge
    /// still contribute their type images to one program.
    type_origins: BTreeMap<TypeOrigin, ClaimedTypeOrigin<'a>>,
    /// L12 refusals, closure-wide, reported on the ROOT (with both modules
    /// named) rather than folded into an `ImportedModuleInvalid`: a dependency
    /// that agrees with itself is not invalid, the CLOSURE is.
    type_origin_conflicts: Vec<ValidationError>,
}

/// One definition's claim on a nominal key, as first seen by the walk.
struct ClaimedTypeOrigin<'a> {
    module: &'a Module,
    table: &'static str,
    name: String,
    ty: Ty,
}

/// One proof-bearing cross-crate row of a module.
enum Site<'m> {
    BackedBy {
        local: FuncId,
        summary: &'m FunctionSummary,
        reference: &'m ExternRef,
    },
    Inherited {
        certificate: &'m ProofCertificate,
        callee: FuncId,
        restatement: ProofId,
        reference: &'m ExternRef,
    },
}

/// L9's partial order over coverage grades: does the far certificate's
/// recorded bound supply what the local claim demands?
///
/// Defined in `trust-ir-laws` and re-exported here at its historical path.
/// Its English table lives on the definition, and every row of that table
/// except the unknown-variant one is a PROVED Trust contract (kernel-rechecked
/// under the `verified-contracts` gate, `scripts/verified_contracts.py`);
/// transitivity is the documented hand step. The tested twin over every pair
/// is `coverage_supports_is_the_ratified_partial_order_over_every_pair`.
pub use trust_ir_laws::coverage_supports;

/// L9's verdict for one cross-crate site.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum CoverageVerdict {
    /// EVERY certificate of the far obligation that records a coverage bound
    /// records one that [`coverage_supports`] the local claim.
    Supported,
    /// NO certificate of the far obligation records a coverage bound at all —
    /// the pre-v41 grandfather state, since nothing in the fleet stamps
    /// `assurance` yet.
    ///
    /// Not a refusal, and not agreement either: refusing it would fail every
    /// module produced before v41 (and every one produced today), while
    /// reading its silence as support would be the unsound half of the same
    /// choice. It is COUNTED instead, on the precedent
    /// `CoverageAssuranceReport::undetermined` already sets — a caller that
    /// needs coverage ESTABLISHED admits only when the count is zero.
    Unrecorded,
    /// At least one recorded far bound is weaker than, or incomparable with,
    /// the demand.
    Insufficient { recorded: Vec<CoverageBound> },
}

/// Running tally of L9 outcomes across the import closure, so neither the
/// grandfather state nor a refusal is invisible in the one line a report
/// prints.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
struct CoverageTally {
    /// Every recorded far bound supplied a POSITIVE local demand.
    supported: usize,
    /// Nothing positive was established: no far record at all, or a local row
    /// that records no grade.
    unrecorded: usize,
    /// Refused by L9 and named by `ImportCoverageBelowClaim`.
    refused: usize,
}

/// L9 for one site: compare the POSITIVE local demand `needs` against every
/// coverage bound `dependency`'s certificates record for `far_obligation`.
/// The same-module inheritance rule (WS1.6, `validate::admit_local_inheritance`)
/// calls it with the module itself as `dependency`.
///
/// # The supply is every recorded bound, and every one of them must supply
///
/// An obligation may carry SEVERAL certificates — uniqueness is only over
/// `(obligation, prover)` — and `Certified` needs just one matching
/// `CleanCic` row, so the bound the grounding discharge recorded sits beside
/// bounds recorded by provers this walk grants no authority at all (a
/// non-replayed `SmtProof`, a `Trusted` audit note). Narrowing the supply to
/// the GROUNDING certificates is not available as a uniform rule: a
/// `backed_by` site has no grounding requirement, so the two site kinds would
/// end up under different rules.
///
/// So the demand is met only when EVERY recorded bound supplies it — the
/// weakest-link reading. That is the sound direction of the choice, and the
/// reason is monotonicity: under the `any` reading a producer LICENSES a
/// stronger cross-crate claim by ADDING a decorative certificate that nothing
/// replays, and a depth-1 kernel discharge beside an `Unbounded` sibling
/// re-earns unbounded standing downstream — exactly the laundering L9 exists
/// to refuse. Under `all`, adding a row can only refuse more.
///
/// The cost is named: a dependency that carries an honest weak corroboration
/// (a depth-1 BMC beside an unbounded proof of the same obligation) records
/// the weaker coverage for that obligation, and an importer needing the
/// stronger grade is refused. The producer's recourse is not to hide the
/// corroboration but to state the obligation it actually covers — an
/// obligation's recorded coverage is its weakest certificate's, by
/// construction.
///
/// `needs` is never [`CoverageBound::Unrecorded`] here: a local row claiming
/// no grade is counted by [`check_coverage`] before this is reached, because
/// "nothing to compare" is not the same verdict as "the far bound supplied
/// it".
pub(crate) fn coverage_verdict(
    dependency: &Module,
    far_obligation: ProofId,
    needs: CoverageBound,
) -> CoverageVerdict {
    debug_assert_ne!(needs, CoverageBound::Unrecorded);
    let recorded: Vec<CoverageBound> = dependency
        .proof_certificates
        .iter()
        .filter(|certificate| certificate.obligation == far_obligation)
        .filter_map(|certificate| certificate.assurance.map(|assurance| assurance.bound))
        .collect();
    if recorded.is_empty() {
        return CoverageVerdict::Unrecorded;
    }
    if recorded
        .iter()
        .all(|bound| coverage_supports(*bound, needs))
    {
        return CoverageVerdict::Supported;
    }
    CoverageVerdict::Insufficient { recorded }
}

/// What a `backed_by` site NEEDS: [`CoverageBound::Unbounded`].
///
/// `FunctionSummary::proved` is a bare `bool` with no coverage field, and its
/// own rustdoc states the unqualified reading — "A caller may *assume* these
/// only when `proved` is set", with no restriction on inputs. So a summary
/// that re-states a far contract as `proved` claims it for ALL inputs, and a
/// far discharge that explored a bounded prefix does not establish that.
///
/// A producer that wants to publish a bounded contract has the honest
/// spelling already: leave `proved` false (the call stays havoced), or carry
/// the claim as an inheritance certificate whose `assurance` records the
/// bound it actually achieved.
const BACKED_BY_NEEDS: CoverageBound = CoverageBound::Unbounded;

/// What an inheritance site NEEDS: exactly the coverage its own certificate
/// declares.
///
/// `assurance: None` is NOT RECORDED, so the local row claims no grade and
/// demands none — sound as a REFUSAL rule, because a fail-closed consumer
/// already reads that row as UNKNOWN coverage, never as `Unbounded`
/// ([`trust_ir::proof::ProofCertificate::assurance`]'s own rule).
///
/// It is NOT free, and this rustdoc used to claim it was. Dropping the field
/// really does turn an L9 refusal into an admission — that is what "demands
/// none" means. What the producer does not get is STANDING: a no-grade row is
/// counted by [`LinkedValidationReport::coverage_unrecorded`], so the
/// documented admission gate (`is_ok() && coverage_unrecorded() == 0`) refuses
/// the closure just as it refuses an absent far record. Omission buys silence,
/// never agreement.
pub(crate) fn inherited_needs(certificate: &ProofCertificate) -> CoverageBound {
    certificate
        .assurance
        .map_or(CoverageBound::Unrecorded, |assurance| assurance.bound)
}

impl Site<'_> {
    fn import(&self) -> ImportId {
        match self {
            Site::BackedBy { reference, .. } | Site::Inherited { reference, .. } => {
                reference.module
            }
        }
    }
}

/// Every row of `module` that makes a cross-crate PROOF claim: a `backed_by`
/// naming an obligation on a `proved` summary, and every `external: Some`
/// inheritance certificate. A `backed_by` with no obligation, or on an
/// unproved summary, names an entity and claims nothing.
fn proof_bearing_sites(module: &Module) -> Vec<Site<'_>> {
    let mut sites = Vec::new();
    for function in &module.functions {
        if let Some(summary) = &function.summary
            && summary.proved
            && let Some(reference) = &summary.backed_by
            && reference.obligation.is_some()
        {
            sites.push(Site::BackedBy {
                local: function.id,
                summary,
                reference,
            });
        }
    }
    for certificate in &module.proof_certificates {
        if let ProofEvidence::InheritedFromCallee {
            callee,
            obligation,
            external: Some(reference),
        } = &certificate.evidence
        {
            sites.push(Site::Inherited {
                certificate,
                callee: *callee,
                restatement: *obligation,
                reference,
            });
        }
    }
    sites
}

/// The imports a module's proof-bearing rows cite — the set
/// [`crate::ModuleValidationReport::proof_bearing_imports`] reports.
pub(crate) fn proof_bearing_imports(module: &Module) -> BTreeSet<ImportId> {
    proof_bearing_sites(module)
        .iter()
        .map(Site::import)
        .collect()
}

/// One import-backed handle declaration of a module (L11, WS3.3): a
/// body-less declaration that is NOT a pinned handle entry point, whose
/// signature reaches a `Ty::Handle`, and whose summary carries a `backed_by`.
///
/// The binding spelling is the v41 one, ratified by DG-26 (no wire): the
/// declaration's `backed_by` is `ExternRef { module, symbol: <its own link
/// symbol>, obligation: None }`. A `backed_by` that ALSO names an obligation is
/// still a handle site — resolved here as the entity it names, while its
/// proof claim is re-earned separately at its own proof-bearing site.
struct HandleSite<'m> {
    local: FuncId,
    reference: &'m ExternRef,
}

/// Every import-backed handle declaration of `module` (see [`HandleSite`]).
/// A pinned entry point is never one — the pinned-symbol rules own it, under
/// the walk's ONE registry. A handle-reaching declaration with NO `backed_by`
/// is not a site either: rule 6 refuses it in every lane.
fn handle_declaration_sites<'m>(
    module: &'m Module,
    registry: &crate::validate::HandleRegistry,
) -> Vec<HandleSite<'m>> {
    let candidates: Vec<(FuncId, trust_ir::value::FuncTyId, &'m ExternRef)> = module
        .functions
        .iter()
        .filter(|function| {
            function.is_declaration() && registry.entry_for_symbol(&function.name).is_none()
        })
        .filter_map(|function| {
            let reference = function.summary.as_ref()?.backed_by.as_ref()?;
            Some((function.id, function.ty, reference))
        })
        .collect();
    if candidates.is_empty() {
        return Vec::new();
    }
    let reachability = module.nominal_type_reachability();
    candidates
        .into_iter()
        .filter(|(_, ty, _)| {
            module.func_type(*ty).is_some_and(|signature| {
                signature
                    .params
                    .iter()
                    .chain(&signature.returns)
                    .any(|slot| reachability.contains_handle(slot))
            })
        })
        .map(|(local, _, reference)| HandleSite { local, reference })
        .collect()
}

/// L11 for one handle declaration: resolve its `backed_by` across the
/// authenticated row with [`Module::resolve_handle_declaration`] — R1–R6 with
/// R4 HARDENED: the far function must be a definition that is not an
/// `AvailableExternally` copy, or a declaration the dependency's OWN linked
/// verdict authenticated as a handle declaration (so a chain of re-declarations
/// bottoms out in a definition, never in an entity-only `backed_by` nothing
/// re-earned).
///
/// Then the SHADOW rule: the body the binding bottoms out in must be the only
/// one a direct import exports under the symbol. A declaration is not an
/// exporter, so a chain through a re-declaration is invisible to the call-edge
/// ambiguity rule; without this check a direct import defining the same
/// symbol (at any signature) would sit beside the checked body at link time.
/// Two direct exporters are already `AmbiguousImportedSymbol`, so only the
/// single-exporter case is decided here.
///
/// Returns the outcome and, when authenticated, the current-scheme digest of
/// the module defining the body. An unauthenticated row records
/// [`SiteOutcome::Reported`]: the row-level error already names the cause.
fn check_handle_declaration(
    module: &Module,
    site: &HandleSite<'_>,
    verified: &VerifiedRows<'_>,
    exports: &ExportIndex<'_>,
) -> (SiteOutcome, Option<ProofDigest>) {
    let Some((verified_import, dependency)) = verified.get(&site.reference.module) else {
        return (SiteOutcome::Reported, None);
    };
    let refused = |why: String| {
        SiteOutcome::Refused(format!(
            "its `backed_by` into import #{} did not authenticate as an import-backed handle \
             declaration: {why}",
            site.reference.module.index()
        ))
    };
    let vouched: BTreeSet<FuncId> = dependency
        .authenticated
        .authenticated_handle_declarations()
        .collect();
    let far = match module.resolve_handle_declaration(
        site.reference,
        site.local,
        verified_import,
        &vouched,
    ) {
        Ok(resolved) => resolved.far,
        Err(error) => return (refused(error.to_string()), None),
    };
    let body = if far.is_declaration() {
        match dependency.authenticated.handle_declaration_body(far.id) {
            Some(body) => body,
            // Vouched but with no recorded body: never admit on a gap.
            None => {
                return (
                    refused(format!(
                        "the dependency's re-declaration of {:?} records no body it bottoms out in",
                        far.name
                    )),
                    None,
                );
            }
        }
    } else {
        verified_import
            .module()
            .stable_digest_under(IdentityScheme::CURRENT)
    };
    let exporters = exports.exporters(&far.name);
    if exporters.len() == 1 {
        for digest in exporters.keys() {
            let Some(row) = exports.first_row(digest) else {
                continue;
            };
            let Some((exporter, _)) = verified.get(&row) else {
                continue;
            };
            if exporter
                .module()
                .stable_digest_under(IdentityScheme::CURRENT)
                != body
            {
                return (
                    refused(format!(
                        "{:?} is also exported by import #{}, which is not the module defining \
                         the body this binding bottoms out in; the linker would see a second \
                         definition nothing checked against this declaration",
                        far.name,
                        row.index()
                    )),
                    None,
                );
            }
        }
    }
    (SiteOutcome::Authenticated, Some(body))
}

fn validate_one<'a>(
    module: &'a Module,
    ctx: &mut LinkContext<'a, '_>,
    depth: usize,
) -> Rc<ModuleVerdict> {
    let mut errors = Vec::new();
    let mut authenticated = AuthenticatedImports::default();
    let sites = proof_bearing_sites(module);
    let handle_sites = handle_declaration_sites(module, ctx.config.handle_registry());

    // L1–L4 once per import row — EVERY row of the table (WS1.7 / WS4.8,
    // DG-78: unconditional), plus any id a site cites that is not in the
    // table, so a dangling citation still names itself as `UnresolvedImport`.
    // A row nothing cites is authenticated exactly like a cited one: the
    // digest it records must name a module the resolver holds, and that
    // module must validate.
    let rows = u32::try_from(module.imports.len()).unwrap_or(u32::MAX);
    let mut to_authenticate: BTreeSet<ImportId> = (0..rows).map(ImportId::new).collect();
    to_authenticate.extend(sites.iter().map(Site::import));
    to_authenticate.extend(handle_sites.iter().map(|site| site.reference.module));
    let mut verified: VerifiedRows<'a> = BTreeMap::new();
    for id in to_authenticate {
        // WS5.3b: the FIRST proof-bearing site kind citing this row, if any;
        // a call-only row has none.
        let proof_site = sites
            .iter()
            .find(|site| site.import() == id)
            .map(|site| match site {
                Site::BackedBy { .. } => "backed_by",
                Site::Inherited { .. } => "inherited",
            });
        match authenticate_import(module, id, proof_site, ctx, depth) {
            Ok((verified_import, dependency)) => {
                authenticated.digests.insert(id, verified_import.digest());
                verified.insert(id, (verified_import, dependency));
            }
            Err(error) => errors.push(*error),
        }
    }

    // L5–L7 per reference.
    for site in &sites {
        let Some((verified_import, dependency)) = verified.get(&site.import()) else {
            // The import-level error above already names the cause.
            match site {
                Site::BackedBy { local, .. } => {
                    authenticated.record_backed_by(*local, SiteOutcome::Reported);
                }
                Site::Inherited { certificate, .. } => {
                    authenticated.record_inherited(certificate, SiteOutcome::Reported);
                }
            }
            continue;
        };
        match site {
            Site::BackedBy {
                local,
                summary,
                reference,
            } => {
                let outcome = match check_backed_by(
                    module,
                    *local,
                    summary,
                    reference,
                    verified_import,
                    dependency,
                ) {
                    Ok(far_obligation) => check_coverage(
                        verified_import,
                        far_obligation,
                        BACKED_BY_NEEDS,
                        "backed_by",
                        "an unqualified `proved` summary claims the contract for ALL inputs",
                        &mut ctx.coverage,
                        &mut errors,
                    ),
                    Err(detail) => SiteOutcome::Refused(detail),
                };
                authenticated.record_backed_by(*local, outcome);
            }
            Site::Inherited {
                certificate,
                callee,
                restatement,
                reference,
            } => {
                // L7(a): the certificate must discharge the obligation its
                // evidence restates. Every restatement check below runs on
                // `evidence.obligation`, and admission discharges
                // `cert.obligation`; letting them differ would let a
                // certificate re-check one claim and discharge another.
                if certificate.obligation != *restatement {
                    errors.push(ValidationError::ExternInheritanceRestatementMismatch {
                        certificate_obligation: certificate.obligation.index(),
                        evidence_obligation: restatement.index(),
                    });
                    authenticated.record_inherited(certificate, SiteOutcome::Reported);
                    continue;
                }
                let outcome = match check_inherited(
                    module,
                    *callee,
                    *restatement,
                    reference,
                    verified_import,
                    dependency,
                ) {
                    Ok(far_obligation) => check_coverage(
                        verified_import,
                        far_obligation,
                        inherited_needs(certificate),
                        "inherited",
                        "the inheritance certificate's own recorded assurance",
                        &mut ctx.coverage,
                        &mut errors,
                    ),
                    Err(detail) => SiteOutcome::Refused(detail),
                };
                authenticated.record_inherited(certificate, outcome);
            }
        }
    }

    // L11: every import-backed handle declaration, with the hardened R4 and
    // the shadow rule.
    let exports = ExportIndex::new(&verified);
    for site in &handle_sites {
        let (outcome, body) = check_handle_declaration(module, site, &verified, &exports);
        if outcome == SiteOutcome::Authenticated {
            ctx.call_edges.authenticated += 1;
        }
        if let Some(body) = body {
            authenticated
                .handle_declaration_bodies
                .insert(site.local.index(), body);
        }
        authenticated
            .handle_declarations
            .insert(site.local.index(), outcome);
    }

    // L10: every call edge into an authenticated dependency.
    check_call_edges(module, &sites, &handle_sites, &verified, ctx, &mut errors);

    // L12: nominal type identity agrees across the whole closure. Runs AFTER
    // the imports above were authenticated and validated, so every dependency
    // reachable from this module has already registered its keys and a
    // conflict names the pair in walk order (dependency first, importer
    // second; root last of all).
    register_type_origins(module, ctx);

    // L8: the module validator, with the authenticated inheritances admitted
    // into the `Discharged` tier and every site's outcome consulted.
    let linked_authority = LinkedAuthority {
        inner: ctx.config.authority(),
        admitted: &authenticated.admitted,
    };
    // Registry and dialect schemas come from the walk's ONE config, for the
    // root and every dependency alike.
    let (module_errors, replayed) = validate_module_filtered(
        module,
        None,
        &linked_authority,
        ctx.config.dialect_schemas(),
        ImportPolicy::Authenticated(&authenticated),
        ctx.config.handle_registry(),
    );
    errors.extend(module_errors);
    // The codegen license layer (when the config asks for it) reads the
    // kernel tier THIS pass replayed, so no module is kernel-rechecked twice.
    extend_with_config_codegen_errors(&mut errors, module, &replayed, ctx.config);
    crate::validate::extend_with_config_binding_errors(&mut errors, module, ctx.config);

    // What an importer may inherit from this module: kernel-tier replayed
    // obligations, plus the restatements its own authenticated inheritances
    // discharge. A capability-replayed `Discharged` row and a `Trusted` row
    // are deliberately absent.
    let mut ground: BTreeSet<ProofId> = module
        .proof_certificates
        .iter()
        .filter(|certificate| replayed.contains(&certificate.lineage_ref()))
        .map(|certificate| certificate.obligation)
        .collect();
    ground.extend(
        module
            .proof_certificates
            .iter()
            .filter(|certificate| authenticated.admitted.contains(&certificate.lineage_ref()))
            .map(|certificate| certificate.obligation),
    );

    Rc::new(ModuleVerdict {
        errors,
        ground,
        replayed,
        authenticated,
    })
}

/// L9's site step: run [`coverage_verdict`] and turn it into a site outcome,
/// pushing the NAMED refusal itself rather than folding it into the
/// import-level `UnauthenticatedImport` detail string — the insufficiency is
/// about a specific far obligation and a specific pair of bounds, and a caller
/// should be able to match on it.
///
/// A refused site records [`SiteOutcome::Reported`]: the error is already
/// named here, and the site must NOT be admitted, so an inheritance whose
/// coverage is insufficient cannot ground its own restatement.
fn check_coverage(
    verified_import: &trust_ir::VerifiedImport<'_>,
    far_obligation: ProofId,
    needs: CoverageBound,
    site: &'static str,
    why: &str,
    coverage: &mut CoverageTally,
    errors: &mut Vec<ValidationError>,
) -> SiteOutcome {
    // A local row that records NO GRADE is not a satisfied demand: there was
    // nothing to compare, so nothing was established. Counted as
    // NOT ESTABLISHED before the far supply is consulted, because
    // `coverage_supports(_, Unrecorded)` is true for every far bound —
    // correct as a partial order, and exactly the reading that would let the
    // tally render "the producer asked for nothing" as "the far bound
    // supplied it".
    if needs == CoverageBound::Unrecorded {
        coverage.unrecorded += 1;
        return SiteOutcome::Authenticated;
    }
    match coverage_verdict(verified_import.module(), far_obligation, needs) {
        CoverageVerdict::Supported => {
            coverage.supported += 1;
            SiteOutcome::Authenticated
        }
        CoverageVerdict::Unrecorded => {
            coverage.unrecorded += 1;
            SiteOutcome::Authenticated
        }
        CoverageVerdict::Insufficient { recorded } => {
            coverage.refused += 1;
            errors.push(ValidationError::ImportCoverageBelowClaim {
                import: verified_import.id().index(),
                site,
                obligation: far_obligation.index(),
                needs: format!("{needs:?} ({why})"),
                far: recorded.iter().map(|bound| format!("{bound:?}")).collect(),
            });
            SiteOutcome::Reported
        }
    }
}

/// The authenticated import rows of one module, with the dependency verdicts.
type VerifiedRows<'a> = BTreeMap<ImportId, (trust_ir::VerifiedImport<'a>, Rc<ModuleVerdict>)>;

/// L12: every nominal [`TypeOrigin`] key `module` stamps must agree, in
/// structure, with the definition the walk FIRST saw it on — in any module of
/// the closure.
///
/// Closure-wide rather than per import edge, for the same reason L9 and L10
/// tally closure-wide: a program links every module of its closure, so a
/// dependency this module never imports directly still contributes its type
/// images to the program, and one source entity with two shapes anywhere in
/// it makes neither shape usable. A check confined to an importer and its
/// direct rows would miss two siblings, and two modules that meet only
/// through a transitive edge.
///
/// The rule is REFUSE-ONLY, in both directions it could have gone wrong:
///
/// * a key one module carries alone is not a finding — no other module
///   claims that entity;
/// * two definitions with DIFFERENT keys are two types, never a conflict;
/// * an UNKEYED definition is not examined, and its absence is never read as
///   agreement with anything.
///
/// Nothing here admits a definition, relaxes a signature check, or merges two
/// types: the key can only split (in the comparator) or refuse (here). A key
/// stamped twice INSIDE one module is that module's own defect (the in-module
/// form of `TypeOriginConflict`, named by the module validator at L8), so a
/// module's second claim on a key it already holds is not re-reported here.
///
/// The memo guarantees each distinct module registers once, so a diamond's
/// shared leaf is compared against each later claimant exactly once.
fn register_type_origins<'a>(module: &'a Module, ctx: &mut LinkContext<'a, '_>) {
    for definition in module.keyed_type_definitions() {
        match ctx.type_origins.get(definition.origin) {
            None => {
                ctx.type_origins.insert(
                    definition.origin.clone(),
                    ClaimedTypeOrigin {
                        module,
                        table: definition.table,
                        name: definition.name.to_string(),
                        ty: definition.ty,
                    },
                );
            }
            // The module validator names an in-module duplicate.
            Some(first) if core::ptr::eq(first.module, module) => {}
            Some(first) => {
                // A struct keyed as an enum's entity is already a
                // contradiction: the tables differ, so nothing structural
                // can reconcile them.
                let agrees = first.table == definition.table
                    && ty_structurally_eq_across(first.module, &first.ty, module, &definition.ty);
                if !agrees {
                    ctx.type_origin_conflicts
                        .push(ValidationError::TypeOriginConflict {
                            origin: definition.origin.to_string(),
                            first_module: Some(first.module.name.clone()),
                            first_table: first.table,
                            first: first.name.clone(),
                            second_module: Some(module.name.clone()),
                            second_table: definition.table,
                            second: definition.name.to_string(),
                        });
                }
            }
        }
    }
}

/// L10: resolve every CALL EDGE of `module` across the import it binds to.
///
/// A call edge is a body-less declaration. It binds to an import either
/// EXPLICITLY — its summary carries a `backed_by` that is not a proof-bearing
/// site (`obligation: None`, or an unproved summary), which names the far
/// entity and claims nothing about it — or IMPLICITLY — no `backed_by`, and
/// exactly one authenticated dependency artifact DEFINES and exports the
/// declaration's link symbol, which is what the linker will bind it to.
/// Either way the edge is resolved with [`Module::resolve_extern_ref`] at
/// [`ExternRefSite::CallEdge`] and NO obligation (R1–R6: the verified row, the
/// local declaration and its symbol, the far symbol's uniqueness,
/// definition-or-backed-declaration, export linkage, far interposability,
/// producer, and [`trust_ir::signatures_compatible`]). A local `ExternalWeak`
/// import is admitted at a call edge — its nullable binding is the importer
/// validator's null-checked idiom, and there is no proof about the far body
/// for a different binding to falsify — but still signature-checked. An
/// explicit citation that also names an obligation is resolved as the ENTITY
/// it names: a claim-free summary makes no claim for R7 to check.
///
/// Refusals:
///
/// * two or more distinct dependency ARTIFACTS (keyed by digest, not by row:
///   the ratified two-producer shape is one artifact behind two rows) export
///   the symbol, as a function or as data →
///   [`ValidationError::AmbiguousImportedSymbol`], whatever else the
///   declaration carries — the linker reads no `backed_by`;
/// * the one exporting artifact exports the symbol as DATA (an initialized
///   global), so the linker would bind the call to a static →
///   [`ValidationError::UnauthenticatedImport`] with `site: "call"`;
/// * any R1–R6 failure → the same, on the row the edge was resolved through.
///
/// The third spelling of a call edge is a relocatable `Constant::SymbolAddr`
/// naming a symbol this module neither declares nor defines: called through
/// `CallIndirect`, its signature is compared with nothing, yet the linker
/// binds it to the dependency's body all the same. Such an address of a
/// FUNCTION an authenticated dependency exports is refused (`site: "call"`,
/// "no local declaration"): a call into a dependency must be spelled through
/// a declaration, which this rule signature-checks. The address of exported
/// DATA, or of a symbol no dependency exports, is untouched.
///
/// A declaration a proof-bearing site already resolved (its `backed_by` or
/// inheritance callee) is not resolved twice. A declaration whose explicit
/// row did not authenticate is skipped: the row-level error (or the module
/// validator's `DanglingExternRef`) already names it. A declaration with no
/// `backed_by` that no authenticated dependency exports is UNBOUND: counted,
/// not refused.
fn check_call_edges<'a>(
    module: &'a Module,
    sites: &[Site<'_>],
    handle_sites: &[HandleSite<'_>],
    verified: &VerifiedRows<'a>,
    ctx: &mut LinkContext<'a, '_>,
    errors: &mut Vec<ValidationError>,
) {
    // A handle declaration (L11) is resolved at the STRICTER
    // `ExternRefSite::HandleDeclaration`, which subsumes this rule's R1–R6.
    let covered: BTreeSet<FuncId> = sites
        .iter()
        .map(|site| match site {
            Site::BackedBy { local, .. } => *local,
            Site::Inherited { callee, .. } => *callee,
        })
        .chain(handle_sites.iter().map(|site| site.local))
        .collect();
    let exports = ExportIndex::new(verified);

    for function in module.functions.iter().filter(|f| f.is_declaration()) {
        let exporters = exports.exporters(&function.name);
        if exporters.len() > 1 {
            errors.push(exports.ambiguous(&function.name, &exporters));
            continue;
        }
        if covered.contains(&function.id) {
            continue;
        }
        let explicit = function
            .summary
            .as_ref()
            .and_then(|summary| summary.backed_by.as_ref());
        let reference = match explicit {
            // The row did not authenticate (already named at L1–L4), or does
            // not exist (the module validator's `DanglingExternRef`).
            Some(reference) if !verified.contains_key(&reference.module) => continue,
            Some(reference) => ExternRef::new(reference.module, reference.symbol.clone()),
            None => match exporters.iter().next() {
                None => {
                    ctx.call_edges.unbound.push(UnboundDeclaration {
                        module: module.name.clone(),
                        symbol: function.name.clone(),
                    });
                    continue;
                }
                Some((digest, Export::Data)) => {
                    if let Some(row) = exports.first_row(digest) {
                        errors.push(ValidationError::UnauthenticatedImport {
                            import: row.index(),
                            site: "call",
                            detail: format!(
                                "call edge @{} (declaration #{}): the dependency exports `{}` \
                                 as DATA (an initialized global), not as a function, so the \
                                 linker would bind this call to a static",
                                function.name,
                                function.id.index(),
                                function.name
                            ),
                        });
                    }
                    continue;
                }
                Some((digest, Export::Function(far_producer))) => {
                    match exports.producer_row(digest, *far_producer, verified) {
                        Some(row) => ExternRef::new(row, function.name.clone()),
                        None => continue,
                    }
                }
            },
        };
        let Some((verified_import, _)) = verified.get(&reference.module) else {
            continue;
        };
        match module.resolve_extern_ref(
            &reference,
            function.id,
            ExternRefSite::CallEdge,
            verified_import,
        ) {
            Ok(_) => ctx.call_edges.authenticated += 1,
            Err(error) => errors.push(ValidationError::UnauthenticatedImport {
                import: reference.module.index(),
                site: "call",
                detail: format!(
                    "call edge @{} (declaration #{}): {error}",
                    function.name,
                    function.id.index()
                ),
            }),
        }
    }

    // The declaration-free spelling: a relocatable address of a symbol this
    // module neither declares nor defines.
    for symbol in undeclared_symbol_addresses(module) {
        let exporters = exports.exporters(symbol);
        if exporters.len() > 1 {
            errors.push(exports.ambiguous(symbol, &exporters));
            continue;
        }
        let Some((digest, Export::Function(far_producer))) = exporters.iter().next() else {
            continue;
        };
        if let Some(row) = exports.producer_row(digest, *far_producer, verified) {
            errors.push(ValidationError::UnauthenticatedImport {
                import: row.index(),
                site: "call",
                detail: format!(
                    "`SymbolAddr` names @{symbol}, a function the dependency exports, but this \
                     module has no local declaration of it, so the signature it is called at \
                     is compared with nothing; declare it so the call edge is checked"
                ),
            });
        }
    }
}

/// Every `Constant::SymbolAddr` symbol in `module` — function-body `Const`s
/// and global initializers, nested constants included — that names neither a
/// function nor a global of `module` itself.
fn undeclared_symbol_addresses(module: &Module) -> BTreeSet<&str> {
    let local: BTreeSet<&str> = module
        .functions
        .iter()
        .map(|function| function.name.as_str())
        .chain(module.globals.iter().map(|global| global.name.as_str()))
        .collect();
    let mut roots: Vec<&Constant> = module
        .globals
        .iter()
        .filter_map(|global| global.initializer.as_ref())
        .collect();
    for function in &module.functions {
        for block in &function.blocks {
            for node in &block.body {
                if let Inst::Const { value, .. } = &node.inst {
                    roots.push(value);
                }
            }
        }
    }
    let mut symbols = BTreeSet::new();
    while let Some(constant) = roots.pop() {
        if let Constant::SymbolAddr { symbol, .. } = constant
            && !local.contains(symbol.as_str())
        {
            symbols.insert(symbol.as_str());
        }
        roots.extend(constant.children());
    }
    symbols
}

/// How one dependency artifact exports a link symbol.
#[derive(Debug, Clone, Copy)]
enum Export<'a> {
    /// A function DEFINITION, with its recorded producer.
    Function(Option<&'a Producer>),
    /// An initialized global: the symbol names a static, not code.
    Data,
}

/// What the authenticated dependencies of one module EXPORT, built once per
/// module so L10 costs one pass over each dependency artifact rather than
/// one per declaration.
///
/// Only a DEFINITION exports (a function with a body, or a global with an
/// initializer; linkage neither `Internal` nor `Private`): a dependency's own
/// declaration of a symbol is that dependency using it, not providing it, so
/// it neither binds an edge nor makes one ambiguous. Interposable definitions
/// DO count — the edge then fails `InterposableFarSite` by name rather than
/// reading as an FFI extern. Artifacts are keyed by digest, so two rows naming
/// one artifact (the ratified two-producer shape) are one exporter.
struct ExportIndex<'a> {
    /// Per link symbol: the exporting artifacts and how each exports it.
    by_symbol: BTreeMap<&'a str, BTreeMap<ProofDigest, Export<'a>>>,
    /// Per artifact: the verified rows naming it, ascending.
    rows: BTreeMap<ProofDigest, Vec<ImportId>>,
}

impl<'a> ExportIndex<'a> {
    fn new(verified: &VerifiedRows<'a>) -> Self {
        let mut index = ExportIndex {
            by_symbol: BTreeMap::new(),
            rows: BTreeMap::new(),
        };
        let exported = |linkage: Linkage| !linkage.is_module_local();
        for (id, (verified_import, _)) in verified {
            let digest = verified_import.digest();
            let rows = index.rows.entry(digest).or_default();
            rows.push(*id);
            if rows.len() > 1 {
                // This artifact's exports were indexed through an earlier row.
                continue;
            }
            let far_module = verified_import.module();
            for far in &far_module.functions {
                if !far.is_declaration() && exported(far.linkage) {
                    index
                        .by_symbol
                        .entry(far.name.as_str())
                        .or_default()
                        .entry(digest)
                        .or_insert(Export::Function(far.producer.as_ref()));
                }
            }
            for global in &far_module.globals {
                if global.initializer.is_some() && exported(global.linkage) {
                    index
                        .by_symbol
                        .entry(global.name.as_str())
                        .or_default()
                        .entry(digest)
                        .or_insert(Export::Data);
                }
            }
        }
        index
    }

    fn exporters(&self, symbol: &str) -> BTreeMap<ProofDigest, Export<'a>> {
        self.by_symbol.get(symbol).cloned().unwrap_or_default()
    }

    fn first_row(&self, digest: &ProofDigest) -> Option<ImportId> {
        self.rows.get(digest).and_then(|rows| rows.first().copied())
    }

    /// `AmbiguousImportedSymbol` for `symbol`, naming one row per exporting
    /// artifact (its lowest), ascending.
    fn ambiguous(
        &self,
        symbol: &str,
        exporters: &BTreeMap<ProofDigest, Export<'a>>,
    ) -> ValidationError {
        let mut imports: Vec<u32> = exporters
            .keys()
            .filter_map(|digest| self.first_row(digest))
            .map(ImportId::index)
            .collect();
        imports.sort_unstable();
        ValidationError::AmbiguousImportedSymbol {
            symbol: symbol.to_string(),
            imports,
        }
    }

    /// Of the rows naming the artifact `digest`, the one whose recorded
    /// producer is the far definition's — the ratified one-row-per-
    /// `(artifact, producer)` shape (`docs/SPEC_RATIFICATIONS.md` §6). With no
    /// such row, the lowest one, so R5 NAMES the mismatch instead of the edge
    /// going unchecked.
    fn producer_row(
        &self,
        digest: &ProofDigest,
        far_producer: Option<&Producer>,
        verified: &VerifiedRows<'_>,
    ) -> Option<ImportId> {
        let rows = self.rows.get(digest)?;
        rows.iter()
            .copied()
            .find(|row| {
                far_producer.is_some()
                    && verified.get(row).is_some_and(|(verified_import, _)| {
                        verified_import.import().producer.as_ref() == far_producer
                    })
            })
            .or_else(|| rows.first().copied())
    }
}

/// L1–L4 for one import row: resolve, guard the walk, authenticate the
/// edge, validate the dependency. The dependency's verdict is memoized by its
/// digest, so a diamond's shared leaf is resolved and validated once.
fn authenticate_import<'a>(
    module: &'a Module,
    id: ImportId,
    proof_site: Option<&'static str>,
    ctx: &mut LinkContext<'a, '_>,
    depth: usize,
) -> Result<(trust_ir::VerifiedImport<'a>, Rc<ModuleVerdict>), Box<ValidationError>> {
    let import_index = id.index();
    let unauthenticated = |detail: String| {
        Box::new(ValidationError::UnauthenticatedImport {
            import: import_index,
            site: "import",
            detail,
        })
    };
    let Some(import) = module.import(id) else {
        return Err(unauthenticated(
            trust_ir::ImportVerificationError::UnresolvedImport {
                import: import_index,
            }
            .to_string(),
        ));
    };

    // Memo hit: the module recorded under this digest was already resolved
    // and validated. The edge checks (C2–C6) are per-import and still run,
    // against the `HashedModule` the walk built at L2 below — its digest was
    // computed over that module, never taken from the import's own record.
    if let Some((hashed, verdict)) = ctx
        .memo
        .get(&(import.scheme, import.digest))
        .map(|(hashed, verdict)| (hashed.clone(), Rc::clone(verdict)))
    {
        let verified_import = module
            .verify_import_hashed(id, &hashed)
            .map_err(|error| unauthenticated(error.to_string()))?;
        return finish_import(id, verified_import, verdict);
    }

    // L1
    let Some(candidate) = ctx.resolver.resolve(import) else {
        return Err(Box::new(ValidationError::ImportUnavailable {
            import: import_index,
            name: import.name.clone(),
        }));
    };
    // WS5.3b (`ImportIncomplete`): a candidate that CLAIMS to be partial
    // cannot back a proof. Probed BEFORE the wire-identity guard so the
    // refusal names the claim rather than the (as yet) missing binary
    // carrier; a call-only row falls through to the ordinary authentication.
    if let (Some(site), Some(trust_ir::ModuleCompleteness::Partial(rows))) =
        (proof_site, &candidate.completeness)
    {
        return Err(Box::new(ValidationError::ImportIncomplete {
            import: import_index,
            site,
            unlowered: rows.iter().map(|row| row.symbol.clone()).collect(),
        }));
    }
    // L2 — computed once per module; the cycle check runs BEFORE the digest
    // comparison so a resolver returning the importer itself is reported as
    // the cycle it is, not as a mismatch. A candidate with no wire identity
    // (an unencodable construct, `wire_identity_blocker`) has no digest to
    // compare, so it cannot authenticate ANY row: refused by name here rather
    // than panicking inside `HashedModule::new`.
    if let Some(blocker) = crate::validate::wire_identity_blocker(candidate) {
        return Err(unauthenticated(format!(
            "the resolved candidate `{}` has no wire identity to authenticate against the \
             recorded digest: {blocker}",
            candidate.name
        )));
    }
    let hashed = HashedModule::new(candidate);
    // The walk's identity of a module is its CURRENT-scheme digest (see
    // `LinkContext::stack`); the row's own scheme is compared at L3.
    let actual = hashed.digest();
    if let Some(position) = ctx.stack.iter().position(|(digest, _)| *digest == actual) {
        let mut path: Vec<String> = ctx.stack[position..]
            .iter()
            .map(|(_, name)| name.clone())
            .collect();
        path.push(candidate.name.clone());
        return Err(Box::new(ValidationError::ImportCycle {
            import: import_index,
            path,
        }));
    }
    if depth + 1 > MAX_IMPORT_DEPTH {
        return Err(Box::new(ValidationError::ImportClosureTooDeep {
            import: import_index,
            depth: depth + 1,
        }));
    }
    // L3
    let verified_import = module
        .verify_import_hashed(id, &hashed)
        .map_err(|error| unauthenticated(error.to_string()))?;
    // The same module reached earlier through a row of ANOTHER scheme (a
    // diamond whose edges record the shared leaf as V2 and as V3): the
    // verdict is keyed by the walk's identity, so it is reused — the leaf is
    // validated once and its L9/L10 sites are counted once — while this edge
    // was authenticated above against THIS candidate under ITS row's scheme.
    if let Some(verdict) = ctx
        .memo
        .get(&(IdentityScheme::CURRENT, actual))
        .map(|(_, verdict)| Rc::clone(verdict))
    {
        ctx.memo.insert(
            (import.scheme, hashed.digest_under(import.scheme)),
            (hashed.clone(), Rc::clone(&verdict)),
        );
        return finish_import(id, verified_import, verdict);
    }
    // L4
    ctx.stack.push((actual, candidate.name.clone()));
    let verdict = validate_one(candidate, ctx, depth + 1);
    ctx.stack.pop();
    for scheme in [IdentityScheme::CURRENT, import.scheme] {
        ctx.memo.insert(
            (scheme, hashed.digest_under(scheme)),
            (hashed.clone(), Rc::clone(&verdict)),
        );
    }
    finish_import(id, verified_import, verdict)
}

fn finish_import<'a>(
    id: ImportId,
    verified_import: trust_ir::VerifiedImport<'a>,
    verdict: Rc<ModuleVerdict>,
) -> Result<(trust_ir::VerifiedImport<'a>, Rc<ModuleVerdict>), Box<ValidationError>> {
    if let Some(first) = verdict.errors.first() {
        return Err(Box::new(ValidationError::ImportedModuleInvalid {
            import: id.index(),
            errors: verdict.errors.len(),
            first: first.to_string(),
        }));
    }
    Ok((verified_import, verdict))
}

/// L5 + L6 for a `backed_by` site. Returns the far obligation L9 compares
/// the recorded coverage of: the cited one, unless (far definition) some
/// restated clause's best-covered grounded row is WEAKER — then that row, so
/// the site is judged on its least-covered clause.
///
/// Beyond the exact restatement of the far summary, the CITED obligation is
/// held to the same two tests an inheritance's far obligation is (WS1.3,
/// [`check_inherited`] is the model):
///
/// * it must be GROUNDED in the dependency — kernel-tier replayed, or
///   discharged by an authenticated inheritance of its own. A
///   capability-replayed `Discharged` row and a `Trusted` row never are, so a
///   status label cannot back a cross-crate `proved`;
/// * its `formula` must be one of the restated clauses of the role its kind
///   backs (Precondition↔requires, Postcondition↔ensures,
///   Termination↔decreases). A citation of a row about some OTHER claim is
///   refused, even when the far summary is `proved`.
///
/// * for a far DEFINITION, EVERY restated clause — not only the cited one —
///   must be stated by a grounded far row of its role's kind scoped to the far
///   function. The importer's `proved` claims all of them, so citing one
///   grounded row must not carry a sibling clause the dependency backs only at
///   the capability tier. A far DECLARATION backs its clauses only through its
///   own `backed_by`, which the dependency's pass re-earned under this rule.
///
/// * for a far DEFINITION, every restated clause's COVERAGE takes part in L9:
///   the returned obligation is the weakest-covered of the cited row and each
///   clause's best-covered grounded row, so a sibling clause discharged only
///   to a recorded bound cannot ride on the cited row's `Unbounded` record.
///
/// The far `proved` bit itself is per-clause because the dependency ran the
/// same rule in its own `validate_one`; together these mean the importer's
/// `proved` rests on a grounded proof of every clause it restates.
///
/// A RECORDED local effect summary (v59, WS1.14) is part of that restatement:
/// it must equal the far summary's `effects` exactly and name no module
/// global. An authenticated site is what makes the declaration's effects
/// admissible at a local call (`validate::effects`); an unrecorded one is
/// always sound (callers havoc).
fn check_backed_by<'a>(
    module: &'a Module,
    local: FuncId,
    summary: &FunctionSummary,
    reference: &ExternRef,
    verified_import: &trust_ir::VerifiedImport<'a>,
    dependency: &ModuleVerdict,
) -> Result<ProofId, String> {
    let resolved = module
        .resolve_extern_ref(
            reference,
            local,
            ExternRefSite::SummaryBackedBy,
            verified_import,
        )
        .map_err(|error| error.to_string())?;
    let far = resolved.far;
    let Some(far_summary) = &far.summary else {
        return Err(format!(
            "far function {:?} carries no summary; there is no contract to have proved",
            far.name
        ));
    };
    if !far_summary.proved {
        return Err(format!(
            "far function {:?}'s summary is not `proved`; a caller may not assume a contract \
             its owner has not established",
            far.name
        ));
    }
    // Exact restatement, bindings included: a clause the local summary adds
    // or drops changes what a caller may assume, and the far module proved
    // only its own clauses.
    if summary.requires != far_summary.requires {
        return Err("local `requires` differ from the far summary's".to_string());
    }
    if summary.ensures != far_summary.ensures {
        return Err("local `ensures` differ from the far summary's".to_string());
    }
    if summary.decreases != far_summary.decreases {
        return Err("local `decreases` differ from the far summary's".to_string());
    }
    if summary.params != far_summary.params {
        return Err("local `params` differ from the far summary's".to_string());
    }
    // v59 (WS1.14): a recorded effect summary is part of the contract a
    // caller relies on, so it is restated EXACTLY — the far definition's
    // effects were checked against its body by the dependency's own pass (a
    // far declaration's, one edge further on by this rule). Recording none is
    // always sound: callers then havoc. A module global has no identity
    // across an import edge at this version, so a restatement may not name
    // one (the importer leaves `effects` unrecorded instead).
    if let Some(effects) = &summary.effects {
        if far_summary.effects.as_ref() != Some(effects) {
            return Err(
                "local `effects` differ from the far summary's (a recorded effect summary is \
                 restated exactly; leave it unrecorded to havoc instead)"
                    .to_string(),
            );
        }
        if effects.names_a_global() {
            return Err(
                "local `effects` name a module global, which has no identity across an import \
                 edge at this version; leave `effects` unrecorded (callers havoc) instead"
                    .to_string(),
            );
        }
    }
    // `proof_bearing_sites` only admits a site whose reference names an
    // obligation, and `resolve_extern_ref` resolves one whenever the
    // reference names one, so this is `Some` by construction. Named rather
    // than unwrapped: `None` is never a wildcard here either.
    let cited: &ProofObligation = resolved.obligation.ok_or_else(|| {
        "reference names no obligation, so there is no proof claim to back".to_string()
    })?;
    // (i) grounded, not merely labelled.
    if !dependency.ground.contains(&cited.id) {
        return Err(format!(
            "far obligation #{} backs `proved` but is not grounded in the dependency \
             (kernel-tier replay or authenticated inheritance)",
            cited.id.index()
        ));
    }
    // (ii) about a clause the importer restates. `resolve_extern_ref` admits
    // only the three contract kinds at this site; an unmapped kind is refused
    // by name rather than assumed to fit.
    let Some(role) = ContractClauseRole::backed_by_kind(&cited.kind) else {
        return Err(format!(
            "cited far obligation #{} has kind {}, which backs no contract clause",
            cited.id.index(),
            cited.kind
        ));
    };
    let Some(formula) = &cited.formula else {
        return Err(format!(
            "cited far obligation #{} carries no formula, so it states none of the restated {} \
             clauses",
            cited.id.index(),
            role.name()
        ));
    };
    if !role.clauses(summary).contains(formula) {
        return Err(format!(
            "cited far obligation #{} states `{}`, which is none of the restated {} clauses",
            cited.id.index(),
            crate::contracts::clause_text(formula),
            role.name()
        ));
    }
    // (iii) every restated clause, not only the cited one, is grounded. The
    // importer's `proved` claims ALL of them, so citing one grounded row must
    // not carry a sibling clause that the dependency backs only with a
    // capability-replayed `Discharged` row: across an edge only the
    // dependency's ground counts (WS1.3 DECIDE). For a far DEFINITION the
    // clause's backing rows are the dependency's own rows scoped to it. A far
    // DECLARATION backs its clauses only through its own `backed_by`, which the
    // dependency's pass re-earned under this same rule one edge further on.
    //
    // (iv) and every restated clause is COVERED, not only the cited one (WS1.3
    // review). L9 compares the far coverage of the ONE obligation this
    // function returns; returning the cited row alone let a sibling clause
    // whose only grounded rows record a BOUNDED discharge ride on the cited
    // row's `Unbounded` record into an unqualified `proved` — with
    // `coverage_unrecorded() == 0`, so even the documented admission gate
    // passed. So each clause contributes its best-covered grounded row, and
    // the site is judged on the WEAKEST of those and the cited row: never
    // weaker than judging the cited row alone.
    let dependency_module = verified_import.module();
    let rank = |obligation: ProofId| match coverage_verdict(
        dependency_module,
        obligation,
        BACKED_BY_NEEDS,
    ) {
        CoverageVerdict::Insufficient { .. } => 0u8,
        CoverageVerdict::Unrecorded => 1,
        CoverageVerdict::Supported => 2,
    };
    let mut weakest = (rank(cited.id), cited.id);
    if !far.is_declaration() {
        for role in ContractClauseRole::ALL {
            for (index, clause) in role.clauses(far_summary).iter().enumerate() {
                let best = dependency_module
                    .proof_obligations
                    .iter()
                    .filter(|row| {
                        row.function == Some(far.id)
                            && ContractClauseRole::backed_by_kind(&row.kind) == Some(role)
                            && row.status.is_discharged_tier()
                            && row.formula.as_ref() == Some(clause)
                            && dependency.ground.contains(&row.id)
                    })
                    .map(|row| (rank(row.id), row.id))
                    .max_by_key(|(rank, _)| *rank);
                let Some(best) = best else {
                    return Err(format!(
                        "far {} clause {index} `{}` is stated by no {} row grounded in the \
                         dependency (kernel-tier replay or authenticated inheritance); a \
                         capability-replayed row cannot back a cross-crate `proved`",
                        role.name(),
                        crate::contracts::clause_text(clause),
                        role.backing_kind_name()
                    ));
                };
                if best.0 < weakest.0 {
                    weakest = best;
                }
            }
        }
    }
    Ok(weakest.1)
}

/// L5 + L7(b)(c) for an inheritance site whose L7(a) already held. Returns
/// the far obligation, so L9 can compare its recorded coverage.
fn check_inherited<'a>(
    module: &'a Module,
    callee: FuncId,
    restatement: ProofId,
    reference: &ExternRef,
    verified_import: &trust_ir::VerifiedImport<'a>,
    dependency: &ModuleVerdict,
) -> Result<ProofId, String> {
    let resolved = module
        .resolve_extern_ref(
            reference,
            callee,
            ExternRefSite::InheritedFromCallee,
            verified_import,
        )
        .map_err(|error| error.to_string())?;
    let far_obligation: &ProofObligation = resolved.obligation.ok_or_else(|| {
        "reference names no obligation, so there is no proof claim to inherit".to_string()
    })?;
    // (b) the far obligation must be GROUNDED in the dependency, not merely
    // labelled: kernel-tier replay or an authenticated inheritance of its own.
    if !dependency.ground.contains(&far_obligation.id) {
        return Err(format!(
            "far obligation #{} is {} in the dependency but not grounded there (no kernel-tier \
             replay and no authenticated inheritance); a status label is not proof authority",
            far_obligation.id.index(),
            far_obligation.status
        ));
    }
    // (c) the local restatement.
    let mut matches = module
        .proof_obligations
        .iter()
        .filter(|obligation| obligation.id == restatement);
    let local_obligation = match (matches.next(), matches.next()) {
        (Some(obligation), None) => obligation,
        _ => {
            return Err(format!(
                "local restatement obligation #{} does not resolve uniquely",
                restatement.index()
            ));
        }
    };
    inheritance_restatement(local_obligation, callee, far_obligation)?;
    Ok(far_obligation.id)
}

/// The RESTATEMENT half of an inheritance edge, shared by the cross-crate rule
/// ([`check_inherited`], L7(c)) and the same-module rule (WS1.6,
/// `validate::admit_local_inheritance`), so the two edges cannot drift apart.
///
/// `local` is the obligation the inheritance certificate discharges; `far` is
/// the obligation it inherits; `callee` is the function the certificate names.
/// The edge holds only when `local` is scoped to `callee`, has `far`'s kind,
/// and restates `far`'s formula EXACTLY (bindings included: the same clause
/// text read at a different sort or place is a different claim). Both formulas
/// must be present — an inherited claim must be stated, not implied.
///
/// This checks what the two obligations SAY, nothing else: whether `far` is
/// grounded is the caller's question (the dependency's verdict cross-crate,
/// the kernel tier locally), and so is whether `local` resolves uniquely.
pub(crate) fn inheritance_restatement(
    local: &ProofObligation,
    callee: FuncId,
    far: &ProofObligation,
) -> Result<(), String> {
    if local.function != Some(callee) {
        return Err(format!(
            "local restatement obligation #{} is scoped to {:?}, not the callee declaration #{}",
            local.id.index(),
            local.function.map(FuncId::index),
            callee.index()
        ));
    }
    if local.kind != far.kind {
        return Err(format!(
            "local restatement obligation #{} has kind {}, far obligation #{} has kind {}",
            local.id.index(),
            local.kind,
            far.id.index(),
            far.kind
        ));
    }
    match (&local.formula, &far.formula) {
        (Some(local_formula), Some(far_formula)) if local_formula == far_formula => Ok(()),
        (Some(_), Some(_)) => Err(format!(
            "local restatement obligation #{} does not restate far obligation #{}'s formula",
            local.id.index(),
            far.id.index()
        )),
        (None, _) => Err(format!(
            "local restatement obligation #{} carries no formula; an inherited claim must be \
             stated, not implied",
            local.id.index()
        )),
        (_, None) => Err(format!(
            "far obligation #{} carries no formula; a claim with no statement cannot be \
             restated",
            far.id.index()
        )),
    }
}

/// The proof authority the linked validator runs the module validator under:
/// the authenticated inheritance certificates, by exact lineage reference, on
/// top of the caller's own capability.
///
/// `validated_authority_refs` consults this only for `Discharged` rows and
/// feeds only the `Discharged` tier, so an authenticated inheritance can
/// ground the restatement it discharges and nothing else — never a
/// `ProofRef`, never a proof context, never another inheritance.
struct LinkedAuthority<'x> {
    inner: &'x dyn ModuleProofAuthority,
    admitted: &'x BTreeSet<ProofCertificateRef>,
}

impl ModuleProofAuthority for LinkedAuthority<'_> {
    fn replays_authority(
        &self,
        module: &Module,
        obligation: &ProofObligation,
        certificate: &ProofCertificate,
    ) -> bool {
        (certificate.obligation == obligation.id
            && self.admitted.contains(&certificate.lineage_ref()))
            || self
                .inner
                .replays_authority(module, obligation, certificate)
    }
}

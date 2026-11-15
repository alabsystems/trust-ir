// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Bounded, untrusted compositional proof candidates over shared named locals.
//!
//! This module installs no declarations, axioms, or interpretation. It builds
//! ordinary Pi/Exists/And terms and scoped candidates; no returned Rust value
//! establishes a proposition. Close the complete term through ONE LocalScope
//! and independently kernel-check it against the consumer's reconstructed goal.
//! Scoped candidate identity prevents accidental witness reuse, not deliberate
//! manufacture of an invalid candidate through the explicitly untrusted API.

use crate::proof_components::{OwnedProofCapture, ProofComponents};
use crate::scoped_local::{LocalScope, ScopedLocal, ScopedLocalAllocator};
use clean_kernel::{Expr, ExprKind, Level, Name};
use std::collections::HashMap;
use std::rc::Rc;

#[path = "proof_assembly_normalize.rs"]
pub(crate) mod normalize;
use normalize::NormalizeMemo;

#[cfg(test)]
#[path = "proof_assembly_tests.rs"]
mod tests;

fn app(name: &str, args: impl IntoIterator<Item = Expr>) -> Expr {
    Expr::apps(Expr::const_str(name), args)
}
fn at(name: &str, levels: Vec<Level>, args: impl IntoIterator<Item = Expr>) -> Expr {
    Expr::apps(Expr::const_(Name::from_string(name), levels), args)
}

type Result<T> = std::result::Result<T, String>;

/// Structural producer limits, not aggregate memory or kernel-replay bounds.
#[derive(Clone, Copy)]
pub struct ProofLimits {
    pub operations: usize,
    pub contexts: usize,
    pub captures: usize,
}

impl Default for ProofLimits {
    fn default() -> Self {
        Self {
            operations: 1_000_000,
            contexts: 65_536,
            captures: 262_144,
        }
    }
}

/// Candidate fact with a construction-scope identity, NOT proof authority.
/// Private fields prevent stale facts from being retagged as outer hypotheses.
#[derive(Clone)]
pub struct ScopedProofCandidate {
    proposition: Expr,
    proof: Expr,
    owner: Rc<()>,
    depth: usize,
    context: usize,
}

impl ScopedProofCandidate {
    pub fn proposition(&self) -> &Expr {
        &self.proposition
    }

    pub fn term(&self) -> &Expr {
        &self.proof
    }
}

/// A small compositional proof producer over ONE shared local owner. Context
/// membership is O(1): a fact records its depth and unique active-stack entry.
pub struct ProofAssembly {
    owner: Rc<()>,
    active: Vec<usize>,
    next_context: usize,
    operations: usize,
    limits: ProofLimits,
    normalized: NormalizeMemo,
    components: Option<ProofComponents>,
    component_captures: Vec<OwnedProofCapture>,
    component_threshold: usize,
    component_capture_ids: HashMap<clean_kernel::expr::FVarId, usize>,
}

impl ProofAssembly {
    pub fn new(limits: ProofLimits) -> Result<Self> {
        if limits.operations == 0
            || limits.contexts == 0
            || limits.captures == 0
            || limits.captures > u32::MAX as usize
        {
            return Err("invalid proof assembly construction limits".into());
        }
        Ok(Self {
            owner: Rc::new(()),
            active: vec![0],
            next_context: 1,
            operations: 0,
            limits,
            normalized: NormalizeMemo::default(),
            components: None,
            component_captures: Vec::new(),
            component_threshold: usize::MAX,
            component_capture_ids: HashMap::new(),
        })
    }

    /// Optionally retain genuine logical continuation bodies. Captures must
    /// describe the exact outer telescope; unknown locals fail at final close.
    pub fn retain_components(
        &mut self,
        components: ProofComponents,
        captures: Vec<OwnedProofCapture>,
        minimum_operations: usize,
    ) -> Result<()> {
        if !self.in_root_context()
            || self.components.is_some()
            || minimum_operations == 0
            || captures.len() > self.limits.captures
        {
            return Err("invalid proof component continuation context".into());
        }
        let ids: HashMap<_, _> = captures
            .iter()
            .enumerate()
            .map(|(index, capture)| (capture.local().id(), index))
            .collect();
        if ids.len() != captures.len() {
            return Err("duplicate proof component outer capture".into());
        }
        self.component_capture_ids = ids;
        self.components = Some(components);
        self.component_captures = captures;
        self.component_threshold = minimum_operations;
        Ok(())
    }

    pub fn take_components(&mut self) -> Result<Option<ProofComponents>> {
        if !self.in_root_context() {
            return Err("proof component continuation still active".into());
        }
        self.component_captures.clear();
        self.component_capture_ids.clear();
        Ok(self.components.take())
    }

    pub fn retaining_components(&self) -> bool {
        self.components.is_some()
    }

    /// A charged owner query for synchronizing an immutable lexical frontier.
    pub fn component_capture_known(&mut self, local: &ScopedLocal) -> Result<bool> {
        if self.components.is_none() {
            return Ok(false);
        }
        self.charge()?;
        Ok(self.component_capture_ids.contains_key(&local.id()))
    }

    /// Retain the actual binder supplied by a caller's own eliminator.
    pub fn note_component_parameter(&mut self, local: ScopedLocal) -> Result<()> {
        if self.components.is_some() {
            self.charge()?;
        }
        self.capture_component_local(OwnedProofCapture::Parameter(local))
    }

    /// Record a caller-owned lexical LET in the current continuation. This is
    /// untrusted capture metadata; its actual value is checked during replay.
    pub fn note_component_definition<A: ScopedLocalAllocator>(
        &mut self,
        allocator: &mut A,
        local: ScopedLocal,
        value: Expr,
    ) -> Result<Expr> {
        self.hoist_component_definition(allocator, local, value)
    }

    pub fn retain_root_component_definition(
        &mut self,
        local: ScopedLocal,
        value: Expr,
    ) -> Result<Expr> {
        if let Some(components) = &mut self.components {
            components.extend_base_definition(OwnedProofCapture::Definition {
                local: local.clone(),
                value: value.clone().into(),
            })?;
            self.charge()?;
            self.capture_component_local(OwnedProofCapture::Definition {
                local,
                value: value.clone().into(),
            })?;
        }
        Ok(value)
    }

    pub fn hoist_component_definition<A: ScopedLocalAllocator>(
        &mut self,
        allocator: &mut A,
        local: ScopedLocal,
        value: Expr,
    ) -> Result<Expr> {
        if self.components.is_none() {
            return Ok(value);
        }
        self.charge()?;
        let reference = self
            .components
            .as_mut()
            .expect("checked above")
            .retain_definition(allocator, &self.component_captures, &local, value)?;
        self.capture_component_local(OwnedProofCapture::Definition {
            local,
            value: reference.clone(),
        })?;
        Ok(reference.as_ref().clone())
    }

    pub fn component_definition_value(&self, local: &ScopedLocal) -> Option<Expr> {
        let index = *self.component_capture_ids.get(&local.id())?;
        match self.component_captures.get(index)? {
            OwnedProofCapture::Definition { value, .. } => Some(value.as_ref().clone()),
            _ => None,
        }
    }

    fn capture_component_local(&mut self, capture: OwnedProofCapture) -> Result<()> {
        if self.components.is_some() {
            if self.component_captures.len() >= self.limits.captures {
                return Err("proof component live capture limit".into());
            }
            if self
                .component_capture_ids
                .contains_key(&capture.local().id())
            {
                return Err("duplicate live proof component capture".into());
            }
            self.component_capture_ids
                .insert(capture.local().id(), self.component_captures.len());
            self.component_captures.push(capture);
        }
        Ok(())
    }

    fn retain_continuation<A: ScopedLocalAllocator>(
        &mut self,
        allocator: &mut A,
        started: usize,
        _capture_count: usize,
        proposition: &Expr,
        proof: Expr,
    ) -> Result<Expr> {
        if self.components.is_none()
            || self.operations.saturating_sub(started) < self.component_threshold
        {
            return Ok(proof);
        }
        self.charge()?;
        // Late recorded outer definitions may remain free in the result;
        // registered binders inside the result are removed by the component's
        // exact free-dependency walk, never by a stale entrance prefix.
        let captures = &self.component_captures;
        self.components
            .as_mut()
            .expect("checked above")
            .bind_scoped(allocator, captures, proposition.clone(), proof)
    }

    /// Construction limits, not expression-size or kernel-resource bounds.
    pub fn limits(&self) -> ProofLimits {
        self.limits
    }

    /// Whether no temporary witness/branch context is active. Not a proof
    /// validity check; callers still close and kernel-check the complete term.
    pub fn in_root_context(&self) -> bool {
        self.active.len() == 1
    }

    fn charge(&mut self) -> Result<()> {
        self.operations = self
            .operations
            .checked_add(1)
            .ok_or("proof operation overflow")?;
        if self.operations > self.limits.operations {
            return Err("proof assembly operation limit".into());
        }
        Ok(())
    }

    /// Refuse another producer's or an expired branch's handle. This tests
    /// construction provenance only, never the truth of the proposition.
    pub fn check_live(&self, fact: &ScopedProofCandidate) -> Result<()> {
        if !Rc::ptr_eq(&self.owner, &fact.owner)
            || self.active.get(fact.depth) != Some(&fact.context)
        {
            return Err("foreign or expired proof assembly handle".into());
        }
        Ok(())
    }

    /// No checking is implied by construction. Every caller ultimately supplies
    /// these terms to the caller's independent kernel check.
    pub fn candidate(&mut self, proposition: Expr, proof: Expr) -> Result<ScopedProofCandidate> {
        self.charge()?;
        let depth = self.active.len() - 1;
        Ok(ScopedProofCandidate {
            proposition,
            proof,
            owner: self.owner.clone(),
            depth,
            context: self.active[depth],
        })
    }

    /// Convert a deferred type to ordinary binders without inventing a meaning.
    /// Close once over the given dependent capture telescope, remove exactly
    /// that telescope, and reopen all captures in ONE simultaneous substitution.
    /// Capture count is bounded before collecting arguments or any u32 cast.
    /// Exact successful inputs may share their normalized graph within this
    /// producer; operation/capture/owner checks still precede every lookup.
    pub fn normalize_open<'a, I>(
        &mut self,
        scope: &LocalScope,
        captures: I,
        term: &Expr,
    ) -> Result<Expr>
    where
        I: IntoIterator<Item = &'a ScopedLocal>,
        I::IntoIter: DoubleEndedIterator + ExactSizeIterator + Clone,
    {
        self.charge()?;
        let captures = captures.into_iter();
        let count = captures.len();
        if count > self.limits.captures {
            return Err("proof capture limit".into());
        }
        if !captures.clone().all(|local| scope.owns(local)) {
            return Err("capture belongs to another local owner".into());
        }
        // A memo hit is still one normalization operation and must pass the
        // current capture/owner checks above. Only complete successful closes
        // are retained; no candidate or kernel authority is cached.
        let owner = scope.memo_owner();
        let key = normalize::key_hash(&owner, captures.clone(), term);
        if let Some(normalized) = self.normalized.get(key, &owner, captures.clone(), term) {
            return Ok(normalized);
        }
        let telescope = captures
            .clone()
            .rev()
            .fold(term.clone(), |body, local| local.lam(body));
        let mut body = scope.close(&telescope).map_err(|error| error.to_string())?;
        for _ in 0..count {
            let ExprKind::Lam(_, _, inner) = body.kind() else {
                return Err("closed capture telescope lost a binder".into());
            };
            body = inner.as_ref().clone();
        }
        // Actual instantiate_rev maps its first item to BVar(0), the
        // INNERMOST capture. Substitution remains one simultaneous operation;
        // the memo retains snapshots only if its graph/root-copy budget fits.
        let arguments: Vec<_> = captures
            .clone()
            .rev()
            .map(|local| local.term().clone())
            .collect();
        let normalized = body.instantiate_rev(&arguments);
        self.normalized.insert(
            key,
            owner,
            captures,
            term,
            &normalized,
            self.limits.captures,
        );
        Ok(normalized)
    }

    pub fn apply(
        &mut self,
        fact: &ScopedProofCandidate,
        argument: Expr,
    ) -> Result<ScopedProofCandidate> {
        self.check_live(fact)?;
        let ExprKind::Pi(_, _, body) = fact.proposition.kind() else {
            return Err("expected normalized function/implication premise".into());
        };
        self.candidate(
            body.instantiate(&argument),
            Expr::app(fact.proof.clone(), argument),
        )
    }

    pub fn and_at(
        &mut self,
        fact: &ScopedProofCandidate,
        index: usize,
    ) -> Result<ScopedProofCandidate> {
        self.check_live(fact)?;
        if index >= self.limits.operations.saturating_sub(self.operations) {
            return Err("conjunction projection exceeds proof budget".into());
        }
        let mut current = fact.clone();
        for position in 0..=index {
            let fields = head(&current.proposition, "And", 2)?;
            let left = fields[0].clone();
            let right = fields[1].clone();
            current = self.candidate(
                if position == index {
                    left.clone()
                } else {
                    right.clone()
                },
                app(
                    if position == index {
                        "And.left"
                    } else {
                        "And.right"
                    },
                    [left, right, current.proof],
                ),
            )?;
        }
        Ok(current)
    }

    /// Project an ordered conjunction prefix with one shared right spine.
    /// These are the same untrusted candidates as `and_at(fact, index)`;
    /// neither a trailing `True` nor the truth of any clause is established.
    /// A successful nonempty prefix charges exactly `2 * count - 1` ordinary
    /// candidate operations. Refused size/budget checks charge nothing, while
    /// malformed input retains all operations already performed before refusal.
    pub fn and_prefix(
        &mut self,
        fact: &ScopedProofCandidate,
        count: usize,
    ) -> Result<Vec<ScopedProofCandidate>> {
        self.check_live(fact)?;
        if count == 0 {
            return Ok(Vec::new());
        }
        let cost = count
            .checked_add(count - 1)
            .ok_or("conjunction prefix cost overflow")?;
        if cost > self.limits.operations.saturating_sub(self.operations) {
            return Err("conjunction prefix exceeds proof budget".into());
        }
        // Do not reserve from an external count: grow only as actual And
        // nodes are encountered, after the complete operation-cost preflight.
        let mut fields = Vec::new();
        let mut current = fact.clone();
        for index in 0..count {
            let parts = head(&current.proposition, "And", 2)?;
            let left = parts[0].clone();
            let right = parts[1].clone();
            fields.push(self.candidate(
                left.clone(),
                app(
                    "And.left",
                    [left.clone(), right.clone(), current.proof.clone()],
                ),
            )?);
            if index + 1 < count {
                current = self.candidate(
                    right.clone(),
                    app("And.right", [left, right, current.proof]),
                )?;
            }
        }
        Ok(fields)
    }

    /// Run a temporary construction scope. Handles made inside it expire when
    /// it returns, including an error or unwind caught by the caller. A panic
    /// is resumed unchanged after cleanup, not turned into a proof candidate.
    pub fn with_scope<T>(&mut self, action: impl FnOnce(&mut Self) -> Result<T>) -> Result<T> {
        self.charge()?;
        if self.next_context >= self.limits.contexts {
            return Err("proof assembly context limit".into());
        }
        let context = self.next_context;
        self.next_context = self
            .next_context
            .checked_add(1)
            .ok_or("proof context overflow")?;
        let previous_depth = self.active.len();
        let previous_captures = self.component_captures.len();
        self.active.push(context);
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| action(self)));
        self.active.truncate(previous_depth);
        for capture in self.component_captures.drain(previous_captures..) {
            self.component_capture_ids.remove(&capture.local().id());
        }
        match result {
            Ok(result) => result,
            Err(payload) => std::panic::resume_unwind(payload),
        }
    }

    /// Share candidate proofs through ordinary defining LETs, not hypotheses.
    /// Each alias retains its input's exact proposition; no normalization or
    /// kernel checking is performed. The wrapped proof must still be closed
    /// in the allocator's original local owner and independently kernel-checked.
    /// Even unused values remain in the LET telescope and must check at replay.
    ///
    /// All input handles are checked before allocation. The existing capture
    /// limit bounds the number of bindings, not graph bytes. A successful call
    /// costs N local allocations, N alias candidates, one temporary scope and
    /// one outer candidate, plus the continuation's normal cumulative charges.
    /// Empty input still enters/exits a scope. Aliases expire on success, error
    /// or unwind; spent proof/allocator budgets are never reset or rolled back.
    pub fn with_let_facts<A: ScopedLocalAllocator>(
        &mut self,
        allocator: &mut A,
        facts: &[ScopedProofCandidate],
        goal: Expr,
        continuation: impl FnOnce(
            &mut Self,
            &mut A,
            Vec<ScopedProofCandidate>,
        ) -> Result<ScopedProofCandidate>,
    ) -> Result<ScopedProofCandidate> {
        for fact in facts {
            self.check_live(fact)?;
        }
        if facts.len() > self.limits.captures {
            return Err("proof let binding limit".into());
        }
        let proof = self.with_scope(|logic| {
            let mut locals = Vec::new();
            let mut aliases = Vec::new();
            let mut definitions = Vec::new();
            for fact in facts {
                let local = allocator.allocate_local(fact.proposition.clone())?;
                aliases.push(logic.candidate(fact.proposition.clone(), local.term().clone())?);
                definitions.push(logic.note_component_definition(
                    allocator,
                    local.clone(),
                    fact.proof.clone(),
                )?);
                locals.push(local);
            }
            let started = logic.operations;
            let capture_count = logic.component_captures.len();
            let result = continuation(logic, allocator, aliases)?;
            logic.check_live(&result)?;
            if result.proposition != goal {
                return Err("let continuation changed the goal".into());
            }
            // Register the real definitions while their candidate scope is
            // live; declaration order is preserved by reverse wrapping.
            let proof = logic.retain_continuation(
                allocator,
                started,
                capture_count,
                &goal,
                result.proof,
            )?;
            Ok(locals
                .iter()
                .zip(&definitions)
                .rev()
                .fold(proof, |body, (local, value)| {
                    local.let_(value.clone(), body)
                }))
        })?;
        self.candidate(goal, proof)
    }

    pub fn introduce_forall<A: ScopedLocalAllocator>(
        &mut self,
        allocator: &mut A,
        goal: Expr,
        body: impl FnOnce(&mut Self, &mut A, ScopedLocal, Expr) -> Result<ScopedProofCandidate>,
    ) -> Result<ScopedProofCandidate> {
        let ExprKind::Pi(_, domain, remainder) = goal.kind() else {
            return Err("expected normalized universal goal".into());
        };
        let parameter = allocator.allocate_local(domain.as_ref().clone())?;
        let instance = remainder.instantiate(parameter.term());
        let proof = self.with_scope(|logic| {
            logic.capture_component_local(OwnedProofCapture::Parameter(parameter.clone()))?;
            let started = logic.operations;
            let capture_count = logic.component_captures.len();
            let result = body(logic, allocator, parameter.clone(), instance.clone())?;
            logic.check_live(&result)?;
            if result.proposition != instance {
                return Err("universal continuation changed the goal".into());
            }
            let proof = logic.retain_continuation(
                allocator,
                started,
                capture_count,
                &instance,
                result.proof,
            )?;
            Ok(parameter.lam(proof))
        })?;
        self.candidate(goal, proof)
    }

    pub fn eliminate_exists<A: ScopedLocalAllocator>(
        &mut self,
        allocator: &mut A,
        premise: &ScopedProofCandidate,
        goal: Expr,
        continuation: impl FnOnce(
            &mut Self,
            &mut A,
            ScopedLocal,
            ScopedProofCandidate,
        ) -> Result<ScopedProofCandidate>,
    ) -> Result<ScopedProofCandidate> {
        self.check_live(premise)?;
        let fields = head(&premise.proposition, "Exists", 2)?;
        let witness_type = fields[0].clone();
        let predicate = fields[1].clone();
        let levels = const_levels(&premise.proposition, "Exists")?;
        let witness = allocator.allocate_local(witness_type.clone())?;
        let instance = apply_lambda(&predicate, witness.term())?;
        let evidence = allocator.allocate_local(instance.clone())?;
        let branch = self.with_scope(|logic| {
            logic.capture_component_local(OwnedProofCapture::Parameter(witness.clone()))?;
            logic.capture_component_local(OwnedProofCapture::Parameter(evidence.clone()))?;
            let started = logic.operations;
            let capture_count = logic.component_captures.len();
            let fact = logic.candidate(instance, evidence.term().clone())?;
            let result = continuation(logic, allocator, witness.clone(), fact)?;
            logic.check_live(&result)?;
            if result.proposition != goal {
                return Err("existential continuation changed the outer goal".into());
            }
            let proof = logic.retain_continuation(
                allocator,
                started,
                capture_count,
                &goal,
                result.proof,
            )?;
            Ok(witness.lam(evidence.lam(proof)))
        })?;
        self.candidate(
            goal.clone(),
            at(
                "Exists.elim",
                levels,
                [witness_type, predicate, goal, premise.proof.clone(), branch],
            ),
        )
    }

    pub fn introduce_exists(
        &mut self,
        goal: Expr,
        witness: Expr,
        evidence: &ScopedProofCandidate,
    ) -> Result<ScopedProofCandidate> {
        self.check_live(evidence)?;
        let fields = head(&goal, "Exists", 2)?;
        let witness_type = fields[0].clone();
        let predicate = fields[1].clone();
        if evidence.proposition != apply_lambda(&predicate, &witness)? {
            return Err("existential witness evidence has another proposition".into());
        }
        let levels = const_levels(&goal, "Exists")?;
        self.candidate(
            goal,
            at(
                "Exists.intro",
                levels,
                [witness_type, predicate, witness, evidence.proof.clone()],
            ),
        )
    }
}

fn head(term: &Expr, name: &str, arity: usize) -> Result<Vec<Expr>> {
    if !matches!(term.get_app_fn().kind(), ExprKind::Const(actual, _) if actual == &Name::from_string(name))
    {
        return Err(format!("expected normalized {name} proposition"));
    }
    // Bound the spine before the allocating convenience accessor.
    if term.get_app_args_iter().take(arity + 1).count() != arity {
        return Err(format!("wrong {name} proposition arity"));
    }
    let fields = term.get_app_args();
    Ok(fields.into_iter().cloned().collect())
}

fn const_levels(term: &Expr, name: &str) -> Result<Vec<clean_kernel::Level>> {
    match term.get_app_fn().kind() {
        ExprKind::Const(actual, levels) if actual == &Name::from_string(name) => {
            Ok(levels.to_vec())
        }
        _ => Err(format!("expected {name} head")),
    }
}

fn apply_lambda(function: &Expr, argument: &Expr) -> Result<Expr> {
    match function.kind() {
        ExprKind::Lam(_, _, body) => Ok(body.instantiate(argument)),
        _ => Err("expected normalized predicate lambda".into()),
    }
}

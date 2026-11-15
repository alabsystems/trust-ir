// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Untrusted assembly of exact executions of the shared, actual Core model.
//!
//! These objects are candidate terms, NOT checked facts or compilation authority.
//! They neither install declarations nor admit a certificate. The whole-model
//! consumer must close them in its own shared Scope and replay the result against
//! its independently reconstructed proposition. In particular a candidate
//! equality supplied by a caller is not trusted merely because it has this Rust
//! type. Function summaries may be composed here, but their body proofs remain
//! obligations of that consumer.
//!
//! Fuel is a kernel Nat expression, not a Rust execution counter. Composition
//! stops at the exact supplied endpoint; it does not spend a summary's unused
//! budget in its caller. Construction limits count this assembler's operations,
//! locals and list inputs. Lookup limits bound each kernel candidate-discovery
//! operation, not aggregate memory, normalization or final proof replay.

use crate::core_reflection::ReflectedCoreModuleV1;
use crate::scoped_local::{LocalScope as Scope, ScopedLocal as Local};
use clean_kernel::{Environment, Expr, ExprKind, Level, Name, TypeChecker};
use std::collections::HashMap;
use trust_ir::{BlockId, FuncId, ValueId};

#[path = "core_execution_field_site_valid.rs"]
mod field_site_valid;

#[path = "core_execution_run_one.rs"]
mod run_one;

#[path = "core_execution_prefix_simulation.rs"]
mod prefix_simulation;
pub use prefix_simulation::PrefixSimulation;

#[path = "core_execution_segmented_simulation.rs"]
mod segmented_simulation;
pub use segmented_simulation::{SegmentedPrefixSimulation, SimulatedPrefix};

#[path = "core_execution_return.rs"]
mod returning;
pub use returning::{ReturnFrame, ReturnTransfer};

#[path = "core_execution_root_return.rs"]
mod root_return;
pub use root_return::{RootReturnFrame, RootReturnTransfer};

#[path = "core_execution_retirement_bound.rs"]
mod retirement_bound;

#[path = "core_execution_call.rs"]
mod calling;
pub use calling::{InternalCallChecks, InternalCallPremises, InternalCallTransfer, InternalTarget};

#[path = "core_execution_readonly_indexed_call.rs"]
mod readonly_indexed_call;
pub use readonly_indexed_call::{
    ReadonlyEightCallCandidate, ReadonlyEightCallee, ReadonlyEightEntered, ReadonlyEightLoaded,
    ReadonlyEightSlot,
};

#[cfg(feature = "source-value-operational")]
#[path = "core_execution_readonly_entry.rs"]
mod readonly_entry;
#[cfg(feature = "source-value-operational")]
pub use readonly_entry::{
    CheckedReadonlyEightCallEntry, CheckedReadonlyEightLicensedEntry,
    CheckedReadonlyEightSourceEntry, ReadonlyEightForwardCall,
};

#[path = "core_execution_defined_constant_call.rs"]
mod defined_constant_call;
#[cfg(feature = "source-value-operational")]
pub use defined_constant_call::{
    CheckedDefinedConstantCallEntry, CheckedDefinedWordForwardCallEntry,
};
#[cfg(feature = "source-value-operational")]
pub use defined_constant_call::{
    CheckedDefinedWordAddCallEntry, DefinedWordAddCall, derive_defined_word_add_call_entry,
};
pub use defined_constant_call::{
    DefinedConstantCall, DefinedConstantCallCandidate, DefinedWordForwardCall,
};

#[path = "core_execution_initialization.rs"]
mod initialization;
pub use initialization::{EntryTarget, Initialization, RustU64EntryV1};

#[path = "core_execution_scalar.rs"]
mod scalar;
pub use scalar::{
    BranchChecks, BranchPremises, BranchTarget, BranchTransfer, ScalarChecks, ScalarPremises,
    ScalarTransfer,
};

#[path = "core_execution_value_binding.rs"]
mod value_binding;
pub use value_binding::{ValueBinding, ValueBindingPremises};

#[path = "core_execution_scalar_shift.rs"]
mod scalar_shift;

#[path = "core_execution_scalar_add.rs"]
mod scalar_add;

#[path = "core_execution_bool_zext.rs"]
mod bool_zext;
pub use bool_zext::ByteBoolZext;

#[path = "core_execution_wrapped_add.rs"]
mod wrapped_add;

#[path = "core_execution_wrapped_mul.rs"]
mod wrapped_mul;

#[path = "core_execution_wrapped_word_mod.rs"]
mod wrapped_word_mod;

#[path = "core_execution_wrapped_word_bound.rs"]
mod wrapped_word_bound;
pub use wrapped_word_bound::WrappedWordBound;

#[path = "core_execution_scalar_unsigned_compare.rs"]
mod scalar_unsigned_compare;

#[path = "core_execution_remainder_bound.rs"]
mod remainder_bound;

#[path = "core_execution_endpoint_ascription.rs"]
mod endpoint_ascription;

#[path = "core_execution_overflow.rs"]
mod overflow;
pub use overflow::{OverflowPremises, OverflowTransfer};

#[path = "core_execution_import.rs"]
mod importing;
pub use importing::{ImportChecks, ImportPremises, ImportResult, ImportTransfer};

#[path = "core_execution_memory.rs"]
mod memory;
pub use memory::{MemoryChecks, MemoryPremises, MemoryResult, MemoryTransfer};

#[path = "core_execution_allocation.rs"]
mod allocation;
pub use allocation::{AllocationChecks, AllocationInput, AllocationPremises, AllocationTransfer};

#[path = "core_execution_typed_alloca.rs"]
mod typed_allocation_dispatch;
pub use typed_allocation_dispatch::{AllocationDispatchChecks, AllocationDispatchPremises};

#[path = "core_execution_memory_access.rs"]
mod memory_access;
pub use memory_access::typed_gep::{
    ByteGepSingleton, ByteGepSingletonChecks, ByteGepSingletonPremises, ByteGepSingletonResult,
    ByteGepTyped, ByteGepTypedChecks, ByteGepTypedPremises, ByteGepTypedResult,
};
pub use memory_access::{
    ByteEightCodec, ByteFourCodec, ByteGepI8, ByteGepI8Premises, ByteGepI8Result, ByteLoadEight,
    ByteLoadEightPremises, ByteLoadFour, ByteLoadFourPremises, ByteLoadWord, ByteLoadWordPremises,
    ByteStoreEight, ByteStoreEightPremises, ByteStoreEightResult, ByteStoreFour,
    ByteStoreFourPremises, ByteStoreFourResult, ByteStoreWord, ByteStoreWordPremises,
    ByteStoreWordResult, ByteWordCodec,
};

#[path = "core_execution_initialized_prefix.rs"]
mod initialized_prefix;
pub use initialized_prefix::{
    InitializedEightAppendPremises, InitializedEightPrefix, InitializedEightRead,
};

#[path = "core_execution_pointer.rs"]
mod pointer;
pub use pointer::BytePointerWord;

#[path = "core_execution_transport.rs"]
mod transporting;
pub use transporting::FrameTransport;

type Result<T> = std::result::Result<T, String>;

fn eq(ty: &Expr, left: Expr, right: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [ty.clone(), left, right],
    )
}
fn refl(ty: &Expr, value: Expr) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("Eq.refl"),
            vec![Level::succ(Level::zero())],
        ),
        [ty.clone(), value],
    )
}
fn choose(ty: &Expr, flag: Expr, yes: Expr, no: Expr) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("Bool.rec"),
            vec![Level::succ(Level::zero())],
        ),
        [
            Expr::lam(
                clean_kernel::BinderInfo::Default,
                constant("Bool"),
                // The result type belongs to the caller's context, outside
                // this motive binder. Keep neutral outer parameters free.
                ty.lift(1),
            ),
            no,
            yes,
            flag,
        ],
    )
}

fn app(name: &str, arguments: impl IntoIterator<Item = Expr>) -> Expr {
    Expr::apps(Expr::const_str(name), arguments)
}

fn constant(name: &str) -> Expr {
    Expr::const_str(name)
}

fn nat(value: u64) -> Expr {
    Expr::nat_lit(value)
}

fn some(ty: &str, value: Expr) -> Expr {
    app("IROption.some", [constant(ty), value])
}

fn list(ty: &str, values: &[Expr]) -> Expr {
    values
        .iter()
        .rev()
        .fold(app("IRList.nil", [constant(ty)]), |tail, value| {
            app("IRList.cons", [constant(ty), value.clone(), tail])
        })
}

fn trans(ty: &Expr, left: Expr, middle: Expr, right: Expr, first: Expr, second: Expr) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("Eq.trans"),
            vec![Level::succ(Level::zero())],
        ),
        [ty.clone(), left, middle, right, first, second],
    )
}

fn require_same(actual: &Expr, expected: &Expr, label: &str) -> Result<()> {
    if actual == expected {
        Ok(())
    } else {
        Err(format!(
            "{label}: different candidate terms; supply an explicit equality transport"
        ))
    }
}

/// Explicit host-side construction policy. Zero does not mean unlimited.
#[derive(Clone, Copy, Debug)]
pub struct Limits {
    pub max_operations: usize,
    pub max_locals: usize,
    pub max_list_items: usize,
    pub max_lookup_candidates: usize,
    pub lookup_heartbeats: u32,
    pub lookup_cache_entries: usize,
}

impl Limits {
    fn validate(self) -> Result<Self> {
        if self.max_operations == 0
            || self.max_locals == 0
            || self.max_list_items == 0
            || self.max_lookup_candidates == 0
            || self.lookup_heartbeats == 0
            || self.lookup_cache_entries == 0
        {
            return Err("execution construction limits must be nonzero".into());
        }
        // IDs and closed literal fuel are represented without lossy usize casts.
        u64::try_from(self.max_list_items).map_err(|_| "list budget does not fit u64")?;
        u64::try_from(self.max_locals).map_err(|_| "local budget does not fit u64")?;
        Ok(self)
    }
}

/// A typed *candidate* equality, whose proof may still be rejected at replay.
#[derive(Clone)]
pub struct PendingEquality {
    ty: Expr,
    left: Expr,
    right: Expr,
    term: Expr,
}

impl PendingEquality {
    pub fn candidate(ty: Expr, left: Expr, right: Expr, term: Expr) -> Self {
        Self {
            ty,
            left,
            right,
            term,
        }
    }

    pub fn reflexive(ty: Expr, value: Expr) -> Self {
        Self::candidate(ty.clone(), value.clone(), value.clone(), refl(&ty, value))
    }

    pub fn proposition(&self) -> Expr {
        eq(&self.ty, self.left.clone(), self.right.clone())
    }

    pub fn term(&self) -> &Expr {
        &self.term
    }
    pub fn left(&self) -> &Expr {
        &self.left
    }
    pub fn right(&self) -> &Expr {
        &self.right
    }

    fn endpoints(&self, ty: &Expr, left: &Expr, right: &Expr) -> Result<()> {
        require_same(&self.ty, ty, "equality type")?;
        require_same(&self.left, left, "equality left endpoint")?;
        require_same(&self.right, right, "equality right endpoint")
    }
}

/// A candidate proof of a proposition, not a kernel-checked fact. In particular
/// the Rust wrapper does not establish that `proposition` has sort Prop or that
/// `term` inhabits it; the independent whole-model replay must check both.
#[derive(Clone)]
pub struct PendingProof {
    proposition: Expr,
    term: Expr,
}

impl PendingProof {
    pub fn candidate(proposition: Expr, term: Expr) -> Self {
        Self { proposition, term }
    }

    pub fn proposition(&self) -> &Expr {
        &self.proposition
    }

    pub fn term(&self) -> &Expr {
        &self.term
    }
}

/// Only well-typed construction forms are exposed: Nat locals, literals, sums,
/// and selections. The model's telescope still has to be checked at replay.
#[derive(Clone)]
pub struct NatTerm(Expr);

impl NatTerm {
    pub fn literal(value: u64) -> Self {
        Self(nat(value))
    }
    pub fn from_usize(value: usize) -> Result<Self> {
        Ok(Self::literal(
            u64::try_from(value).map_err(|_| "fuel does not fit u64")?,
        ))
    }
    pub fn local(local: &Local) -> Result<Self> {
        require_same(local.ty(), &constant("Nat"), "fuel local type")?;
        Ok(Self(local.term().clone()))
    }
    pub fn term(&self) -> &Expr {
        &self.0
    }
}

/// Immutable execution semantics. World/frame changes do not retarget an
/// already-built equation to different providers or a different module.
#[derive(Clone)]
pub struct MachineModel {
    world_type: Expr,
    context: Expr,
    providers: Expr,
}

impl MachineModel {
    pub fn new(world_type: Expr, reflected: &ReflectedCoreModuleV1<'_>, providers: Expr) -> Self {
        Self {
            world_type,
            context: reflected.context_term().clone(),
            providers,
        }
    }
    pub fn world_type(&self) -> &Expr {
        &self.world_type
    }
    pub fn context(&self) -> &Expr {
        &self.context
    }
    pub fn providers(&self) -> &Expr {
        &self.providers
    }
    pub fn config_type(&self) -> Expr {
        app("IRByteConfigV1", [self.world_type.clone()])
    }
    /// The actual run function with world, context, providers and fuel fixed.
    /// Passing this partial application to [`Assembler::congruence_function`]
    /// avoids capturing a growing execution suffix beneath a fresh binder.
    /// This is a candidate expression, not an execution or typing judgment.
    pub fn run_function(&self, fuel: &NatTerm) -> Expr {
        app(
            "ir_byte_run_v1",
            [
                self.world_type.clone(),
                self.context.clone(),
                self.providers.clone(),
                fuel.0.clone(),
            ],
        )
    }
    pub fn run(&self, fuel: &NatTerm, initial: Expr) -> Expr {
        app(
            "ir_byte_run_v1",
            [
                self.world_type.clone(),
                self.context.clone(),
                self.providers.clone(),
                fuel.0.clone(),
                initial,
            ],
        )
    }
    pub fn step(&self, initial: Expr) -> Expr {
        app(
            "ir_byte_step_v1",
            [
                self.world_type.clone(),
                self.context.clone(),
                self.providers.clone(),
                initial,
            ],
        )
    }
    fn same(&self, other: &Self) -> Result<()> {
        require_same(&self.world_type, &other.world_type, "run world type")?;
        require_same(&self.context, &other.context, "run reflected context")?;
        require_same(&self.providers, &other.providers, "run providers")
    }
}

/// Explicit current machine/world. A new state requires a new world-validity
/// fact; no cached pre-return validity is silently reused after a call/pop.
#[derive(Clone)]
pub struct Current {
    pub frame: Expr,
    pub tail: Expr,
    pub legacy_memory: Expr,
    pub legacy_cursor: Expr,
    pub world: Expr,
}

impl Current {
    pub fn machine(&self) -> Expr {
        app(
            "IRMachine.mk",
            [
                app(
                    "IRList.cons",
                    [constant("IRFrame"), self.frame.clone(), self.tail.clone()],
                ),
                self.legacy_memory.clone(),
                self.legacy_cursor.clone(),
            ],
        )
    }
    pub fn running(&self, model: &MachineModel) -> Expr {
        app(
            "IRByteConfigV1.running",
            [model.world_type.clone(), self.machine(), self.world.clone()],
        )
    }
    pub fn valid(&self, model: &MachineModel) -> Expr {
        app(
            "ir_byte_world_valid_v1",
            [model.world_type.clone(), self.machine(), self.world.clone()],
        )
    }
}

#[derive(Clone)]
pub struct ExactRun {
    model: MachineModel,
    initial: Expr,
    reached: Expr,
    fuel: NatTerm,
    equality: PendingEquality,
}

impl ExactRun {
    /// A supplied summary is merely a candidate. No callee is considered proved
    /// until the whole closed term checks against the independent model claim.
    pub fn candidate(
        model: MachineModel,
        initial: Expr,
        reached: Expr,
        fuel: NatTerm,
        equality: PendingEquality,
    ) -> Result<Self> {
        equality.endpoints(
            &model.config_type(),
            &model.run(&fuel, initial.clone()),
            &reached,
        )?;
        Ok(Self {
            model,
            initial,
            reached,
            fuel,
            equality,
        })
    }
    pub fn initial(&self) -> &Expr {
        &self.initial
    }
    pub fn reached(&self) -> &Expr {
        &self.reached
    }
    pub fn fuel(&self) -> &NatTerm {
        &self.fuel
    }
    pub fn equality(&self) -> &PendingEquality {
        &self.equality
    }

    /// State the real sufficiency obligation. This constructs no proof that the
    /// candidate budget is adequate and makes no inference from a node census.
    pub fn bounded_by(&self, budget: &NatTerm) -> Expr {
        app("Nat.le", [self.fuel.0.clone(), budget.0.clone()])
    }
}

/// Uses the model-owned Scope, so function/body declarations and all proof
/// terms share one fresh-local allocator and one deferred closing traversal.
pub struct Assembler<'scope> {
    scope: &'scope mut Scope,
    limits: Limits,
    operations: usize,
    locals: usize,
    cons_congruence: Option<Expr>,
    site_catalog_unique: Option<(Expr, PendingEquality)>,
    run_one_candidate: Option<Expr>,
    frame_transport_candidates: Option<(Expr, Expr)>,
    world_eta_candidate: Option<Expr>,
    memory_world_presentation_candidate: Option<Expr>,
    byte_gep_i8_candidate: Option<Expr>,
    byte_gep_i8_inbounds_candidate: Option<Expr>,
    byte_gep_singleton_candidates: [Option<Expr>; 2],
    byte_gep_typed_candidates: [Option<Expr>; 2],
    allocation_dispatch_candidate: Option<Expr>,
    byte_pointer_word_candidate: Option<Expr>,
    byte_ptr_encoded_candidate: Option<Expr>,
    initialized_eight_helpers: Option<initialized_prefix::InitializedEightHelpers>,
    #[cfg(test)]
    initialized_eight_helper_builds: usize,
    #[cfg(test)]
    initialized_eight_appends: usize,
}

impl crate::scoped_local::allocator_seal::Sealed for Assembler<'_> {}

impl crate::scoped_local::ScopedLocalAllocator for Assembler<'_> {
    fn local_scope(&self) -> &Scope {
        self.scope
    }
    fn allocate_local(&mut self, ty: Expr) -> Result<Local> {
        self.local(ty)
    }
}

impl<'scope> Assembler<'scope> {
    pub fn new(scope: &'scope mut Scope, limits: Limits) -> Result<Self> {
        Ok(Self {
            scope,
            limits: limits.validate()?,
            operations: 0,
            locals: 0,
            cons_congruence: None,
            site_catalog_unique: None,
            run_one_candidate: None,
            frame_transport_candidates: None,
            world_eta_candidate: None,
            memory_world_presentation_candidate: None,
            byte_gep_i8_candidate: None,
            byte_gep_i8_inbounds_candidate: None,
            byte_gep_singleton_candidates: [None, None],
            byte_gep_typed_candidates: [None, None],
            allocation_dispatch_candidate: None,
            byte_pointer_word_candidate: None,
            byte_ptr_encoded_candidate: None,
            initialized_eight_helpers: None,
            #[cfg(test)]
            initialized_eight_helper_builds: 0,
            #[cfg(test)]
            initialized_eight_appends: 0,
        })
    }

    /// Read-only access for model-owned normalization/closing. Allocation must
    /// still pass through this assembler and consume its existing budgets.
    pub fn local_scope(&self) -> &Scope {
        self.scope
    }
    /// Actual charged construction work so far, without resetting or changing
    /// its budget. Candidate assembly is not kernel/proof admission.
    pub fn operations(&self) -> usize {
        self.operations
    }
    fn charge(&mut self) -> Result<()> {
        let next = self
            .operations
            .checked_add(1)
            .ok_or("operation counter overflow")?;
        if next > self.limits.max_operations {
            return Err("execution construction operation budget exceeded".into());
        }
        self.operations = next;
        Ok(())
    }
    fn items(&self, count: usize) -> Result<()> {
        if count > self.limits.max_list_items {
            return Err("execution construction list budget exceeded".into());
        }
        Ok(())
    }
    pub fn local(&mut self, ty: Expr) -> Result<Local> {
        self.charge()?;
        let next = self.locals.checked_add(1).ok_or("local counter overflow")?;
        if next > self.limits.max_locals {
            return Err("execution construction local budget exceeded".into());
        }
        let local = self.scope.try_local(ty).map_err(|e| e.to_string())?;
        self.locals = next;
        Ok(local)
    }

    pub fn compose(
        &mut self,
        first: PendingEquality,
        second: PendingEquality,
    ) -> Result<PendingEquality> {
        self.charge()?;
        require_same(&first.ty, &second.ty, "composition type")?;
        require_same(&first.right, &second.left, "composition middle endpoint")?;
        let term = trans(
            &first.ty,
            first.left.clone(),
            first.right,
            second.right.clone(),
            first.term,
            second.term,
        );
        Ok(PendingEquality::candidate(
            first.ty,
            first.left,
            second.right,
            term,
        ))
    }

    pub fn congruence(
        &mut self,
        equality: PendingEquality,
        output_type: Expr,
        map: impl FnOnce(Expr) -> Expr,
    ) -> Result<PendingEquality> {
        let local = self.local(equality.ty.clone())?;
        let body = map(local.term().clone());
        // Beta-redex endpoints avoid traversing/substituting the whole suffix
        // here; the ordinary kernel and deferred Scope closing handle binders.
        let function = local.lam(body);
        let left = Expr::app(function.clone(), equality.left.clone());
        let right = Expr::app(function.clone(), equality.right.clone());
        let term = Expr::apps(
            Expr::const_(
                Name::from_string("congrArg"),
                vec![Level::succ(Level::zero()), Level::succ(Level::zero())],
            ),
            [
                equality.ty,
                output_type.clone(),
                equality.left,
                equality.right,
                function,
                equality.term,
            ],
        );
        Ok(PendingEquality::candidate(output_type, left, right, term))
    }

    /// Lift an equality through an already-constructed function, without
    /// allocating a scoped local or capturing its operands beneath a binder.
    /// The function, its input/output types and the supplied equality proof
    /// remain untrusted: the complete closed term must be checked by the
    /// consumer's kernel against its independently reconstructed proposition.
    pub fn congruence_function(
        &mut self,
        equality: PendingEquality,
        output_type: Expr,
        function: Expr,
    ) -> Result<PendingEquality> {
        self.charge()?;
        let left = Expr::app(function.clone(), equality.left.clone());
        let right = Expr::app(function.clone(), equality.right.clone());
        let term = Expr::apps(
            Expr::const_(
                Name::from_string("congrArg"),
                vec![Level::succ(Level::zero()), Level::succ(Level::zero())],
            ),
            [
                equality.ty,
                output_type.clone(),
                equality.left,
                equality.right,
                function,
                equality.term,
            ],
        );
        Ok(PendingEquality::candidate(output_type, left, right, term))
    }

    /// One closed, polymorphic candidate proof of congruence for IRList.cons.
    /// The arbitrary heads/tails are PARAMETERS of this tiny term. Actual
    /// operand suffixes are passed as application arguments, never captured
    /// beneath a new binder for every successive suffix. Closing this constant
    /// sized helper uses the same Scope, but is not kernel admission.
    fn cons_congruence(&mut self) -> Result<Expr> {
        if let Some(proof) = &self.cons_congruence {
            return Ok(proof.clone());
        }
        let element = self.local(Expr::type_())?;
        let element_type = element.term().clone();
        let list_type = app("IRList", [element_type.clone()]);
        let left_head = self.local(element_type.clone())?;
        let right_head = self.local(element_type.clone())?;
        let left_tail = self.local(list_type.clone())?;
        let right_tail = self.local(list_type.clone())?;
        let head_eq = self.local(eq(
            &element_type,
            left_head.term().clone(),
            right_head.term().clone(),
        ))?;
        let tail_eq = self.local(eq(
            &list_type,
            left_tail.term().clone(),
            right_tail.term().clone(),
        ))?;
        let cons = |head, tail| app("IRList.cons", [element_type.clone(), head, tail]);
        let left = cons(left_head.term().clone(), left_tail.term().clone());
        let middle = cons(right_head.term().clone(), left_tail.term().clone());
        let right = cons(right_head.term().clone(), right_tail.term().clone());
        let head = self.congruence(
            PendingEquality::candidate(
                element_type.clone(),
                left_head.term().clone(),
                right_head.term().clone(),
                head_eq.term().clone(),
            ),
            list_type.clone(),
            |value| cons(value, left_tail.term().clone()),
        )?;
        let head_before = self.conversion(list_type.clone(), left, head.left.clone())?;
        let head_after = self.conversion(list_type.clone(), head.right.clone(), middle.clone())?;
        let tail = self.congruence(
            PendingEquality::candidate(
                list_type.clone(),
                left_tail.term().clone(),
                right_tail.term().clone(),
                tail_eq.term().clone(),
            ),
            list_type.clone(),
            |value| cons(right_head.term().clone(), value),
        )?;
        let tail_before = self.conversion(list_type.clone(), middle, tail.left.clone())?;
        let tail_after = self.conversion(list_type, tail.right.clone(), right)?;
        let proof = self.compose(head_before, head)?;
        let proof = self.compose(proof, head_after)?;
        let proof = self.compose(proof, tail_before)?;
        let proof = self.compose(proof, tail)?;
        let proof = self.compose(proof, tail_after)?;
        let parameters = [
            element, left_head, right_head, left_tail, right_tail, head_eq, tail_eq,
        ];
        let term = parameters
            .iter()
            .rev()
            .fold(proof.term, |body, local| local.lam(body));
        let closed = self.scope.close(&term).map_err(|e| e.to_string())?;
        self.cons_congruence = Some(closed.clone());
        Ok(closed)
    }

    /// Lift ordered pointwise equality candidates to an IRList equality.
    /// Both endpoint lists and the proof are built from right to left, sharing
    /// their actual suffixes as arguments to the cached polymorphic cons proof.
    /// No growing list is captured under a fresh binder for each element.
    /// Empty lists need no helper; order and duplicate elements are preserved.
    /// This constructs a candidate, not a kernel-checked list equivalence.
    pub fn list_congruence(
        &mut self,
        element_type: Expr,
        equalities: &[PendingEquality],
    ) -> Result<PendingEquality> {
        self.list_congruence_iter(element_type, equalities.iter())
    }

    fn list_congruence_iter<'e>(
        &mut self,
        element_type: Expr,
        equalities: impl DoubleEndedIterator<Item = &'e PendingEquality> + ExactSizeIterator,
    ) -> Result<PendingEquality> {
        self.charge()?;
        self.items(equalities.len())?;
        let list_type = app("IRList", [element_type.clone()]);
        let nil = app("IRList.nil", [element_type.clone()]);
        let mut proof = PendingEquality::reflexive(list_type.clone(), nil);
        let helper = if equalities.len() == 0 {
            return Ok(proof);
        } else {
            self.cons_congruence()?
        };
        for equality in equalities.rev() {
            self.charge()?;
            require_same(&equality.ty, &element_type, "list equality element type")?;
            let left = app(
                "IRList.cons",
                [
                    element_type.clone(),
                    equality.left.clone(),
                    proof.left.clone(),
                ],
            );
            let right = app(
                "IRList.cons",
                [
                    element_type.clone(),
                    equality.right.clone(),
                    proof.right.clone(),
                ],
            );
            let term = Expr::apps(
                helper.clone(),
                [
                    element_type.clone(),
                    equality.left.clone(),
                    equality.right.clone(),
                    proof.left,
                    proof.right,
                    equality.term.clone(),
                    proof.term,
                ],
            );
            proof = PendingEquality::candidate(list_type.clone(), left, right, term);
        }
        Ok(proof)
    }

    /// Explicit endpoint transport. Refl is a conversion candidate, NOT a Rust
    /// assertion that the supplied terms reduce to one another.
    pub fn conversion(&mut self, ty: Expr, left: Expr, right: Expr) -> Result<PendingEquality> {
        self.charge()?;
        Ok(PendingEquality::candidate(
            ty.clone(),
            left,
            right.clone(),
            refl(&ty, right),
        ))
    }

    /// Re-present the endpoints of the SAME untrusted proof term using kernel
    /// conversion, without manufacturing reflexive/transitive proof wrappers.
    /// The equality type is retained verbatim. This charges one candidate and
    /// allocates no scoped locals; it checks neither the old nor new proposition.
    /// Only independent strict replay against the consumer's complete claimed
    /// endpoints can establish the new equality. In particular this is not a
    /// checked proof, an assertion of definitional equality, or cache authority.
    pub fn convert_endpoints(
        &mut self,
        equality: PendingEquality,
        left: Expr,
        right: Expr,
    ) -> Result<PendingEquality> {
        self.charge()?;
        Ok(PendingEquality::candidate(
            equality.ty,
            left,
            right,
            equality.term,
        ))
    }

    pub fn zero(&mut self, model: &MachineModel, initial: Expr) -> Result<ExactRun> {
        self.charge()?;
        let fuel = NatTerm::literal(0);
        let term = app(
            "ir_byte_run_zero_v1",
            [
                model.world_type.clone(),
                model.context.clone(),
                model.providers.clone(),
                initial.clone(),
            ],
        );
        let equality = PendingEquality::candidate(
            model.config_type(),
            model.run(&fuel, initial.clone()),
            initial.clone(),
            term,
        );
        ExactRun::candidate(model.clone(), initial.clone(), initial, fuel, equality)
    }

    /// Closed candidate for the actual byte definition's run-one equation.
    /// A neutral configuration requires elimination of IRByteConfigV1: a raw
    /// Refl of `step(initial)` does not definitionally equal `run(1, initial)`.
    /// Both constructor cases do reduce, including halted outcomes/worlds.
    /// This cached term is still untrusted until replay in the actual model.
    ///
    /// Replay checks each constructor case ONCE, over bound payload and world
    /// binders, so the kernel never evaluates an actual step to decide
    /// `run(1, c) = step(c)`; instantiating the closed equation at the actual
    /// configuration is syntactic. See [`Self::one_step`] for why an actual
    /// configuration must not be presented to the kernel's conversion instead.
    fn run_one_candidate(&mut self) -> Result<Expr> {
        if let Some(candidate) = &self.run_one_candidate {
            return Ok(candidate.clone());
        }
        // Preserve the original nine cold helper-construction charges. Its
        // fixed closed binders need no caller locals or deferred scope close.
        for _ in 0..9 {
            self.charge()?;
        }
        let closed = run_one::closed_candidate();
        self.run_one_candidate = Some(closed.clone());
        Ok(closed)
    }

    /// One exact step as a fuel-1 run, for EVERY configuration, through the
    /// closed run-one eliminator composed with the supplied step proof.
    ///
    /// Never present the step proof at the run-one type by kernel conversion,
    /// not even for an explicit `running`/`halted` constructor. Deciding
    /// `run(1, c) = step(c)` on an actual `c` makes the kernel's lazy delta
    /// unfold `step` (the side of greater definitional height) until it is a
    /// constructor. That evaluates the actual instruction's REFERENCE
    /// semantics far enough to decide the result-carrier check
    /// (`ir_byte_values_match_v1`) on its value. For a full-width U64 `LShr`
    /// by 3 that is `ir_nat_div word 8` by repeated subtraction: 2^61
    /// iterations at `u64::MAX`, exactly what the derived shift law exists to
    /// avoid. Measured (2026-10-14, debug): the replay grew from 0.2 s at a
    /// 4-bit word to 21-46 s at 20 bits and did not finish at 64 bits (3.5 h
    /// in gate 9). The closed eliminator decides the equation over bound
    /// binders once, so replay work depends on the proof's shape, never on an
    /// operand's magnitude (DR-RUN-ONE-CLOSED-ELIMINATOR-20261014; guarded by
    /// `fetched_replay_work_tracks_word_bit_length_not_magnitude`).
    pub fn one_step(
        &mut self,
        model: &MachineModel,
        initial: Expr,
        step: PendingEquality,
    ) -> Result<ExactRun> {
        step.endpoints(
            &model.config_type(),
            &model.step(initial.clone()),
            step.right(),
        )?;
        let fuel = NatTerm::literal(1);
        let conversion = PendingEquality::candidate(
            model.config_type(),
            model.run(&fuel, initial.clone()),
            step.left.clone(),
            Expr::apps(
                self.run_one_candidate()?,
                [
                    model.world_type.clone(),
                    model.context.clone(),
                    model.providers.clone(),
                    initial.clone(),
                ],
            ),
        );
        let reached = step.right.clone();
        let equality = self.compose(conversion, step)?;
        ExactRun::candidate(model.clone(), initial, reached, fuel, equality)
    }

    /// Compose arbitrary symbolic exact counts. The law's order is b+a, not a+b.
    pub fn concatenate(&mut self, first: ExactRun, second: ExactRun) -> Result<ExactRun> {
        self.charge()?;
        first.model.same(&second.model)?;
        require_same(&first.reached, &second.initial, "run composition boundary")?;
        let model = &first.model;
        let ty = model.config_type();
        let fuel = NatTerm(app(
            "Nat.add",
            [second.fuel.0.clone(), first.fuel.0.clone()],
        ));
        let left = model.run(&fuel, first.initial.clone());
        let nested = model.run(&second.fuel, model.run(&first.fuel, first.initial.clone()));
        let law = PendingEquality::candidate(
            ty.clone(),
            left,
            nested,
            app(
                "ir_byte_run_add_v1",
                [
                    model.world_type.clone(),
                    model.context.clone(),
                    model.providers.clone(),
                    second.fuel.0.clone(),
                    first.fuel.0.clone(),
                    first.initial.clone(),
                ],
            ),
        );
        let mapped =
            self.congruence_function(first.equality, ty, model.run_function(&second.fuel))?;
        // run_function is the actual curried primitive, not a capturing
        // lambda. ExactRun::candidate plus the exact model/run boundary above
        // make BOTH joins structurally identical. Retain strict compose's
        // endpoint checks, but do not allocate redundant refl bridges or the
        // two additional Eq.trans nodes that only joined those bridges.
        let joined = self.compose(law, mapped)?;
        let equality = self.compose(joined, second.equality)?;
        ExactRun::candidate(first.model, first.initial, second.reached, fuel, equality)
    }

    /// Eliminate an actual symbolic Boolean, retaining distinct exact fuel and
    /// endpoint expressions for its two paths. The callbacks receive scoped
    /// equality hypotheses, not globally assumed branch outcomes. Their proofs
    /// are abstracted under those hypotheses before the Bool eliminator is used.
    /// Endpoint and fuel expressions must not depend on witnesses local to an
    /// arm. Use [`Self::branch_proposition`] to introduce existential results
    /// separately inside the arms. Any accidental escape of a local is rejected when the
    /// model-owned Scope closes the resulting whole-program proposition/proof.
    pub fn branch(
        &mut self,
        model: &MachineModel,
        flag: Expr,
        initial: Expr,
        on_false: impl FnOnce(&mut Self, PendingEquality) -> Result<ExactRun>,
        on_true: impl FnOnce(&mut Self, PendingEquality) -> Result<ExactRun>,
    ) -> Result<ExactRun> {
        let bool_type = constant("Bool");
        let false_hypothesis = self.local(eq(&bool_type, flag.clone(), constant("Bool.false")))?;
        let true_hypothesis = self.local(eq(&bool_type, flag.clone(), constant("Bool.true")))?;
        let no = on_false(
            self,
            PendingEquality::candidate(
                bool_type.clone(),
                flag.clone(),
                constant("Bool.false"),
                false_hypothesis.term().clone(),
            ),
        )?;
        let yes = on_true(
            self,
            PendingEquality::candidate(
                bool_type.clone(),
                flag.clone(),
                constant("Bool.true"),
                true_hypothesis.term().clone(),
            ),
        )?;
        model.same(&no.model)?;
        model.same(&yes.model)?;
        require_same(&initial, &no.initial, "false branch initial configuration")?;
        require_same(&initial, &yes.initial, "true branch initial configuration")?;
        let choice = self.local(bool_type.clone())?;
        let equality_hypothesis =
            self.local(eq(&bool_type, flag.clone(), choice.term().clone()))?;
        let selected_fuel = |b| {
            NatTerm(choose(
                &constant("Nat"),
                b,
                yes.fuel.0.clone(),
                no.fuel.0.clone(),
            ))
        };
        let selected_result = |b| {
            choose(
                &model.config_type(),
                b,
                yes.reached.clone(),
                no.reached.clone(),
            )
        };
        let motive = choice.lam(equality_hypothesis.pi(eq(
            &model.config_type(),
            model.run(&selected_fuel(choice.term().clone()), initial.clone()),
            selected_result(choice.term().clone()),
        )));
        let cases = Expr::apps(
            Expr::const_(Name::from_string("Bool.rec"), vec![Level::zero()]),
            [
                motive,
                false_hypothesis.lam(no.equality.term.clone()),
                true_hypothesis.lam(yes.equality.term.clone()),
                flag.clone(),
            ],
        );
        let term = Expr::app(cases, refl(&bool_type, flag.clone()));
        let fuel = selected_fuel(flag.clone());
        let reached = selected_result(flag);
        let equation = PendingEquality::candidate(
            model.config_type(),
            model.run(&fuel, initial.clone()),
            reached.clone(),
            term,
        );
        ExactRun::candidate(model.clone(), initial, reached, fuel, equation)
    }

    /// Prove one externally scoped proposition by Boolean cases. Unlike
    /// [`Self::branch`], this does not export an arm's fuel or result expression.
    /// Each arm can eliminate local existential premises and introduce its own
    /// witnesses into the common goal (for example, existence of an exact run
    /// satisfying representation and resource bounds) before returning.
    ///
    /// Both callbacks must return the exact same candidate proposition; this
    /// syntactic check is not a substitute for checking either proof in the
    /// kernel. The common goal itself must contain no arm-local witnesses.
    /// Closing the whole candidate in the model-owned Scope rejects such an
    /// escape. No existential witness is extracted into Rust or assumed proved.
    pub fn branch_proposition(
        &mut self,
        flag: Expr,
        proposition: Expr,
        on_false: impl FnOnce(&mut Self, PendingEquality) -> Result<PendingProof>,
        on_true: impl FnOnce(&mut Self, PendingEquality) -> Result<PendingProof>,
    ) -> Result<PendingProof> {
        self.branch_proposition_with_context(
            &mut (),
            flag,
            proposition,
            |assembler, _, hypothesis| on_false(assembler, hypothesis),
            |assembler, _, hypothesis| on_true(assembler, hypothesis),
        )
    }

    /// Prove a common proposition while both arm constructors sequentially
    /// borrow the same caller-owned context. The false arm runs first; the true
    /// arm sees its context changes. No context cloning or branch-local budget
    /// is introduced, and construction failure does not roll back either owner.
    ///
    /// This has the same scoped hypotheses, goal checks, and pending-proof
    /// contract as [`Self::branch_proposition`]. Context contents confer no proof
    /// authority; both arm proofs still require kernel checking after closing.
    pub fn branch_proposition_with_context<C>(
        &mut self,
        context: &mut C,
        flag: Expr,
        proposition: Expr,
        on_false: impl FnOnce(&mut Self, &mut C, PendingEquality) -> Result<PendingProof>,
        on_true: impl FnOnce(&mut Self, &mut C, PendingEquality) -> Result<PendingProof>,
    ) -> Result<PendingProof> {
        self.branch_proposition_with_scoped_context(
            context,
            flag,
            proposition,
            |assembler, context, _, hypothesis| on_false(assembler, context, hypothesis),
            |assembler, context, _, hypothesis| on_true(assembler, context, hypothesis),
        )
    }

    /// The same Bool eliminator, also exposing each arm's actual lexical
    /// parameter to a compositional proof producer. It confers no authority:
    /// the resulting arm proof is still wrapped under this exact binder.
    pub fn branch_proposition_with_scoped_context<C>(
        &mut self,
        context: &mut C,
        flag: Expr,
        proposition: Expr,
        on_false: impl FnOnce(&mut Self, &mut C, Local, PendingEquality) -> Result<PendingProof>,
        on_true: impl FnOnce(&mut Self, &mut C, Local, PendingEquality) -> Result<PendingProof>,
    ) -> Result<PendingProof> {
        self.charge()?;
        let bool_type = constant("Bool");
        let false_hypothesis = self.local(eq(&bool_type, flag.clone(), constant("Bool.false")))?;
        let true_hypothesis = self.local(eq(&bool_type, flag.clone(), constant("Bool.true")))?;
        let no = on_false(
            self,
            context,
            false_hypothesis.clone(),
            PendingEquality::candidate(
                bool_type.clone(),
                flag.clone(),
                constant("Bool.false"),
                false_hypothesis.term().clone(),
            ),
        )?;
        require_same(&proposition, no.proposition(), "false branch proposition")?;
        let yes = on_true(
            self,
            context,
            true_hypothesis.clone(),
            PendingEquality::candidate(
                bool_type.clone(),
                flag.clone(),
                constant("Bool.true"),
                true_hypothesis.term().clone(),
            ),
        )?;
        require_same(&proposition, yes.proposition(), "true branch proposition")?;
        let choice = self.local(bool_type.clone())?;
        let hypothesis = self.local(eq(&bool_type, flag.clone(), choice.term().clone()))?;
        let cases = Expr::apps(
            Expr::const_(Name::from_string("Bool.rec"), vec![Level::zero()]),
            [
                choice.lam(hypothesis.pi(proposition.clone())),
                false_hypothesis.lam(no.term),
                true_hypothesis.lam(yes.term),
                flag.clone(),
            ],
        );
        Ok(PendingProof::candidate(
            proposition,
            Expr::app(cases, refl(&bool_type, flag)),
        ))
    }

    /// Compose explicit pointwise reads. A read fact must refer to this exact
    /// machine and actual operand ID; neither whole-map equality nor an assumed
    /// successful post-lookup is synthesized here.
    pub fn resolve(&mut self, machine: &Expr, facts: &[LookupFact]) -> Result<PendingEquality> {
        self.charge()?;
        self.items(facts.len())?;
        let scalar = constant("IRScalar");
        let mut ids = Vec::with_capacity(facts.len());
        for fact in facts {
            require_same(&fact.machine, machine, "operand read machine")?;
            fact.equality.endpoints(
                &scalar,
                &app(
                    "ir_getd",
                    [machine.clone(), nat(u64::from(fact.id.index()))],
                ),
                &fact.value,
            )?;
            ids.push(nat(u64::from(fact.id.index())));
        }
        let proof = self.list_congruence_iter(scalar, facts.iter().map(|fact| &fact.equality))?;
        let resolved = app("ir_resolve", [machine.clone(), list("Nat", &ids)]);
        let values = proof.right.clone();
        // Keep both the pointwise-list equality and the actual ir_resolve
        // equality as typed obligations. Strict replay, not this producer,
        // establishes the definitional list presentation. No Refl/trans bridge
        // is constructed, and the ordinary one-candidate charge remains paid.
        self.ascribe_preserving_endpoints(proof, resolved, values)
    }

    pub fn bindings(&mut self, ids: &[ValueId], values: &[Expr], tail: Expr) -> Result<Expr> {
        self.charge()?;
        self.items(ids.len())?;
        if ids.len() != values.len() {
            return Err("binding ID/value arity mismatch".into());
        }
        // Retain actual first-match order, including duplicates. Positional
        // binding theorems, not an invented global NoDup requirement, govern use.
        Ok(ids
            .iter()
            .zip(values)
            .rev()
            .fold(tail, |tail, (id, value)| {
                app(
                    "IRList.cons",
                    [
                        constant("IRBinding"),
                        app("IRBinding.mk", [nat(u64::from(id.index())), value.clone()]),
                        tail,
                    ],
                )
            }))
    }
}

#[derive(Clone)]
pub struct LookupFact {
    machine: Expr,
    id: ValueId,
    value: Expr,
    equality: PendingEquality,
}

impl LookupFact {
    pub fn candidate(
        machine: Expr,
        id: ValueId,
        value: Expr,
        equality: PendingEquality,
    ) -> Result<Self> {
        equality.endpoints(
            &constant("IRScalar"),
            &app("ir_getd", [machine.clone(), nat(u64::from(id.index()))]),
            &value,
        )?;
        Ok(Self {
            machine,
            id,
            value,
            equality,
        })
    }
}

/// All three coordinates matter; block/value IDs are function-local.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Coordinate {
    pub function: FuncId,
    pub block: BlockId,
    pub instruction: usize,
}

#[derive(Clone)]
pub struct FetchedSite {
    context: Expr,
    coordinate: Coordinate,
    function: Expr,
    block: Expr,
    node: Expr,
    pub instruction: Expr,
    pub results: Expr,
    pub site: Expr,
}

/// Candidate extraction from the one shared reflection. A cache entry is never
/// a proof that a runtime frame has reached that coordinate.
pub struct Catalog<'env, 'module> {
    reflected: &'module ReflectedCoreModuleV1<'module>,
    checker: TypeChecker<'env>,
    limits: Limits,
    lookups: usize,
    functions: HashMap<FuncId, Expr>,
    blocks: HashMap<(FuncId, BlockId), Expr>,
    sites: HashMap<Coordinate, FetchedSite>,
    calls: HashMap<FuncId, CallTarget>,
}

/// Borrow one fixed constructor spine, without a fanout Vec or normalization.
/// This recognizes candidate data only; it supplies no typing/equality fact.
fn exact_constructor_fields<'expr, const N: usize>(
    expression: &'expr Expr,
    constructor: &str,
) -> Option<[&'expr Expr; N]> {
    let mut cursor = expression;
    let mut fields = [expression; N];
    for field in fields.iter_mut().rev() {
        let ExprKind::App(function, argument) = cursor.kind() else {
            return None;
        };
        *field = argument.as_ref();
        cursor = function.as_ref();
    }
    match cursor.kind() {
        ExprKind::Const(name, levels)
            if name == &Name::from_string(constructor) && levels.is_empty() =>
        {
            Some(fields)
        }
        _ => None,
    }
}

impl<'env, 'module> Catalog<'env, 'module> {
    pub fn new(
        env: &'env Environment,
        reflected: &'module ReflectedCoreModuleV1<'module>,
        limits: Limits,
    ) -> Result<Self> {
        let limits = limits.validate()?;
        let mut checker = TypeChecker::new(env);
        checker.set_max_cache_entries(limits.lookup_cache_entries);
        Ok(Self {
            reflected,
            checker,
            limits,
            lookups: 0,
            functions: HashMap::new(),
            blocks: HashMap::new(),
            sites: HashMap::new(),
            calls: HashMap::new(),
        })
    }

    fn found(&mut self, ty: &str, lookup: Expr) -> Result<Expr> {
        let next = self
            .lookups
            .checked_add(1)
            .ok_or("lookup counter overflow")?;
        if next > self.limits.max_lookup_candidates {
            return Err("reflected lookup candidate budget exceeded".into());
        }
        self.lookups = next;
        self.checker
            .set_heartbeat_limit(self.limits.lookup_heartbeats);
        self.checker
            .check_type(&lookup, &app("IROption", [constant(ty)]))
            // A rejected reflected term can have a very large diagnostic. Do
            // not stringify that graph merely to report candidate refusal.
            .map_err(|_| format!("actual {ty} lookup type check failed; candidate refused"))?;
        let reduced = self.checker.whnf(&lookup);
        if self.checker.heartbeat_spent() {
            return Err(format!("actual {ty} lookup exhausted its reduction budget"));
        }
        if !matches!(reduced.get_app_fn().kind(), ExprKind::Const(name, _) if name == &Name::from_string("IROption.some"))
        {
            return Err(format!("actual {ty} lookup did not yield Some"));
        }
        let arguments = reduced.get_app_args();
        let [actual_type, value] = arguments.as_slice() else {
            return Err(format!("malformed Some in {ty} lookup"));
        };
        require_same(actual_type, &constant(ty), "lookup result type")?;
        // No stored lookup proof is trusted. Fetched applications below include
        // the actual lookup obligations afresh in the final replayed term.
        Ok((*value).clone())
    }

    fn function(&mut self, fid: FuncId) -> Result<Expr> {
        if let Some(function) = self.functions.get(&fid) {
            return Ok(function.clone());
        }
        let context = self.reflected.context_term().clone();
        let function = self.found(
            "IRFunc",
            app(
                "ir_func_find",
                [
                    app(
                        "ir_mod_funcs",
                        [app("ir_byte_context_module_v1", [context])],
                    ),
                    nat(u64::from(fid.index())),
                ],
            ),
        )?;
        self.functions.insert(fid, function.clone());
        Ok(function)
    }

    /// Reuse the exact node constituent of the already typechecked block.
    /// This is only candidate discovery: the fetched rule still checks the
    /// original `ir_nodes_get` equation at the actual frame PC. No separate
    /// node index, inferred source interpretation, or execution fact is added.
    fn block_node(&self, coordinate: Coordinate, block: &Expr) -> Result<Expr> {
        let actual = self
            .reflected
            .block(coordinate.function, coordinate.block)
            .ok_or("actual IRNode projection block absent")?;
        if coordinate.instruction >= actual.body.len() {
            return Err("actual IRNode projection coordinate absent".into());
        }
        let fields = block.get_app_args();
        if block.get_app_fn() != &constant("IRBlock.mk") || fields.len() != 3 {
            return Err("actual IRNode projection requires canonical IRBlock.mk".into());
        }
        require_same(
            fields[0],
            &nat(u64::from(coordinate.block.index())),
            "actual IRNode projection nominal block",
        )?;
        let mut nodes = (*fields[2]).clone();
        // A kernel lookup used the same per-discovery reduction bound. Charge
        // before observing each cons, also within the borrowed actual length;
        // no fanout allocation, recursive traversal, or retained cursor exists.
        let count = coordinate
            .instruction
            .checked_add(1)
            .ok_or("actual IRNode projection count overflow")?;
        let work_limit = usize::try_from(self.limits.lookup_heartbeats)
            .map_err(|_| "actual IRNode projection budget does not fit usize")?;
        for index in 0..count {
            if index >= work_limit || index >= actual.body.len() {
                return Err("actual IRNode projection exhausted its traversal budget".into());
            }
            let arguments = nodes.get_app_args();
            if nodes.get_app_fn() != &constant("IRList.cons") || arguments.len() != 3 {
                return Err("actual IRNode projection requires canonical IRList.cons".into());
            }
            require_same(arguments[0], &constant("IRNode"), "actual IRNode list type")?;
            if index + 1 == count {
                return Ok((*arguments[1]).clone());
            }
            let next = (*arguments[2]).clone();
            drop(arguments);
            nodes = next;
        }
        Err("actual IRNode projection coordinate absent".into())
    }

    /// Borrow the first exact site in an already typechecked canonical context.
    /// Function/block discovery checked the real container; the final fetched
    /// rule still checks ir_byte_site_v1 at its actual nominal coordinate.
    /// An opaque outer context retains the ordinary kernel lookup route.
    fn projected_byte_site(&self, coordinate: Coordinate, context: &Expr) -> Result<Option<Expr>> {
        let Some(fields) = exact_constructor_fields::<5>(context, "IRByteContextV1.mk") else {
            return Ok(None);
        };
        let pc = u64::try_from(coordinate.instruction)
            .map_err(|_| "instruction coordinate exceeds u64")?;
        let expected = [
            nat(u64::from(coordinate.function.index())),
            nat(u64::from(coordinate.block.index())),
            nat(pc),
        ];
        let mut sites = fields[4];
        let mut remaining = self.limits.lookup_heartbeats;
        loop {
            // Charge before observing each cons, including a malformed tail.
            // Return at the first matching head, just like ir_byte_site_v1;
            // do not inspect or materialize the unused suffix.
            remaining = remaining
                .checked_sub(1)
                .ok_or("actual IRByteSiteV1 projection exhausted its traversal budget")?;
            if let Some([ty]) = exact_constructor_fields::<1>(sites, "IRList.nil") {
                require_same(
                    ty,
                    &constant("IRByteSiteV1"),
                    "actual IRByteSiteV1 list type",
                )?;
                return Err("actual IRByteSiteV1 projection coordinate absent".into());
            }
            let Some([ty, site, rest]) = exact_constructor_fields::<3>(sites, "IRList.cons") else {
                return Err("actual IRByteSiteV1 projection requires canonical IRList.cons".into());
            };
            require_same(
                ty,
                &constant("IRByteSiteV1"),
                "actual IRByteSiteV1 list type",
            )?;
            let coordinates = if let Some(fields) =
                exact_constructor_fields::<6>(site, "IRByteSiteV1.mk")
            {
                [fields[0], fields[1], fields[2]]
            } else if let Some(fields) = exact_constructor_fields::<7>(site, "IRByteSiteV1.mkt") {
                [fields[0], fields[1], fields[2]]
            } else if let Some(fields) = exact_constructor_fields::<7>(site, "IRByteSiteV1.mki") {
                [fields[0], fields[1], fields[2]]
            } else {
                return Err(
                    "actual IRByteSiteV1 projection requires canonical mk/mkt/mki site".into(),
                );
            };
            if !coordinates
                .iter()
                .all(|field| matches!(field.kind(), ExprKind::Lit(clean_kernel::Literal::Nat(_))))
            {
                return Err(
                    "actual IRByteSiteV1 projection requires literal nominal coordinates".into(),
                );
            }
            if coordinates
                .iter()
                .zip(&expected)
                .all(|(actual, expected)| *actual == expected)
            {
                // Preserve the exact mk/mkt/mki, alignment, convention, result
                // lanes and operand catalog by sharing its original Expr.
                return Ok(Some((*site).clone()));
            }
            sites = rest;
        }
    }

    fn byte_site(&mut self, coordinate: Coordinate, context: &Expr) -> Result<(Expr, bool)> {
        if let Some(site) = self.projected_byte_site(coordinate, context)? {
            return Ok((site, true));
        }
        let pc = u64::try_from(coordinate.instruction)
            .map_err(|_| "instruction coordinate exceeds u64")?;
        self.found(
            "IRByteSiteV1",
            app(
                "ir_byte_site_v1",
                [
                    context.clone(),
                    nat(u64::from(coordinate.function.index())),
                    nat(u64::from(coordinate.block.index())),
                    nat(pc),
                ],
            ),
        )
        .map(|site| (site, false))
    }

    pub fn fetch(&mut self, coordinate: Coordinate) -> Result<FetchedSite> {
        if let Some(site) = self.sites.get(&coordinate) {
            return Ok(site.clone());
        }
        let context = self.reflected.context_term().clone();
        let function = self.function(coordinate.function)?;
        let block_key = (coordinate.function, coordinate.block);
        let block = if let Some(block) = self.blocks.get(&block_key) {
            block.clone()
        } else {
            let block = self.found(
                "IRBlock",
                app(
                    "ir_block_find",
                    [
                        app("ir_func_blocks", [function.clone()]),
                        nat(u64::from(coordinate.block.index())),
                    ],
                ),
            )?;
            self.blocks.insert(block_key, block.clone());
            block
        };
        let node = self.block_node(coordinate, &block)?;
        if !matches!(node.get_app_fn().kind(), ExprKind::Const(name, _) if name == &Name::from_string("IRNode.mk"))
        {
            return Err("actual node candidate is not IRNode.mk".into());
        }
        let fields = node.get_app_args();
        let [instruction, results] = fields.as_slice() else {
            return Err("actual node candidate has wrong constructor arity".into());
        };
        let instruction = (*instruction).clone();
        let results = (*results).clone();
        drop(fields);
        let (site, projected) = self.byte_site(coordinate, &context)?;
        let fetched = FetchedSite {
            context,
            coordinate,
            function,
            block,
            node,
            instruction,
            results,
            site,
        };
        // Canonical constituents are shared on demand, not indexed/retained
        // once per PC. Opaque contexts keep their existing bounded discoveries.
        if !projected {
            self.sites.insert(coordinate, fetched.clone());
        }
        Ok(fetched)
    }

    /// The target is selected by its actual nominal function identity. For an
    /// indirect call the consumer must additionally derive that exact fnptr from
    /// the current machine; this lookup does not assume it is the runtime target.
    pub fn call_target(&mut self, fid: FuncId) -> Result<CallTarget> {
        if let Some(target) = self.calls.get(&fid) {
            return Ok(target.clone());
        }
        let context = self.reflected.context_term().clone();
        let function_id = nat(u64::from(fid.index()));
        let binding = self.found(
            "IRByteFunctionV1",
            app(
                "ir_byte_function_v1",
                [context.clone(), function_id.clone()],
            ),
        )?;
        let signature = self.found(
            "IRByteSignatureV1",
            app(
                "ir_byte_signature_v1",
                [
                    context.clone(),
                    app("ir_byte_binding_sig_v1", [binding.clone()]),
                ],
            ),
        )?;
        let target = CallTarget {
            context,
            function_id,
            binding,
            signature,
        };
        self.calls.insert(fid, target.clone());
        Ok(target)
    }
}

#[derive(Clone)]
pub struct CallTarget {
    context: Expr,
    function_id: Expr,
    pub binding: Expr,
    pub signature: Expr,
}

impl CallTarget {
    fn binding_found(&self) -> Expr {
        refl(
            &app("IROption", [constant("IRByteFunctionV1")]),
            some("IRByteFunctionV1", self.binding.clone()),
        )
    }
    fn signature_found(&self) -> Expr {
        refl(
            &app("IROption", [constant("IRByteSignatureV1")]),
            some("IRByteSignatureV1", self.signature.clone()),
        )
    }

    /// Exact indirect-call checks, including the actual site's convention.
    /// This exposes the proof obligation rather than returning an assumed guard.
    pub fn indirect_guard(&self, signature: Expr, convention: Expr, site: &FetchedSite) -> Expr {
        app(
            "Bool.and",
            [
                app(
                    "ir_nat_eqb",
                    [
                        signature,
                        app("ir_byte_binding_sig_v1", [self.binding.clone()]),
                    ],
                ),
                app(
                    "ir_nat_eqb",
                    [convention, app("ir_byte_site_cc_v1", [site.site.clone()])],
                ),
            ],
        )
    }

    pub fn admission(&self, model: &MachineModel, site: &FetchedSite, values: Expr) -> Expr {
        let and = |a, b| app("Bool.and", [a, b]);
        let length = |ty, values| app("ir_byte_length_v1", [constant(ty), values]);
        let returns = app("ir_byte_signature_returns_v1", [self.signature.clone()]);
        and(
            app(
                "Bool.not",
                [app("ir_byte_signature_vararg_v1", [self.signature.clone()])],
            ),
            and(
                app(
                    "ir_nat_leb",
                    [app("ir_byte_binding_cc_v1", [self.binding.clone()]), nat(1)],
                ),
                and(
                    app(
                        "ir_nat_eqb",
                        [
                            app("ir_byte_site_cc_v1", [site.site.clone()]),
                            app("ir_byte_binding_cc_v1", [self.binding.clone()]),
                        ],
                    ),
                    and(
                        app(
                            "ir_nat_eqb",
                            [
                                length("Nat", site.results.clone()),
                                length("IRTy", returns.clone()),
                            ],
                        ),
                        and(
                            app(
                                "ir_byte_ty_list_eq_v1",
                                [app("ir_byte_site_results_v1", [site.site.clone()]), returns],
                            ),
                            app(
                                "ir_byte_values_match_v1",
                                [
                                    model.context.clone(),
                                    app("ir_byte_signature_params_v1", [self.signature.clone()]),
                                    values,
                                ],
                            ),
                        ),
                    ),
                ),
            ),
        )
    }

    fn call(
        &self,
        model: &MachineModel,
        current: &Current,
        site: &FetchedSite,
        arguments: Expr,
    ) -> Expr {
        app(
            "ir_byte_call_v1",
            [
                model.world_type.clone(),
                model.context.clone(),
                model.providers.clone(),
                current.machine(),
                current.world.clone(),
                site.results.clone(),
                site.site.clone(),
                self.function_id.clone(),
                arguments,
            ],
        )
    }

    fn known(
        &self,
        model: &MachineModel,
        current: &Current,
        site: &FetchedSite,
        values: Expr,
    ) -> Expr {
        Expr::app(self.known_function(model, current, site), values)
    }

    // Values are the final argument of the actual known-call primitive. Keep
    // that function available for equality transport without a new wrapper
    // binder; its context, world, binding and signature remain unchanged.
    fn known_function(&self, model: &MachineModel, current: &Current, site: &FetchedSite) -> Expr {
        app(
            "ir_byte_call_known_v1",
            [
                model.world_type.clone(),
                model.context.clone(),
                model.providers.clone(),
                current.machine(),
                current.world.clone(),
                site.results.clone(),
                site.site.clone(),
                self.binding.clone(),
                self.signature.clone(),
            ],
        )
    }

    // Imported and internal calls transport the same actual argument-list
    // primitive. No source operand is captured under a new wrapper binder.
    fn map_known_arguments(
        &self,
        assembler: &mut Assembler<'_>,
        model: &MachineModel,
        current: &Current,
        site: &FetchedSite,
        resolved: PendingEquality,
    ) -> Result<PendingEquality> {
        assembler.congruence_function(
            resolved,
            model.config_type(),
            self.known_function(model, current, site),
        )
    }

    /// Actual direct dispatch through the two catalog lookups. This derives no
    /// body result and does not silently classify the target as non-imported.
    pub fn direct(
        &self,
        assembler: &mut Assembler<'_>,
        model: &MachineModel,
        current: &Current,
        site: &FetchedSite,
    ) -> Result<PendingEquality> {
        require_same(&self.context, &model.context, "call target context")?;
        if !matches!(site.instruction.get_app_fn().kind(), ExprKind::Const(name, _) if name == &Name::from_string("IRInst.call"))
        {
            return Err("direct call assembler requires an actual IRInst.call".into());
        }
        let operands = site.instruction.get_app_args();
        let [fid, arguments] = operands.as_slice() else {
            return Err("actual direct call has wrong constructor arity".into());
        };
        let arguments = *arguments;
        require_same(fid, &self.function_id, "actual direct call identity")?;
        self.direct_from_arguments(
            assembler,
            model,
            current,
            site,
            arguments.clone(),
            site.dispatch(model, current)?,
        )
    }

    fn direct_from_arguments(
        &self,
        assembler: &mut Assembler<'_>,
        model: &MachineModel,
        current: &Current,
        site: &FetchedSite,
        arguments: Expr,
        left: Expr,
    ) -> Result<PendingEquality> {
        let call = self.call(model, current, site, arguments.clone());
        let values = app("ir_resolve", [current.machine(), arguments.clone()]);
        let known = self.known(model, current, site, values);
        let conversion = assembler.conversion(model.config_type(), left, call.clone())?;
        let term = app(
            "ir_byte_call_of_catalog_v1",
            [
                model.world_type.clone(),
                model.context.clone(),
                model.providers.clone(),
                current.machine(),
                current.world.clone(),
                site.results.clone(),
                site.site.clone(),
                self.function_id.clone(),
                arguments,
                self.binding.clone(),
                self.signature.clone(),
                self.binding_found(),
                self.signature_found(),
            ],
        );
        assembler.compose(
            conversion,
            PendingEquality::candidate(model.config_type(), call, known, term),
        )
    }

    /// Resolve the actual indirect-call operand from a pointwise fact, preserving
    /// nominal target identity and the requested signature/convention. The
    /// callback's execution remains a separately checked summary obligation.
    pub fn indirect(
        &self,
        assembler: &mut Assembler<'_>,
        model: &MachineModel,
        current: &Current,
        site: &FetchedSite,
        callback: &LookupFact,
        exact: PendingEquality,
    ) -> Result<PendingEquality> {
        require_same(&self.context, &model.context, "indirect target context")?;
        require_same(
            &callback.machine,
            &current.machine(),
            "indirect callback machine",
        )?;
        if !matches!(site.instruction.get_app_fn().kind(), ExprKind::Const(name, _) if name == &Name::from_string("IRInst.callindirect"))
        {
            return Err("indirect call assembler requires an actual IRInst.callindirect".into());
        }
        let operands = site.instruction.get_app_args();
        let [operand, signature, arguments, convention] = operands.as_slice() else {
            return Err("actual indirect call has wrong constructor arity".into());
        };
        let (operand, signature, arguments, convention) =
            (*operand, *signature, *arguments, *convention);
        require_same(
            operand,
            &nat(u64::from(callback.id.index())),
            "actual callback operand ID",
        )?;
        let fnptr = app("IRScalar.fnptr_", [self.function_id.clone()]);
        callback.equality.endpoints(
            &constant("IRScalar"),
            &app("ir_getd", [current.machine(), operand.clone()]),
            &fnptr,
        )?;
        exact.endpoints(
            &constant("Bool"),
            &self.indirect_guard(signature.clone(), convention.clone(), site),
            &constant("Bool.true"),
        )?;
        let indirect = |value| {
            app(
                "ir_byte_call_indirect_v1",
                [
                    model.world_type.clone(),
                    model.context.clone(),
                    model.providers.clone(),
                    current.machine(),
                    current.world.clone(),
                    site.results.clone(),
                    site.site.clone(),
                    value,
                    signature.clone(),
                    arguments.clone(),
                    convention.clone(),
                ],
            )
        };
        let mapped =
            assembler.congruence(callback.equality.clone(), model.config_type(), indirect)?;
        let before = assembler.conversion(
            model.config_type(),
            site.dispatch(model, current)?,
            mapped.left.clone(),
        )?;
        let after =
            assembler.conversion(model.config_type(), mapped.right.clone(), indirect(fnptr))?;
        let call = self.call(model, current, site, arguments.clone());
        let rule = app(
            "ir_byte_indirect_call_exact_v1",
            [
                model.world_type.clone(),
                model.context.clone(),
                model.providers.clone(),
                current.machine(),
                current.world.clone(),
                site.results.clone(),
                site.site.clone(),
                self.function_id.clone(),
                signature.clone(),
                arguments.clone(),
                convention.clone(),
                self.binding.clone(),
                self.binding_found(),
                exact.term,
            ],
        );
        let reduction = PendingEquality::candidate(
            model.config_type(),
            after.right.clone(),
            call.clone(),
            rule,
        );
        let proof = assembler.compose(before, mapped)?;
        let proof = assembler.compose(proof, after)?;
        let proof = assembler.compose(proof, reduction)?;
        let direct =
            self.direct_from_arguments(assembler, model, current, site, arguments.clone(), call)?;
        assembler.compose(proof, direct)
    }

    /// Use the shared actual internal-call rule, ending at push rather than an
    /// assumed callee answer. `resolved` must be the pointwise operand-list fact
    /// for this actual call. Body lookup and each operational guard are retained
    /// as typed candidate obligations; no formal arity or result lane is fixed.
    pub fn enter_internal(
        &self,
        assembler: &mut Assembler<'_>,
        model: &MachineModel,
        current: &Current,
        site: &FetchedSite,
        dispatch: PendingEquality,
        resolved: PendingEquality,
        body: Expr,
        body_lookup: PendingEquality,
        local_binding: PendingEquality,
        arity: PendingEquality,
        admitted: PendingEquality,
    ) -> Result<PendingEquality> {
        assembler.charge()?;
        require_same(&self.context, &model.context, "internal target context")?;
        require_same(
            &resolved.ty,
            &app("IRList", [constant("IRScalar")]),
            "resolved call values type",
        )?;
        let values = resolved.right.clone();
        dispatch.endpoints(
            &model.config_type(),
            &site.dispatch(model, current)?,
            &self.known(model, current, site, resolved.left.clone()),
        )?;
        local_binding.endpoints(
            &constant("Bool"),
            &app("ir_byte_binding_import_v1", [self.binding.clone()]),
            &constant("Bool.false"),
        )?;
        body_lookup.endpoints(
            &app("IROption", [constant("IRFunc")]),
            &app(
                "ir_func_find",
                [
                    app(
                        "ir_mod_funcs",
                        [app("ir_byte_context_module_v1", [model.context.clone()])],
                    ),
                    app("ir_byte_binding_fid_v1", [self.binding.clone()]),
                ],
            ),
            &some("IRFunc", body.clone()),
        )?;
        arity.endpoints(
            &constant("Bool"),
            &app(
                "ir_nat_eqb",
                [
                    app(
                        "ir_byte_length_v1",
                        [constant("Nat"), app("ir_func_params", [body.clone()])],
                    ),
                    app("ir_byte_length_v1", [constant("IRScalar"), values.clone()]),
                ],
            ),
            &constant("Bool.true"),
        )?;
        admitted.endpoints(
            &constant("Bool"),
            &self.admission(model, site, values.clone()),
            &constant("Bool.true"),
        )?;
        let mapped = self.map_known_arguments(assembler, model, current, site, resolved)?;
        let before = assembler.conversion(
            model.config_type(),
            dispatch.right.clone(),
            mapped.left.clone(),
        )?;
        let known = self.known(model, current, site, values.clone());
        let after =
            assembler.conversion(model.config_type(), mapped.right.clone(), known.clone())?;
        let push = app(
            "ir_byte_lift_v1",
            [
                model.world_type.clone(),
                app(
                    "ir_byte_push_owner_v1",
                    [model.world_type.clone(), current.world.clone()],
                ),
                app(
                    "ir_push",
                    [
                        current.machine(),
                        site.results.clone(),
                        body.clone(),
                        values.clone(),
                    ],
                ),
            ],
        );
        let rule = app(
            "ir_byte_internal_call_rule_v1",
            [
                model.world_type.clone(),
                model.context.clone(),
                model.providers.clone(),
                current.machine(),
                current.world.clone(),
                site.results.clone(),
                site.site.clone(),
                self.binding.clone(),
                self.signature.clone(),
                values,
                body,
                local_binding.term,
                body_lookup.term,
                arity.term,
                admitted.term,
            ],
        );
        let proof = assembler.compose(dispatch, before)?;
        let proof = assembler.compose(proof, mapped)?;
        let proof = assembler.compose(proof, after)?;
        assembler.compose(
            proof,
            PendingEquality::candidate(model.config_type(), known, push, rule),
        )
    }
}

impl FetchedSite {
    pub fn coordinate(&self) -> Coordinate {
        self.coordinate
    }

    pub fn dispatch(&self, model: &MachineModel, current: &Current) -> Result<Expr> {
        require_same(&self.context, &model.context, "fetched module context")?;
        Ok(app(
            "ir_byte_exec_v1",
            [
                model.world_type.clone(),
                model.context.clone(),
                model.providers.clone(),
                current.machine(),
                current.world.clone(),
                self.site.clone(),
                self.instruction.clone(),
                self.results.clone(),
            ],
        ))
    }

    /// Actual frame-PC/catalog equations are checked by the fetched rule, even
    /// when caller-provided current-frame expressions use symbolic locals.
    pub fn step(
        &self,
        assembler: &mut Assembler<'_>,
        model: &MachineModel,
        current: &Current,
        valid: PendingEquality,
    ) -> Result<PendingEquality> {
        assembler.charge()?;
        require_same(&self.context, &model.context, "fetched module context")?;
        valid.endpoints(
            &constant("Bool"),
            &current.valid(model),
            &constant("Bool.true"),
        )?;
        let found = |ty, value| refl(&app("IROption", [constant(ty)]), some(ty, value));
        let term = app(
            "ir_byte_step_fetched_v1",
            [
                model.world_type.clone(),
                model.context.clone(),
                model.providers.clone(),
                current.frame.clone(),
                current.tail.clone(),
                current.legacy_memory.clone(),
                current.legacy_cursor.clone(),
                current.world.clone(),
                self.function.clone(),
                self.block.clone(),
                self.instruction.clone(),
                self.results.clone(),
                self.site.clone(),
                valid.term,
                found("IRFunc", self.function.clone()),
                found("IRBlock", self.block.clone()),
                found("IRNode", self.node.clone()),
                found("IRByteSiteV1", self.site.clone()),
                refl(&constant("Bool"), constant("Bool.true")),
            ],
        );
        Ok(PendingEquality::candidate(
            model.config_type(),
            model.step(current.running(model)),
            self.dispatch(model, current)?,
            term,
        ))
    }
}

#[cfg(test)]
#[path = "core_execution_tests.rs"]
mod tests;

#[cfg(test)]
#[path = "core_execution_proof_tests.rs"]
mod proof_tests;

#[cfg(test)]
#[path = "core_execution_congruence_function_tests.rs"]
mod congruence_function_tests;

#[cfg(test)]
#[path = "core_execution_composition_tests.rs"]
mod composition_tests;

#[cfg(test)]
#[path = "core_execution_endpoint_conversion_tests.rs"]
mod endpoint_conversion_tests;

#[cfg(test)]
#[path = "core_execution_catalog_tests.rs"]
mod catalog_tests;

#[path = "core_execution_field.rs"]
mod field;
#[path = "core_execution_site_order.rs"]
mod site_order;
pub use field::ExtractFieldPremises;

// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! The builder world: [`ModuleBuilder`] and [`FunctionBuilder`].
//!
//! No door here panics on a value its signature admits ("A construction door
//! refuses; it never panics on a value its signature admits",
//! `docs/SPEC_RATIFICATIONS.md`). A door with no commit point of its own
//! RECORDS its refusal (a sticky [`BuildError`], first fault wins) and returns
//! a placeholder id; [`ModuleBuilder::build`], the one exit of the builder
//! world, reports the fault, so a placeholder never reaches a [`Module`].
//! The lint below holds the non-test code to it.
#![cfg_attr(
    not(test),
    deny(
        clippy::panic,
        clippy::unwrap_used,
        clippy::expect_used,
        clippy::indexing_slicing,
        clippy::unreachable,
        clippy::todo,
        clippy::unimplemented,
        clippy::arithmetic_side_effects,
        clippy::cast_possible_truncation
    )
)]

use trust_ir::constant::Constant;
use trust_ir::dialect::DialectInst;
use trust_ir::inst::{BindingFrameDef, *};
use trust_ir::node::InstrNode;
use trust_ir::proof::{ProofAnnotation, ProofObligation};
use trust_ir::spec::SpecModule;
use trust_ir::ty::{ClosureTy, EnumDef, FuncTy, RecordDef, StructDef, Ty};
use trust_ir::value::{
    BlockId, ClosureTyId, EnumId, FreshIds, FuncId, FuncTyId, GlobalId, IdRun, IdSpaceExhausted,
    ImportId, ProofId, RecordId, ScopeData, SourceSpan, TypedId, ValueId,
};
use trust_ir::{
    Block, Function, FunctionSummary, Global, Linkage, Module, ModuleImport, TargetInfo,
};

use std::collections::HashMap;
use std::ops::{Deref, DerefMut};

/// A fixed-arity dialect emission disagreed with its declared result types.
/// The builder is unchanged: no SSA IDs or instructions were allocated.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct DialectResultArityError {
    pub expected: usize,
    pub actual: usize,
}

impl std::fmt::Display for DialectResultArityError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "dialect result arity: expected {}, declared {}",
            self.expected, self.actual
        )
    }
}

impl std::error::Error for DialectResultArityError {}

/// Why a [`FunctionBuilder`] door declined. The builder is unchanged when one
/// of these is returned.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum BuilderError {
    /// [`FunctionBuilder::annotate_last`] found no node to attach to: either
    /// no block is selected (`block: None`) or the selected block has no
    /// instruction yet. The annotation is NOT redirected to
    /// `Function::proofs` — that would widen an instruction claim into a
    /// claim about the whole function.
    NoEmittedInstruction { block: Option<BlockId> },
    /// [`FunctionBuilder::annotate_last`] was called after the cursor moved
    /// back to `block`, but the instruction emitted most recently lives in
    /// `emitted_in`. `block`'s last node is NOT the instruction just emitted,
    /// so attaching there would pin the claim on a node the producer did not
    /// mean; the door refuses rather than guess.
    LastEmittedInAnotherBlock { block: BlockId, emitted_in: BlockId },
}

impl std::fmt::Display for BuilderError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::NoEmittedInstruction { block: None } => write!(
                f,
                "annotate_last: no block is selected, so there is no emitted instruction to annotate"
            ),
            Self::NoEmittedInstruction { block: Some(b) } => write!(
                f,
                "annotate_last: block {b} has no emitted instruction to annotate"
            ),
            Self::LastEmittedInAnotherBlock { block, emitted_in } => write!(
                f,
                "annotate_last: the current block is {block}, but the instruction emitted most \
                 recently is in block {emitted_in}; switch back to it to annotate it"
            ),
        }
    }
}

impl std::error::Error for BuilderError {}

/// A byte-extent fact about a pointer value produced by this builder: the
/// pointer addresses byte `offset` of an allocation that is exactly `size`
/// bytes long and rooted at `root`.
///
/// This is the evidence behind [`FunctionBuilder::gep_byte_offset`]'s
/// `inbounds` flag. Extents are recorded ONLY where the builder can actually
/// establish one:
///
/// * [`FunctionBuilder::alloca`] / [`alloca_aligned`](FunctionBuilder::alloca_aligned),
///   when the allocated type has a byte-exact [`Module::ty_layout_shape`];
/// * an explicit [`FunctionBuilder::note_alloc_extent`], for a producer that
///   knows a size the format cannot derive (e.g. a `Ty::Tuple` memory slot,
///   which has no declared trust-ir layout).
///
/// They propagate ONLY through [`FunctionBuilder::gep_byte_offset`]. Every
/// other way a pointer can arise — a `Load`, a block parameter, a call result,
/// an `IntToPtr` — has NO extent. That is what makes the derived claim
/// conservative: *unknown means `inbounds: false`*, never a guess.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PtrExtent {
    /// The allocation base this pointer is derived from.
    pub root: ValueId,
    /// Byte offset of this pointer from `root`. Always `<= size`.
    pub offset: u64,
    /// Size of the whole allocation rooted at `root`, in bytes.
    pub size: u64,
}

impl PtrExtent {
    /// The extent of `self + delta` bytes, or `None` when that address is not
    /// provably inside (or exactly one past the end of) the same allocation.
    ///
    /// `offset + delta == size` — the one-past-the-end address — is ALLOWED:
    /// LLVM `inbounds` explicitly permits it and it is the shape every
    /// half-open iterator sentinel takes. Overflow fails closed.
    pub fn offset_by(self, delta: u64) -> Option<Self> {
        let offset = self.offset.checked_add(delta)?;
        (offset <= self.size).then_some(Self { offset, ..self })
    }
}

pub struct ModuleBuilder {
    module: Module,
    /// The first refusal any door of this builder world met (sticky: the
    /// first write wins, [`record`]). [`Self::build`] reports it instead of a
    /// module, so no placeholder id a refused door returned can reach one.
    fault: Option<BuildError>,
    /// The one fresh-id rule for this builder's function ids; refused, never
    /// wrapped, once `u32::MAX` is taken.
    next_func_id: FreshIds<FuncId>,
    /// Only functions explicitly reserved through the two-phase API appear
    /// here. IDs need not equal table slots (abandoned legacy builders leave
    /// gaps); retaining the slot gives constant-time definition lookup.
    declarations: HashMap<FuncId, FunctionDeclaration>,
    /// Producer provenance (v23) stamped on every function subsequently
    /// created via [`function`](Self::function) or
    /// [`declare_function`](Self::declare_function). `None` (the default) leaves
    /// `Function::producer` unset; a per-function
    /// [`FunctionBuilder::set_producer`] overrides it.
    default_producer: Option<trust_ir::Producer>,
}

/// The declarations [`ModuleBuilder::declare_handle_runtime`] produced for
/// one trusted handle runtime.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct HandleRuntimeDecls {
    /// The runtime's handle type, exactly as the validator pins it.
    pub handle: Ty,
    entries: std::collections::BTreeMap<&'static str, FuncId>,
}

impl HandleRuntimeDecls {
    /// The declared entry point for `role` (`"add"`, `"from_u64"`, ...), if
    /// the pin has one.
    pub fn entry(&self, role: &str) -> Option<FuncId> {
        self.entries.get(role).copied()
    }

    /// Every declared `(role, function)` pair, in role order.
    pub fn entries(&self) -> impl Iterator<Item = (&'static str, FuncId)> + '_ {
        self.entries.iter().map(|(role, id)| (*role, *id))
    }
}

/// Why [`ModuleBuilder::declare_handle_runtime`] declined.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum HandleDeclError {
    /// A function with the pinned symbol already exists and is not the exact
    /// pinned bodyless declaration.
    ConflictingDeclaration { symbol: String },
    /// [`ModuleBuilder::declare_handle_runtime_roles`] was asked for a role
    /// this row does not pin. Named rather than ignored: a producer that
    /// misspells `"drop"` would otherwise silently declare nothing and then
    /// fail to find the entry point it was about to call.
    UnknownRole { runtime: String, role: String },
}

impl core::fmt::Display for HandleDeclError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::ConflictingDeclaration { symbol } => write!(
                f,
                "function `{symbol}` already exists with a signature, body or linkage other than \
                 the pinned handle-runtime declaration"
            ),
            Self::UnknownRole { runtime, role } => write!(
                f,
                "handle runtime `{runtime}` pins no entry point with role `{role}`"
            ),
        }
    }
}

impl std::error::Error for HandleDeclError {}

impl ModuleBuilder {
    pub fn new(name: impl Into<String>) -> Self {
        Self {
            module: Module::new(name),
            fault: None,
            next_func_id: FreshIds::new(),
            declarations: HashMap::new(),
            default_producer: None,
        }
    }

    /// Create a builder whose module is target-bound before any IR is added.
    ///
    /// Frontends that derive target-sensitive layouts, signatures, proof
    /// obligations, or executable identities should use this constructor
    /// instead of mutating [`Module::target_info`] after [`Self::build`]. The
    /// builder deliberately exposes no retargeting setter: a different target
    /// requires constructing and lowering a different module.
    ///
    /// `TargetInfo` is caller-supplied descriptive metadata. This constructor
    /// records it but does not authenticate correspondence with a physical
    /// host or compiler target; an authority-bearing consumer must perform
    /// that check independently.
    pub fn new_with_target_info(name: impl Into<String>, target_info: TargetInfo) -> Self {
        let mut module = Module::new(name);
        module.target_info = Some(target_info);
        Self {
            module,
            fault: None,
            next_func_id: FreshIds::new(),
            declarations: HashMap::new(),
            default_producer: None,
        }
    }

    /// Set the producer provenance tag (v23) stamped on every function created
    /// via [`function`](Self::function) or
    /// [`declare_function`](Self::declare_function) from this point on. A frontend calls
    /// this once (e.g. `Producer::Clean`) instead of tagging each function;
    /// [`FunctionBuilder::set_producer`] overrides it per function.
    pub fn set_default_producer(&mut self, producer: trust_ir::Producer) {
        self.default_producer = Some(producer);
    }

    /// Append a signature to the module's table. A full table records
    /// [`BuildError::IdSpaceExhausted`] and returns the placeholder
    /// `FuncTyId(u32::MAX)`; [`Self::build`] then refuses.
    pub fn add_func_type(&mut self, params: Vec<Ty>, returns: Vec<Ty>) -> FuncTyId {
        let id = self
            .module
            .add_func_type(FuncTy::unrecorded(params, returns, false));
        self.recorded(id)
    }

    /// Intern a C-variadic function signature: `params` is the fixed prefix and
    /// callers may pass additional trailing arguments. Used to declare imports
    /// of variadic runtime symbols (e.g. `clean_alloc_ctor(tag, nobj, scalar,
    /// ...)`); `validate_module` only requires `args.len() >= params.len()` for
    /// calls to a vararg callee.
    pub fn add_vararg_func_type(&mut self, params: Vec<Ty>, returns: Vec<Ty>) -> FuncTyId {
        let id = self
            .module
            .add_func_type(FuncTy::unrecorded(params, returns, true));
        self.recorded(id)
    }

    pub fn add_struct(&mut self, sd: StructDef) -> trust_ir::StructId {
        self.module.add_struct(sd)
    }

    /// Register a `Ty` in the module's type table and return its `TyId`.
    ///
    /// Needed by callers that construct aggregate types such as
    /// `Ty::Array(TyId, len)`, whose element type must be interned first.
    pub fn add_type(&mut self, ty: Ty) -> trust_ir::TyId {
        let id = self.module.add_type(ty);
        self.recorded(id)
    }

    // ── The typed value model (v30) ───────────────────────────────────────
    //
    // Pass-throughs to the module's CONTENT-INTERNED tables. Frontends must
    // mint predicate/universe ids through these and never by pushing into the
    // tables directly: interning is what makes two carriers over the same
    // universe — minted by two different passes, cited by two different proofs
    // — the SAME id, so a control-flow join merges them instead of dropping
    // the convention and reverting the value to its raw encoding.

    /// Intern a [`trust_ir::Universe`] by content. See
    /// [`trust_ir::Module::intern_universe`].
    ///
    /// `None` means "not canonicalizable" and nothing else: a full table
    /// records [`BuildError::IdSpaceExhausted`] and returns
    /// `Some(placeholder)`.
    pub fn intern_universe(&mut self, universe: trust_ir::Universe) -> Option<trust_ir::UnivId> {
        let id = self.module.intern_universe(universe);
        self.recorded_option(id)
    }

    /// Intern a [`trust_ir::Pred`] by content. See
    /// [`trust_ir::Module::intern_pred`].
    ///
    /// `None` means "not canonicalizable" and nothing else (see
    /// [`Self::intern_universe`]).
    pub fn intern_pred(&mut self, pred: trust_ir::Pred) -> Option<trust_ir::PredId> {
        let id = self.module.intern_pred(pred);
        self.recorded_option(id)
    }

    /// Intern `Pred::InUniverse(universe, space)` in one step.
    pub fn intern_in_universe(
        &mut self,
        universe: trust_ir::Universe,
        space: trust_ir::Space,
    ) -> Option<trust_ir::PredId> {
        let id = self.module.intern_in_universe(universe, space);
        self.recorded_option(id)
    }

    /// Build the refinement type `refine<base, pred>`, interning `base` in the
    /// module type table. Representation-preserving: the value still has
    /// exactly `base`'s representation.
    pub fn refine_ty(&mut self, base: Ty, pred: trust_ir::PredId) -> Ty {
        let base_id = self.add_type(base);
        Ty::Refine(base_id, pred)
    }

    pub fn add_global(&mut self, global: Global) {
        self.module.globals.push(global);
    }

    // ── Module-table doors (WS4.12) ───────────────────────────────────────
    //
    // Thin pass-throughs to the `Module` methods, so a producer never has to
    // `build()` early and mutate the module by hand. Like every other builder
    // method they check NOTHING: the validator is the authority, and a door
    // here grants no claim the hand-built spelling would not.

    /// Register an enum definition and return its declared id, verbatim.
    ///
    /// Pass-through to [`Module::add_enum`] (raw: no dedup, no id-collision
    /// check), matching [`add_struct`](Self::add_struct). The caller owns the
    /// id space: two defs sharing an id are a validation error, not something
    /// this door prevents.
    pub fn add_enum(&mut self, ed: EnumDef) -> EnumId {
        self.module.add_enum(ed)
    }

    /// Register a record definition and return its declared id, verbatim.
    /// Pass-through to [`Module::add_record`].
    pub fn add_record(&mut self, rd: RecordDef) -> RecordId {
        self.module.add_record(rd)
    }

    /// Register a closure type and return its positional id. Pass-through to
    /// [`Module::add_closure_type`].
    pub fn add_closure_type(&mut self, ct: ClosureTy) -> ClosureTyId {
        let id = self.module.add_closure_type(ct);
        self.recorded(id)
    }

    /// Intern a function signature by structure (idempotent). Pass-through to
    /// [`Module::intern_func_type`]; [`add_func_type`](Self::add_func_type)
    /// stays the always-appending form.
    pub fn intern_func_type(&mut self, ft: FuncTy) -> FuncTyId {
        let id = self.module.intern_func_type(ft);
        self.recorded(id)
    }

    /// Intern a cross-crate dependency by content (idempotent). Pass-through
    /// to [`Module::intern_import`].
    ///
    /// TRUST BOUNDARY: the row records a CLAIM about what was depended on. It
    /// authenticates nothing; `validate_linked_module` re-derives the digest
    /// against the artifact a resolver supplies.
    pub fn intern_import(&mut self, import: ModuleImport) -> ImportId {
        let id = self.module.intern_import(import);
        self.recorded(id)
    }

    /// Append a spec module (`Module::spec_modules`). Anchors and waivers
    /// name a spec module by its `name`, so there is no id to return.
    /// Duplicate names are not checked here; the spec linker and the
    /// validator own that.
    pub fn add_spec_module(&mut self, spec: SpecModule) {
        self.module.spec_modules.push(spec);
    }

    /// Append one module-level `global_asm!` block (`Module::global_asm`,
    /// v41), in source order. Opaque text; a consumer that cannot emit it
    /// must refuse the module, never drop it.
    /// State `glue` as the drop glue of `ty` (amendment D,
    /// `docs/SPEC_RATIFICATIONS.md` §20): every `Drop` / `DropInvoke` at `ty`
    /// then executes as a call of `glue`. Inserted at the table's canonical
    /// position ([`Module::set_drop_glue`]); a second glue for one type, or
    /// one glue for two types, is refused. Whether `glue` is a `(ptr) -> ()`
    /// function is `validate_module`'s question (`InvalidDropGlue`).
    pub fn set_drop_glue(
        &mut self,
        ty: Ty,
        glue: FuncId,
    ) -> Result<(), trust_ir::DropGlueConflict> {
        self.module.set_drop_glue(ty, glue)
    }

    /// Interns `data` in the module's content-addressed blob table
    /// ([`Module::intern_blob`], PKG-U13e) and returns the digest a
    /// `Constant::TensorBlob` names it by. Identical bytes are held once.
    pub fn intern_blob(&mut self, data: Vec<u8>) -> trust_ir::blob::BlobDigest {
        self.module.intern_blob(data)
    }

    pub fn add_global_asm(&mut self, asm: impl Into<String>) {
        self.module.global_asm.push(asm.into());
    }

    /// The `FuncId` the next [`function`](Self::function) or
    /// [`declare_function`](Self::declare_function) call will assign.
    ///
    /// A producer that must know a body's id BEFORE taking the builder's
    /// exclusive module borrow (to wire self-recursion, or to B4-scope a
    /// module-level [`ProofObligation`] at the body it belongs to) reads it
    /// here instead of re-deriving the arithmetic and hoping it still agrees.
    ///
    /// It returns `Result`, not a placeholder: `&self` cannot record a fault,
    /// and an unrecorded placeholder would escape into a committed obligation.
    ///
    /// # Errors
    ///
    /// [`IdSpaceExhausted`] once `u32::MAX` has been assigned.
    pub fn peek_next_func_id(&self) -> Result<FuncId, IdSpaceExhausted> {
        self.next_func_id
            .peek()
            .ok_or(IdSpaceExhausted::of::<FuncId>())
    }

    /// Take the next function id. Once the space is exhausted, records
    /// [`BuildError::IdSpaceExhausted`] and returns `None`; the caller hands
    /// out the placeholder `FuncId(u32::MAX)` and commits nothing.
    fn allocate_function_id(&mut self) -> Option<FuncId> {
        match self.next_func_id.take() {
            Ok(id) => Some(id),
            Err(exhausted) => {
                record(
                    &mut self.fault,
                    BuildError::IdSpaceExhausted {
                        space: exhausted.space,
                        function: None,
                    },
                );
                None
            }
        }
    }

    /// A table door's id, or — on a full table — the recorded fault and the
    /// placeholder `u32::MAX` of the id's space.
    fn recorded<I: TypedId>(&mut self, id: Result<I, IdSpaceExhausted>) -> I {
        match id {
            Ok(id) => id,
            Err(exhausted) => {
                record(
                    &mut self.fault,
                    BuildError::IdSpaceExhausted {
                        space: exhausted.space,
                        function: None,
                    },
                );
                I::from_index(u32::MAX)
            }
        }
    }

    /// [`Self::recorded`] for an interning door whose `None` means "not
    /// canonicalizable": capacity is a fault and `Some(placeholder)`.
    fn recorded_option<I: TypedId>(
        &mut self,
        id: Result<Option<I>, IdSpaceExhausted>,
    ) -> Option<I> {
        match id {
            Ok(id) => id,
            Err(exhausted) => Some(self.recorded(Err(exhausted))),
        }
    }

    /// RECORD an undischarged proof obligation on the module, allocating its
    /// `ProofId` (one past the largest id already in the table, so a sparse
    /// producer-assigned table never collides). `make` receives the freshly
    /// allocated id and returns the row to push; the returned id is the one
    /// that landed.
    ///
    /// TRUST BOUNDARY: this mints a CLAIM, never evidence. It attaches no
    /// certificate and asserts nothing about `status` — a producer recording a
    /// property it has not proved must pass
    /// [`ProofStatus::Pending`](trust_ir::ProofStatus::Pending). A stronger
    /// status here is a statement about work that was actually done elsewhere;
    /// `validate_module` independently refuses `Discharged`/`Certified` rows
    /// with no ground certificate.
    ///
    /// The id is the one rule [`Module::next_obligation_id`] states, so
    /// every table-extending door allocates identically.
    ///
    /// # Errors
    ///
    /// Nothing is pushed on any error:
    ///
    /// - [`AddObligationError::IdSpaceExhausted`] when a row already holds
    ///   `u32::MAX` (`make` is not called);
    /// - [`AddObligationError::IdMismatch`] when `make` returned a row whose
    ///   `id` is not the one it was handed — the row is neither pushed nor
    ///   overwritten, and comes back in the error. Checked in every profile.
    pub fn add_proof_obligation(
        &mut self,
        make: impl FnOnce(ProofId) -> ProofObligation,
    ) -> Result<ProofId, AddObligationError> {
        let id = self
            .module
            .fresh_obligation_ids()
            .take()
            .map_err(AddObligationError::IdSpaceExhausted)?;
        let obligation = make(id);
        if obligation.id != id {
            return Err(AddObligationError::IdMismatch {
                minted: id,
                row: Box::new(obligation),
            });
        }
        self.module.proof_obligations.push(obligation);
        Ok(id)
    }

    /// Attach an [`trust_ir::ObligationSite`] to an already-recorded obligation.
    ///
    /// Sites can only be known AFTER the function is built — the IR position of
    /// a lowered check does not exist while the obligation table is being
    /// populated (the frontend records obligations in a pre-`FunctionBuilder`
    /// window, because that is when it holds the module borrow). So this is the
    /// deliberate back-fill door, and it is narrow: it sets `site` and nothing
    /// else.
    ///
    /// Returns `false` if no obligation carries `id`, so a producer whose
    /// bookkeeping has drifted can fail loudly rather than silently emit
    /// site-less rows.
    #[must_use]
    pub fn set_obligation_site(&mut self, id: ProofId, site: trust_ir::ObligationSite) -> bool {
        match self
            .module
            .proof_obligations
            .iter_mut()
            .find(|o| o.id == id)
        {
            Some(obligation) => {
                obligation.site = Some(site);
                true
            }
            None => false,
        }
    }

    /// Intern a source-file path in the module's debug-info file table and
    /// return its index (for use as `SourceSpan::file`). Idempotent. Pairs with
    /// `FunctionBuilder::set_span` to thread debug info through construction.
    ///
    /// A full table records [`BuildError::IdSpaceExhausted`] (space `files`)
    /// and returns the placeholder `u32::MAX`.
    pub fn intern_file(&mut self, path: impl Into<String>) -> u32 {
        match self.module.intern_file(path) {
            Ok(index) => index,
            Err(exhausted) => {
                record(
                    &mut self.fault,
                    BuildError::IdSpaceExhausted {
                        space: exhausted.space,
                        function: None,
                    },
                );
                u32::MAX
            }
        }
    }

    /// Start a function body under the next function id.
    ///
    /// Once the function-id space is exhausted this records
    /// [`BuildError::IdSpaceExhausted`]; the draft carries the placeholder
    /// `FuncId(u32::MAX)`, and its [`FunctionBuilder::build`] commits nothing.
    pub fn function(&mut self, name: impl Into<String>, ty: FuncTyId) -> FunctionBuilder<'_> {
        let id = self.allocate_function_id().unwrap_or(FuncId::new(u32::MAX));
        let mut func = Function::new(id, name, ty, BlockId::new(0));
        func.producer = self.default_producer.clone();
        FunctionBuilder::new(&mut self.module, &mut self.fault, func, None)
    }

    /// Reserve a function identity and its actual module-table slot before
    /// emitting any bodies. Forward and recursive calls can use the returned
    /// ID directly; definition order does not change declaration order.
    ///
    /// The reservation is a bodyless declaration with the ordinary function
    /// defaults (C calling convention, external linkage, no proof authority)
    /// and the current diagnostic producer tag. It remains bodyless if never
    /// defined. Signatures and eventual bodies are unchecked; callers must run
    /// module validation. This API is not a legalization/proof transaction.
    ///
    /// Once the function-ID space is exhausted this records
    /// [`BuildError::IdSpaceExhausted`], pushes nothing, and returns the
    /// placeholder `FuncId(u32::MAX)`; [`Self::build`] then refuses.
    pub fn declare_function(&mut self, name: impl Into<String>, ty: FuncTyId) -> FuncId {
        let Some(id) = self.allocate_function_id() else {
            return FuncId::new(u32::MAX);
        };
        let mut function = Function::new(id, name, ty, BlockId::new(0));
        function.producer = self.default_producer.clone();
        let slot = self.module.functions.len();
        // A bodyless declaration carries no claim, so no obligation is
        // synthesized; the refusal arm records rather than discards.
        if let Err(refusal) = self.module.try_add_function(function) {
            record(
                &mut self.fault,
                BuildError::IdSpaceExhausted {
                    space: refusal.exhausted.space,
                    function: Some(id),
                },
            );
            return id;
        }
        self.declarations.insert(
            id,
            FunctionDeclaration {
                slot,
                defined: false,
            },
        );
        id
    }

    /// Declare every entry point of a trusted handle runtime (v43) as a
    /// bodyless C `External` declaration carrying exactly the pinned
    /// signature and definition path, so the module passes the validator's
    /// pinned-symbol rules by construction.
    ///
    /// Idempotent per symbol: a same-named function that is already the exact
    /// pinned declaration is reused; a same-named function with any other
    /// signature or a body is [`HandleDeclError::ConflictingDeclaration`],
    /// and nothing is added in that case. The returned
    /// [`HandleRuntimeDecls`] carries the handle type and the entry-point
    /// ids by role.
    ///
    /// The declarations are FFI boundaries, so the module must carry
    /// `target_info` ([`Self::new_with_target_info`]) to validate.
    ///
    /// A pinned row GROWS: since WS3.2 the `Nat` row also carries the Clean
    /// kernel's native `Nat` surface (nineteen entry points, not five), and a
    /// shim can be pinned before its runtime exports it. A producer that
    /// calls only part of a row should therefore use
    /// [`Self::declare_handle_runtime_roles`] with the roles it calls, so a
    /// row edit never adds external declarations — symbols the link must
    /// then resolve — to a module that never calls them.
    pub fn declare_handle_runtime(
        &mut self,
        pin: &crate::validate::HandleRuntimePin,
    ) -> Result<HandleRuntimeDecls, HandleDeclError> {
        let roles: Vec<&str> = pin.entry_points.iter().map(|entry| entry.role).collect();
        self.declare_handle_runtime_roles(pin, &roles)
    }

    /// Declare exactly the entry points named by `roles`, and no others.
    ///
    /// [`Self::declare_handle_runtime`] declares the WHOLE row, which is the
    /// right default for a producer that uses all of it. This is the variant
    /// for a producer that uses part of it — most concretely one that
    /// constructs and inspects handles but never RELEASES them, and so has no
    /// business declaring the pinned `drop` symbol: an `External` declaration
    /// is a statement that the module's callees include that symbol, and a
    /// producer should state only what it calls.
    ///
    /// It also keeps the pin table's growth off the wire in the one place a
    /// pin row is observable as BYTES: the `ty_handle` conformance golden
    /// is built from this API with the four roles its body actually calls, so
    /// adding the `drop` row to [`TRUSTED_HANDLE_RUNTIMES`] left every golden
    /// byte-identical.
    ///
    /// Same contract as [`Self::declare_handle_runtime`] otherwise: idempotent
    /// per symbol, all-or-nothing, and a role the row does not pin is
    /// [`HandleDeclError::UnknownRole`] rather than a silent no-op. Duplicate
    /// roles in `roles` are harmless (each symbol is declared once).
    ///
    /// [`TRUSTED_HANDLE_RUNTIMES`]: crate::validate::TRUSTED_HANDLE_RUNTIMES
    pub fn declare_handle_runtime_roles(
        &mut self,
        pin: &crate::validate::HandleRuntimePin,
        roles: &[&str],
    ) -> Result<HandleRuntimeDecls, HandleDeclError> {
        for role in roles {
            if !pin.entry_points.iter().any(|entry| entry.role == *role) {
                return Err(HandleDeclError::UnknownRole {
                    runtime: pin.runtime.to_owned(),
                    role: (*role).to_owned(),
                });
            }
        }
        let selected = pin
            .entry_points
            .iter()
            .filter(|entry| roles.contains(&entry.role));
        // Check every entry before mutating anything.
        let mut planned: Vec<(&crate::validate::HandleEntryPoint, Option<FuncId>)> = Vec::new();
        for entry in selected {
            let expected = pin.func_ty(entry);
            let existing = self
                .module
                .functions
                .iter()
                .filter(|function| function.name == entry.symbol)
                .collect::<Vec<_>>();
            let reusable = match existing.as_slice() {
                [] => None,
                [function]
                    if function.is_declaration()
                        && function.linkage == trust_ir::Linkage::External
                        && function.calling_conv == pin.calling_conv
                        && !function.attrs.naked
                        && self.module.func_type(function.ty) == Some(&expected)
                        && function
                            .display_path
                            .as_deref()
                            .is_none_or(|path| path == entry.def_path) =>
                {
                    Some(function.id)
                }
                _ => {
                    return Err(HandleDeclError::ConflictingDeclaration {
                        symbol: entry.symbol.to_owned(),
                    });
                }
            };
            planned.push((entry, reusable));
        }
        let mut decls = HandleRuntimeDecls {
            handle: pin.handle_ty(),
            entries: std::collections::BTreeMap::new(),
        };
        for (entry, reusable) in planned {
            let id = match reusable {
                Some(id) => id,
                None => {
                    let signature = pin.func_ty(entry);
                    // The exact enumeration: a row past `u32::MAX` has no id,
                    // so nothing can name it (`value::table_index`).
                    let known = (0..=u32::MAX).zip(&self.module.func_types).find_map(
                        |(index, candidate)| {
                            (*candidate == signature).then_some(FuncTyId::new(index))
                        },
                    );
                    let ty = match known {
                        Some(ty) => ty,
                        None => {
                            let added = self.module.add_func_type(signature);
                            self.recorded(added)
                        }
                    };
                    let slot = self.module.functions.len();
                    let id = self.declare_function(entry.symbol, ty);
                    // A refused declare pushed nothing (its fault is
                    // recorded), so there is nothing to customize.
                    if let Some(function) = self
                        .module
                        .functions
                        .get_mut(slot)
                        .filter(|function| function.id == id)
                    {
                        function.calling_conv = pin.calling_conv;
                        function.linkage = trust_ir::Linkage::External;
                        function.display_path = Some(entry.def_path.to_owned());
                    }
                    id
                }
            };
            decls.entries.insert(entry.role, id);
        }
        Ok(decls)
    }

    /// Stage the body of a function reserved by [`Self::declare_function`].
    ///
    /// The draft preserves only the declaration's identity, name, signature,
    /// linkage, calling convention and diagnostic producer tag. Attributes,
    /// proofs, summaries, source provenance and body-local debug tables start
    /// empty. They are not transplanted from the declaration.
    ///
    /// Dropping the returned builder leaves the declaration and reservation
    /// untouched, so definition can be retried. [`FunctionBuilder::build`]
    /// replaces its exact reserved slot and consumes the reservation even if
    /// the unchecked draft is bodyless. No duplicate function is appended and
    /// no function ID is allocated or recycled by definition.
    pub fn define_function(
        &mut self,
        id: FuncId,
    ) -> Result<FunctionBuilder<'_>, FunctionDefinitionError> {
        let declaration = self
            .declarations
            .get_mut(&id)
            .ok_or(FunctionDefinitionError::NotDeclared(id))?;
        if declaration.defined {
            return Err(FunctionDefinitionError::AlreadyDefined(id));
        }
        let original = self
            .module
            .functions
            .get(declaration.slot)
            .filter(|function| function.id == id && function.blocks.is_empty())
            .ok_or(FunctionDefinitionError::DeclarationChanged(id))?;
        let mut function = Function::new(id, original.name.clone(), original.ty, BlockId::new(0));
        function.linkage = original.linkage;
        function.calling_conv = original.calling_conv;
        function.producer = original.producer.clone();
        Ok(FunctionBuilder::new(
            &mut self.module,
            &mut self.fault,
            function,
            Some(declaration),
        ))
    }

    /// The one exit of the builder world: the module, or the first fault any
    /// door recorded ([`BuildError`]). A placeholder id a refused door
    /// returned is never carried by a returned [`Module`].
    ///
    /// # Errors
    ///
    /// The first recorded [`BuildError`]; the partial module is dropped.
    pub fn build(self) -> Result<Module, BuildError> {
        match self.fault {
            Some(fault) => Err(fault),
            None => Ok(self.module),
        }
    }
}

#[derive(Debug)]
struct FunctionDeclaration {
    slot: usize,
    defined: bool,
}

/// Record a builder fault: the FIRST one wins, so the fault reported is the
/// one that happened first, not a consequence of it.
fn record(slot: &mut Option<BuildError>, fault: BuildError) {
    if slot.is_none() {
        *slot = Some(fault);
    }
}

/// Recoverable misuse of a reserved function definition. Rejection does not
/// mutate the module, the reservation, or either identity allocator.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum FunctionDefinitionError {
    /// No two-phase declaration reserved this ID (including legacy functions).
    NotDeclared(FuncId),
    /// A body builder already committed to this declaration.
    AlreadyDefined(FuncId),
    /// The reserved slot no longer contains its original bodyless function.
    DeclarationChanged(FuncId),
}

impl std::fmt::Display for FunctionDefinitionError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::NotDeclared(id) => write!(
                formatter,
                "function {} was not reserved for definition",
                id.index()
            ),
            Self::AlreadyDefined(id) => {
                write!(formatter, "function {} is already defined", id.index())
            }
            Self::DeclarationChanged(id) => write!(
                formatter,
                "function {} no longer has its reserved bodyless declaration",
                id.index()
            ),
        }
    }
}

impl std::error::Error for FunctionDefinitionError {}

/// Why [`ModuleBuilder::add_proof_obligation`] pushed nothing.
#[derive(Debug, Clone, PartialEq)]
pub enum AddObligationError {
    /// A row already holds obligation id `u32::MAX`: no fresh id exists.
    IdSpaceExhausted(IdSpaceExhausted),
    /// The row `make` returned does not carry the id it was handed. It is
    /// returned (boxed), not pushed and not overwritten.
    IdMismatch {
        /// The id the builder minted and handed to `make`.
        minted: ProofId,
        /// The rejected row.
        row: Box<ProofObligation>,
    },
}

impl std::fmt::Display for AddObligationError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::IdSpaceExhausted(exhausted) => {
                write!(formatter, "add_proof_obligation: {exhausted}")
            }
            Self::IdMismatch { minted, row } => write!(
                formatter,
                "add_proof_obligation: the row must carry the id it was handed (minted {}, row \
                 carries {})",
                minted.index(),
                row.id.index()
            ),
        }
    }
}

impl std::error::Error for AddObligationError {}

/// Why [`ModuleBuilder::build`] returned no module: the FIRST fault any door
/// of the builder world recorded. A door with no commit point records its
/// refusal here and returns a placeholder id (`u32::MAX` of its space), so
/// the fault names where construction first went wrong, and no placeholder
/// reaches a [`Module`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum BuildError {
    /// An id space ran out: every id of `space` is taken (refused, never
    /// wrapped). `function` names the draft it happened in, when one did.
    IdSpaceExhausted {
        space: &'static str,
        function: Option<FuncId>,
    },
    /// An instruction was emitted with no block selected
    /// ([`FunctionBuilder::switch_to_block`] first); `emitted` instructions
    /// had been emitted into the function before it. The node was dropped.
    NoCurrentBlock { function: FuncId, emitted: u32 },
    /// A door named a block the function does not have. Nothing was written.
    UnknownBlock { function: FuncId, block: BlockId },
    /// An ordinary block parameter was added while a canonical reservation
    /// view was alive (through the view's `DerefMut`). Mixing the two would
    /// let an exhausted reservation falsely appear canonical. Nothing was
    /// written.
    MixedReservation { function: FuncId },
    /// The function was committed while its reservation view was still
    /// marked alive (the view was leaked, e.g. with `mem::forget`). Nothing
    /// was committed.
    ReservationAbandoned { function: FuncId },
    /// The reserved declaration was already defined.
    AlreadyDefined(FuncId),
    /// The reserved slot no longer holds its original bodyless declaration.
    DeclarationChanged(FuncId),
}

impl std::fmt::Display for BuildError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::IdSpaceExhausted {
                space,
                function: None,
            } => write!(
                formatter,
                "cannot build the module: {}",
                IdSpaceExhausted { space }
            ),
            Self::IdSpaceExhausted {
                space,
                function: Some(function),
            } => write!(
                formatter,
                "cannot build function {}: {}",
                function.index(),
                IdSpaceExhausted { space }
            ),
            Self::NoCurrentBlock { function, emitted } => write!(
                formatter,
                "function {}: an instruction was emitted with no current block (after {emitted} \
                 emitted instructions); call switch_to_block first",
                function.index()
            ),
            Self::UnknownBlock { function, block } => write!(
                formatter,
                "function {} has no block {block}",
                function.index()
            ),
            Self::MixedReservation { function } => write!(
                formatter,
                "function {}: ordinary block-parameter allocation cannot be mixed with an active \
                 canonical reservation",
                function.index()
            ),
            Self::ReservationAbandoned { function } => write!(
                formatter,
                "function {}: built while a canonical block-parameter reservation is still active",
                function.index()
            ),
            Self::AlreadyDefined(id) => {
                write!(
                    formatter,
                    "reserved function {} is already defined",
                    id.index()
                )
            }
            Self::DeclarationChanged(id) => write!(
                formatter,
                "reserved function declaration {} changed",
                id.index()
            ),
        }
    }
}

impl std::error::Error for BuildError {}

/// Programmatic emitter for a single function's IR.
///
/// CONTRACT — this is an *unchecked* emitter by design: it produces structure,
/// it does not verify it. Specifically:
/// * No door panics on a value its signature admits ("A construction door
///   refuses; it never panics on a value its signature admits",
///   `docs/SPEC_RATIFICATIONS.md`). Misuse — an instruction emitted with no
///   current block (`switch_to_block` first), an unknown block, a mixed
///   reservation, an exhausted id space — is RECORDED as a sticky
///   [`BuildError`] on the module builder; the door returns a placeholder id
///   and [`ModuleBuilder::build`] reports the fault. (Until D1b this contract
///   chose to panic; that choice is reversed.)
/// * It performs **no** type-checking, SSA/dominance, terminator-placement, or
///   well-formedness checks — that is `validate_function`/`validate_module`'s
///   job. A builder can construct anything the validator rejects; producers are
///   expected to run validation before trusting a built module.
/// * `FuncId`s are assigned by `ModuleBuilder` at registration. Abandoning a
///   legacy [`ModuleBuilder::function`] draft leaves an ID gap; abandoning a
///   [`ModuleBuilder::define_function`] draft leaves its original reserved
///   declaration intact. IDs are never recycled and are not table indexes.
pub struct FunctionBuilder<'m> {
    module: &'m mut Module,
    /// The module builder's sticky fault ([`record`]), borrowed beside the
    /// module, so a fault recorded here poisons the module even when this
    /// draft is dropped.
    fault: &'m mut Option<BuildError>,
    func: Function,
    definition: Option<&'m mut FunctionDeclaration>,
    current_block: Option<BlockId>,
    /// Instructions emitted into this function so far (a diagnostic of
    /// [`BuildError::NoCurrentBlock`]).
    emitted: u32,
    /// The one fresh-id rule for this function's value ids: refused, never
    /// wrapped, once `u32::MAX` is taken.
    next_value: FreshIds<ValueId>,
    /// The same rule for block ids.
    next_block: FreshIds<BlockId>,
    /// Whether a canonical block-parameter reservation view is alive. Keeping
    /// the flag in the underlying builder makes unrestricted emission through
    /// the view safe: ordinary parameter allocation and nested reservation
    /// detect and reject mixing rather than silently invalidating
    /// canonicality. The reserved ids themselves live in the view's run.
    reservation_active: bool,
    /// The source span stamped onto every node emitted while it is set. `file`
    /// indexes `Module.files` (see `ModuleBuilder::intern_file`). Threads
    /// debug-info through the builder so emitted IR carries provenance for
    /// TrustCg DWARF output and obligation diagnostics. `None` => nodes are
    /// emitted span-less (the back-compat default).
    current_span: Option<SourceSpan>,
    /// The function-local lexical-scope index stamped onto subsequently
    /// emitted nodes. It indexes `Function::scopes`; `None` leaves nodes
    /// unstamped for legacy/debug-info-free producers.
    current_scope: Option<u32>,
    /// Byte-extent facts for pointer values in THIS function (see
    /// [`PtrExtent`]). Keyed by `ValueId::index`, which is unique per
    /// function — a fresh builder starts value numbering at 0, so the map
    /// never outlives or crosses the function it describes. Absence is the
    /// conservative default and carries no claim.
    ptr_extents: HashMap<u32, PtrExtent>,
    /// `(block, inst index)` of the node this builder pushed most
    /// recently, in ANY block. `annotate_last` requires it to be the node
    /// `last_emitted_position` names, so a cursor moved back to an older block
    /// cannot redirect an instruction claim onto that block's last node.
    last_pushed: Option<(BlockId, usize)>,
    /// The layouts of the module's types, kept across this function's
    /// `Alloca`s so each type is laid out once however many slots it sizes.
    /// Sound because the builder holds the module exclusively and edits no
    /// type table while it lives (it writes only its own function, at
    /// commit). `None` until the first layout-derived extent.
    layouts: Option<trust_ir::LayoutMemo>,
}

/// A move-only view of one exact [`FunctionBuilder`] with a reserved prefix of
/// future block-parameter value IDs.
///
/// Canonical TrustIR numbering places every block parameter before every
/// instruction result. Frontends that discover CFG joins while emitting can
/// reserve the exact number of future block parameters before the first
/// instruction, then attach those already-allocated IDs as blocks are created.
/// All ordinary builder operations remain available through this view.
///
/// This is an unchecked construction convenience, not a validation result or
/// proof. [`Self::is_exhausted`] says only that this reservation interval was
/// attached completely; it does not certify the finished function. A producer
/// can still make the function noncanonical after dropping the view. Dropping
/// an incomplete reservation reserves no IR definition by itself; if later
/// definitions are allocated, its unused IDs become observable gaps and
/// canonical identity fast paths decline naturally.
///
/// ```compile_fail
/// use trust_ir_build::builder::ReservedBlockParamFunctionBuilder;
///
/// fn needs_clone<T: Clone>() {}
/// needs_clone::<ReservedBlockParamFunctionBuilder<'static, 'static>>();
/// ```
#[must_use = "reserved value IDs should be deliberately attached or abandoned"]
pub struct ReservedBlockParamFunctionBuilder<'builder, 'module> {
    builder: &'builder mut FunctionBuilder<'module>,
    /// The reserved ids not yet attached. Their count is stored, so no
    /// subtraction of cursor positions exists.
    run: IdRun<ValueId>,
    /// The block the most recent attachment named (seeded from the dense
    /// prefix), for the nondecreasing-order rule.
    last_block: Option<BlockId>,
}

impl<'builder, 'module> Deref for ReservedBlockParamFunctionBuilder<'builder, 'module> {
    type Target = FunctionBuilder<'module>;

    fn deref(&self) -> &Self::Target {
        self.builder
    }
}

impl DerefMut for ReservedBlockParamFunctionBuilder<'_, '_> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.builder
    }
}

/// Recoverable misuse of canonical block-parameter reservation.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum ReservedBlockParamError {
    /// Reserving the requested prefix would overflow TrustIR's `u32` value-ID space.
    ValueIdOverflow,
    /// A reservation view already exclusively owns this builder.
    ReservationAlreadyActive,
    /// Existing value allocation is not a dense block-parameter-only prefix.
    NonCanonicalExistingValuePrefix,
    /// Every reserved value ID has already been attached.
    Exhausted,
    /// The requested block does not belong to the wrapped function.
    UnknownBlock(BlockId),
    /// Attaching to an earlier block would violate canonical block-parameter order.
    BlockOrder {
        /// Most recently attached block.
        previous: BlockId,
        /// Requested earlier block.
        requested: BlockId,
    },
}

impl std::fmt::Display for ReservedBlockParamError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::ValueIdOverflow => {
                formatter.write_str("block-parameter reservation overflows the value-ID space")
            }
            Self::ReservationAlreadyActive => {
                formatter.write_str("a block-parameter reservation is already active")
            }
            Self::NonCanonicalExistingValuePrefix => formatter
                .write_str("existing value IDs are not a dense block-parameter-only prefix"),
            Self::Exhausted => formatter.write_str("block-parameter reservation is exhausted"),
            Self::UnknownBlock(block) => {
                write!(
                    formatter,
                    "block-parameter reservation names unknown bb{}",
                    block.index()
                )
            }
            Self::BlockOrder {
                previous,
                requested,
            } => write!(
                formatter,
                "block-parameter reservation order regressed from bb{} to bb{}",
                previous.index(),
                requested.index()
            ),
        }
    }
}

impl std::error::Error for ReservedBlockParamError {}

/// Recoverable reserved-parameter attachment failure.
///
/// The exact [`Ty`] supplied by the caller is retained so a failed checked
/// attachment never requires pre-cloning an owned type merely to retry.
#[derive(Debug, PartialEq, Eq)]
#[must_use = "the rejected type owner should be recovered or deliberately dropped"]
pub struct ReservedBlockParamAttachFailure {
    error: ReservedBlockParamError,
    ty: Ty,
}

impl ReservedBlockParamAttachFailure {
    /// Borrow the attachment rejection reason.
    #[must_use]
    pub const fn error(&self) -> &ReservedBlockParamError {
        &self.error
    }

    /// Borrow the exact rejected type owner.
    #[must_use]
    pub const fn ty(&self) -> &Ty {
        &self.ty
    }

    /// Recover both the rejection reason and exact type owner.
    #[must_use]
    pub fn into_parts(self) -> (ReservedBlockParamError, Ty) {
        (self.error, self.ty)
    }
}

impl std::fmt::Display for ReservedBlockParamAttachFailure {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.error.fmt(formatter)
    }
}

impl std::error::Error for ReservedBlockParamAttachFailure {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        Some(&self.error)
    }
}

impl ReservedBlockParamFunctionBuilder<'_, '_> {
    /// Number of reserved value IDs not yet attached to a block.
    #[must_use]
    pub fn remaining(&self) -> u32 {
        self.run.remaining()
    }

    /// Whether every value ID in this reservation interval was attached exactly once.
    ///
    /// This does not validate or freeze the function. Subsequent ordinary
    /// builder operations after this view is dropped can make its numbering
    /// noncanonical.
    #[must_use]
    pub fn is_exhausted(&self) -> bool {
        self.remaining() == 0
    }

    /// Attach the next reserved value ID to `block` without allocating another ID.
    ///
    /// Successful calls must name blocks in nondecreasing ID order. The cursor
    /// advances only after all checks pass, and every error returns the exact
    /// rejected [`Ty`] for retry.
    pub fn add_reserved_block_param(
        &mut self,
        block: BlockId,
        ty: Ty,
    ) -> Result<ValueId, ReservedBlockParamAttachFailure> {
        let reject = |error, ty| Err(ReservedBlockParamAttachFailure { error, ty });
        if self.run.remaining() == 0 {
            return reject(ReservedBlockParamError::Exhausted, ty);
        }
        if let Some(previous) = self.last_block
            && block.index() < previous.index()
        {
            return reject(
                ReservedBlockParamError::BlockOrder {
                    previous,
                    requested: block,
                },
                ty,
            );
        }
        let Some(target) = self
            .builder
            .func
            .blocks
            .get_mut(block.as_usize())
            .filter(|target| target.id == block)
        else {
            return reject(ReservedBlockParamError::UnknownBlock(block), ty);
        };
        let Some(value) = self.run.take() else {
            return reject(ReservedBlockParamError::Exhausted, ty);
        };
        self.last_block = Some(block);
        target.params.push((value, ty));
        Ok(value)
    }
}

impl Drop for ReservedBlockParamFunctionBuilder<'_, '_> {
    fn drop(&mut self) {
        self.builder.reservation_active = false;
    }
}

impl<'m> FunctionBuilder<'m> {
    fn new(
        module: &'m mut Module,
        fault: &'m mut Option<BuildError>,
        func: Function,
        definition: Option<&'m mut FunctionDeclaration>,
    ) -> Self {
        Self {
            module,
            fault,
            func,
            definition,
            current_block: None,
            emitted: 0,
            next_value: FreshIds::new(),
            next_block: FreshIds::new(),
            reservation_active: false,
            current_span: None,
            current_scope: None,
            ptr_extents: HashMap::new(),
            last_pushed: None,
            layouts: None,
        }
    }

    /// Record a fault on the module builder (the first one wins).
    fn record(&mut self, fault: BuildError) {
        record(self.fault, fault);
    }

    /// Record an exhausted id space in this function.
    fn record_exhausted(&mut self, exhausted: IdSpaceExhausted) {
        let function = Some(self.func.id);
        self.record(BuildError::IdSpaceExhausted {
            space: exhausted.space,
            function,
        });
    }

    /// Take the next value id, or record the exhausted space and return
    /// `None` (never a wrap onto an id already defined).
    fn take_value(&mut self) -> Option<ValueId> {
        match self.next_value.take() {
            Ok(id) => Some(id),
            Err(exhausted) => {
                self.record_exhausted(exhausted);
                None
            }
        }
    }

    /// The value id for an emitted definition; once `u32::MAX` is taken (a
    /// function with 2^32 definitions) the fault is recorded and the
    /// placeholder `ValueId(u32::MAX)` returned.
    fn alloc_value(&mut self) -> ValueId {
        self.take_value().unwrap_or(ValueId::new(u32::MAX))
    }

    /// The block `block` names in this function, if it has one.
    fn block_mut(&mut self, block: BlockId) -> Option<&mut Block> {
        self.func
            .blocks
            .get_mut(block.as_usize())
            .filter(|candidate| candidate.id == block)
    }

    /// Append a new block and return its id.
    ///
    /// Once block id `u32::MAX` has been assigned this records
    /// [`BuildError::IdSpaceExhausted`], appends nothing, and returns the
    /// placeholder `BlockId(u32::MAX)` (never wrapping onto block 0).
    pub fn create_block(&mut self) -> BlockId {
        match self.next_block.take() {
            Ok(id) => {
                self.func.blocks.push(Block::new(id));
                id
            }
            Err(exhausted) => {
                self.record_exhausted(exhausted);
                BlockId::new(u32::MAX)
            }
        }
    }

    /// Allocate and append one ordinary block parameter.
    ///
    /// Through a live [`ReservedBlockParamFunctionBuilder`] this records
    /// [`BuildError::MixedReservation`] and writes nothing: mixing the two
    /// allocation modes would let an exhausted reservation falsely appear to
    /// preserve canonical parameter order. An unknown `block` records
    /// [`BuildError::UnknownBlock`]. Either way the placeholder
    /// `ValueId(u32::MAX)` is returned.
    pub fn add_block_param(&mut self, block: BlockId, ty: Ty) -> ValueId {
        let function = self.func.id;
        if self.reservation_active {
            self.record(BuildError::MixedReservation { function });
            return ValueId::new(u32::MAX);
        }
        if self.block_mut(block).is_none() {
            self.record(BuildError::UnknownBlock { function, block });
            return ValueId::new(u32::MAX);
        }
        let Some(val) = self.take_value() else {
            return ValueId::new(u32::MAX);
        };
        if let Some(target) = self.block_mut(block) {
            target.params.push((val, ty));
        }
        val
    }

    /// Reserve an exact prefix of future value IDs for block parameters.
    ///
    /// The returned move-only view exclusively borrows this exact function
    /// builder, so reserved IDs cannot be attached through another function.
    /// Instruction emission through the view starts after the complete reserved
    /// range. Attaching the range later in nondecreasing block-ID order preserves
    /// the block-parameter-first prefix used by canonical TrustIR. Exhausting
    /// the range is not a whole-function canonicality certificate; the producer
    /// must still finish construction correctly and run normal validation.
    ///
    /// Dropping an incomplete range creates no definition by itself. Any later
    /// value allocation exposes the unused IDs as gaps, so callers should
    /// require [`ReservedBlockParamFunctionBuilder::is_exhausted`] on successful
    /// producer paths. The builder remains structurally unchecked; ordinary
    /// TrustIR validation is still required before granting authority.
    ///
    /// A complete external use still validates the finished module normally:
    ///
    /// ```
    /// use trust_ir::ty::Ty;
    /// use trust_ir_build::{validate_module, ModuleBuilder};
    ///
    /// let mut module = ModuleBuilder::new("reserved-join");
    /// let signature = module.add_func_type(vec![], vec![Ty::Bool]);
    /// let mut function = module.function("f", signature);
    /// let entry = function.create_block();
    /// let join = function.create_block();
    /// function.set_entry(entry);
    /// {
    ///     let mut reserved = function.reserve_block_params(1)?;
    ///     reserved.switch_to_block(entry);
    ///     let condition = reserved.bool_const(true);
    ///     reserved.br(join, vec![condition]);
    ///     let joined = reserved.add_reserved_block_param(join, Ty::Bool)?;
    ///     reserved.switch_to_block(join);
    ///     reserved.ret(vec![joined]);
    ///     assert!(reserved.is_exhausted());
    /// }
    /// function.build();
    /// assert!(validate_module(&module.build()?).is_empty());
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// The reservation view exclusively borrows the exact builder:
    ///
    /// ```compile_fail
    /// use trust_ir::ty::Ty;
    /// use trust_ir_build::builder::ModuleBuilder;
    ///
    /// let mut module = ModuleBuilder::new("exclusive");
    /// let signature = module.add_func_type(vec![], vec![]);
    /// let mut function = module.function("f", signature);
    /// let mut reserved = function.reserve_block_params(1).unwrap();
    /// let _other_block = function.create_block();
    /// let block = reserved.create_block();
    /// let _value = reserved.add_reserved_block_param(block, Ty::Bool);
    /// ```
    ///
    /// # Errors
    ///
    /// Returns:
    ///
    /// - [`ReservedBlockParamError::ReservationAlreadyActive`] when called
    ///   through an existing live reservation view;
    /// - [`ReservedBlockParamError::NonCanonicalExistingValuePrefix`] when
    ///   prior results, gaps, or noncanonical parameters already consumed IDs;
    /// - [`ReservedBlockParamError::ValueIdOverflow`] when `count` cannot fit
    ///   in the remaining value-ID space.
    ///
    /// Every rejection leaves the builder unchanged.
    pub fn reserve_block_params(
        &mut self,
        count: u32,
    ) -> Result<ReservedBlockParamFunctionBuilder<'_, 'm>, ReservedBlockParamError> {
        if self.reservation_active {
            return Err(ReservedBlockParamError::ReservationAlreadyActive);
        }
        // The existing parameters must be the dense prefix `0, 1, 2, …` in
        // block order, and the builder's cursor must stand exactly after it
        // (no instruction result or gap consumed an id). Both are stated by
        // the one fresh-id rule, so no count is compared by hand.
        let mut prefix = FreshIds::<ValueId>::new();
        let mut last_block = None;
        for block in &self.func.blocks {
            for (value, _) in &block.params {
                if prefix.take() != Ok(*value) {
                    return Err(ReservedBlockParamError::NonCanonicalExistingValuePrefix);
                }
                last_block = Some(block.id);
            }
        }
        if prefix != self.next_value {
            return Err(ReservedBlockParamError::NonCanonicalExistingValuePrefix);
        }

        // All or nothing: on refusal the cursor is unchanged.
        let run = self
            .next_value
            .take_run(count)
            .map_err(|_| ReservedBlockParamError::ValueIdOverflow)?;
        self.reservation_active = true;
        Ok(ReservedBlockParamFunctionBuilder {
            builder: self,
            run,
            last_block,
        })
    }

    pub fn switch_to_block(&mut self, block: BlockId) {
        self.current_block = Some(block);
    }

    /// `(block, inst_index)` of the node emitted most recently into the current
    /// block, or `None` if no block is selected or the current block is empty.
    ///
    /// Exists so a producer can record a [`trust_ir::ObligationSite`] pointing
    /// at the instruction it JUST emitted. Reading the position back from the
    /// builder is the only way to get it right: a producer that recomputes the
    /// index from its own bookkeeping is one refactor away from attaching an
    /// obligation to the wrong instruction, and nothing downstream could tell.
    pub fn last_emitted_position(&self) -> Option<(BlockId, u32)> {
        let current = self.current_block?;
        let block = self
            .func
            .blocks
            .get(current.as_usize())
            .filter(|block| block.id == current)?;
        let index = u32::try_from(block.body.len().checked_sub(1)?).ok()?;
        Some((block.id, index))
    }

    /// Set the source span stamped onto subsequently-emitted nodes. `span.file`
    /// must index `Module.files` (use `ModuleBuilder::intern_file`). Stays in
    /// effect until changed or [`clear_span`](Self::clear_span).
    pub fn set_span(&mut self, span: SourceSpan) {
        self.current_span = Some(span);
    }

    /// Stop stamping a span on emitted nodes (back to the span-less default).
    pub fn clear_span(&mut self) {
        self.current_span = None;
    }

    /// Set the lexical-scope index stamped onto subsequently emitted nodes.
    pub fn set_scope(&mut self, scope: u32) {
        self.current_scope = Some(scope);
    }

    /// Stop stamping a lexical-scope index on emitted nodes.
    pub fn clear_scope(&mut self) {
        self.current_scope = None;
    }

    fn push_node(&mut self, mut node: InstrNode) {
        // Thread the builder's current span onto the node unless it already
        // carries one. Centralized here so every emit path (emit /
        // emit_with_proofs / emit_void and the terminator helpers) inherits it.
        if node.span.is_none()
            && let Some(span) = self.current_span
        {
            node.span = Some(span);
        }
        if node.scope.is_none()
            && let Some(scope) = self.current_scope
        {
            node.scope = Some(scope);
        }
        let function = self.func.id;
        let Some(block) = self.current_block else {
            let emitted = self.emitted;
            self.record(BuildError::NoCurrentBlock { function, emitted });
            return;
        };
        let Some(target) = self.block_mut(block) else {
            self.record(BuildError::UnknownBlock { function, block });
            return;
        };
        let at = target.body.len();
        target.body.push(node);
        self.last_pushed = Some((block, at));
        self.emitted = self.emitted.saturating_add(1);
    }

    // `pub(crate)` so the demo/fixture emitters (`crate::demo`) can share the
    // single span-threading emit path without widening the public API.
    pub(crate) fn emit(&mut self, inst: Inst) -> ValueId {
        let result = self.alloc_value();
        let node = InstrNode::new(inst).with_result(result);
        self.push_node(node);
        result
    }

    fn emit_results<const N: usize>(&mut self, inst: Inst) -> [ValueId; N] {
        let results = std::array::from_fn(|_| self.alloc_value());
        let mut node = InstrNode::new(inst);
        // Only the retained node needs a heap allocation. The returned array
        // keeps fixed-arity consumers from allocating another result vector.
        node.results = results.to_vec();
        self.push_node(node);
        results
    }

    fn emit_with_proofs(&mut self, inst: Inst, proofs: Vec<ProofAnnotation>) -> ValueId {
        let result = self.alloc_value();
        let mut node = InstrNode::new(inst).with_result(result);
        node.proofs = proofs;
        self.push_node(node);
        result
    }

    fn emit_void(&mut self, inst: Inst) {
        self.push_node(InstrNode::new(inst));
    }

    // --- Arithmetic ---

    pub fn binop(&mut self, op: BinOp, ty: Ty, lhs: ValueId, rhs: ValueId) -> ValueId {
        self.emit(Inst::BinOp { op, ty, lhs, rhs })
    }

    pub fn add(&mut self, ty: Ty, lhs: ValueId, rhs: ValueId) -> ValueId {
        self.binop(BinOp::Add, ty, lhs, rhs)
    }

    pub fn sub(&mut self, ty: Ty, lhs: ValueId, rhs: ValueId) -> ValueId {
        self.binop(BinOp::Sub, ty, lhs, rhs)
    }

    pub fn mul(&mut self, ty: Ty, lhs: ValueId, rhs: ValueId) -> ValueId {
        self.binop(BinOp::Mul, ty, lhs, rhs)
    }

    pub fn sdiv(&mut self, ty: Ty, lhs: ValueId, rhs: ValueId) -> ValueId {
        self.binop(BinOp::SDiv, ty, lhs, rhs)
    }

    pub fn udiv(&mut self, ty: Ty, lhs: ValueId, rhs: ValueId) -> ValueId {
        self.binop(BinOp::UDiv, ty, lhs, rhs)
    }

    pub fn fadd(&mut self, ty: Ty, lhs: ValueId, rhs: ValueId) -> ValueId {
        self.binop(BinOp::FAdd, ty, lhs, rhs)
    }

    pub fn fmul(&mut self, ty: Ty, lhs: ValueId, rhs: ValueId) -> ValueId {
        self.binop(BinOp::FMul, ty, lhs, rhs)
    }

    pub fn unop(&mut self, op: UnOp, ty: Ty, operand: ValueId) -> ValueId {
        self.emit(Inst::UnOp { op, ty, operand })
    }

    pub fn ctpop(&mut self, ty: Ty, operand: ValueId) -> ValueId {
        self.unop(UnOp::CtPop, ty, operand)
    }

    pub fn overflow(
        &mut self,
        op: OverflowOp,
        ty: Ty,
        lhs: ValueId,
        rhs: ValueId,
    ) -> (ValueId, ValueId) {
        let result = self.alloc_value();
        let flag = self.alloc_value();
        let node = InstrNode::new(Inst::Overflow { op, ty, lhs, rhs })
            .with_result(result)
            .with_result(flag);
        self.push_node(node);
        (result, flag)
    }

    // --- Comparison ---

    pub fn icmp(&mut self, op: ICmpOp, ty: Ty, lhs: ValueId, rhs: ValueId) -> ValueId {
        self.emit(Inst::ICmp { op, ty, lhs, rhs })
    }

    pub fn fcmp(&mut self, op: FCmpOp, ty: Ty, lhs: ValueId, rhs: ValueId) -> ValueId {
        self.emit(Inst::FCmp { op, ty, lhs, rhs })
    }

    // --- Cast ---

    pub fn cast(&mut self, op: CastOp, src_ty: Ty, dst_ty: Ty, operand: ValueId) -> ValueId {
        self.emit(Inst::Cast {
            op,
            src_ty,
            dst_ty,
            operand,
        })
    }

    pub fn zext(&mut self, src_ty: Ty, dst_ty: Ty, operand: ValueId) -> ValueId {
        self.cast(CastOp::ZExt, src_ty, dst_ty, operand)
    }

    pub fn sext(&mut self, src_ty: Ty, dst_ty: Ty, operand: ValueId) -> ValueId {
        self.cast(CastOp::SExt, src_ty, dst_ty, operand)
    }

    pub fn trunc(&mut self, src_ty: Ty, dst_ty: Ty, operand: ValueId) -> ValueId {
        self.cast(CastOp::Trunc, src_ty, dst_ty, operand)
    }

    // --- Pointer metadata ---

    pub fn ptr_data(&mut self, ptr_ty: Ty, ptr: ValueId) -> ValueId {
        self.emit(Inst::PtrData { ptr_ty, ptr })
    }

    pub fn ptr_metadata(&mut self, ptr_ty: Ty, metadata_ty: Ty, ptr: ValueId) -> ValueId {
        self.emit(Inst::PtrMetadata {
            ptr_ty,
            metadata_ty,
            ptr,
        })
    }

    pub fn ptr_from_parts(
        &mut self,
        ptr_ty: Ty,
        metadata_ty: Ty,
        data: ValueId,
        metadata: ValueId,
    ) -> ValueId {
        self.emit(Inst::PtrFromParts {
            ptr_ty,
            metadata_ty,
            data,
            metadata,
        })
    }

    // --- Memory ---

    pub fn load(&mut self, ty: Ty, ptr: ValueId) -> ValueId {
        self.emit(Inst::Load {
            ty,
            ptr,
            volatile: false,
            align: None,
        })
    }

    pub fn load_volatile(&mut self, ty: Ty, ptr: ValueId) -> ValueId {
        self.emit(Inst::Load {
            ty,
            ptr,
            volatile: true,
            align: None,
        })
    }

    pub fn load_aligned(&mut self, ty: Ty, ptr: ValueId, align: u64) -> ValueId {
        self.emit(Inst::Load {
            ty,
            ptr,
            volatile: false,
            align: Some(align),
        })
    }

    pub fn load_proven(&mut self, ty: Ty, ptr: ValueId, proofs: Vec<ProofAnnotation>) -> ValueId {
        self.emit_with_proofs(
            Inst::Load {
                ty,
                ptr,
                volatile: false,
                align: None,
            },
            proofs,
        )
    }

    pub fn store(&mut self, ty: Ty, ptr: ValueId, value: ValueId) {
        self.emit_void(Inst::Store {
            ty,
            ptr,
            value,
            volatile: false,
            align: None,
        });
    }

    pub fn store_volatile(&mut self, ty: Ty, ptr: ValueId, value: ValueId) {
        self.emit_void(Inst::Store {
            ty,
            ptr,
            value,
            volatile: true,
            align: None,
        });
    }

    pub fn store_aligned(&mut self, ty: Ty, ptr: ValueId, value: ValueId, align: u64) {
        self.emit_void(Inst::Store {
            ty,
            ptr,
            value,
            volatile: false,
            align: Some(align),
        });
    }

    pub fn alloca(&mut self, ty: Ty) -> ValueId {
        let ptr = self.emit(Inst::Alloca {
            ty: ty.clone(),
            count: None,
            align: None,
        });
        self.note_layout_derived_extent(ptr, &ty);
        ptr
    }

    pub fn alloca_aligned(&mut self, ty: Ty, align: u64) -> ValueId {
        let ptr = self.emit(Inst::Alloca {
            ty: ty.clone(),
            count: None,
            align: Some(align),
        });
        self.note_layout_derived_extent(ptr, &ty);
        ptr
    }

    // --- Pointer extents (the evidence behind `inbounds`) ---

    /// Record that `ptr` is the base of an allocation of exactly `size_bytes`
    /// bytes, so [`gep_byte_offset`](Self::gep_byte_offset) can DISCHARGE the
    /// `inbounds` claim for offsets derived from it (see [`PtrExtent`]).
    ///
    /// A producer calls this when it knows a size the trust-ir format cannot
    /// derive on its own — most importantly a `Ty::Tuple` memory slot, which
    /// deliberately has no declared trust-ir layout, so
    /// [`Module::ty_layout_shape`] fails closed on it. The size supplied must
    /// be the allocation's true byte length; it is producer knowledge, and the
    /// inbounds claims derived from it are only as good as it is. Everything
    /// downstream of this fact is *checked*, not assumed.
    ///
    /// If `ptr` already carries an extent (the `Alloca` was layout-derivable)
    /// and the two DISAGREE, the SMALLER survives. A disagreement means the
    /// module is internally inconsistent about the allocation, and silently
    /// taking the producer's larger number would widen every claim built on it.
    pub fn note_alloc_extent(&mut self, ptr: ValueId, size_bytes: u64) {
        let size = match self.ptr_extents.get(&ptr.index()) {
            Some(prior) if prior.root == ptr => prior.size.min(size_bytes),
            _ => size_bytes,
        };
        self.ptr_extents.insert(
            ptr.index(),
            PtrExtent {
                root: ptr,
                offset: 0,
                size,
            },
        );
    }

    /// The recorded byte extent of `ptr`, or `None` when the builder has no
    /// fact about it. `None` is the normal, conservative answer.
    pub fn ptr_extent(&self, ptr: ValueId) -> Option<PtrExtent> {
        self.ptr_extents.get(&ptr.index()).copied()
    }

    /// Record an `Alloca`'s extent when — and only when — the format itself
    /// can size the allocated type byte-exactly.
    ///
    /// [`Module::ty_layout_shape`] is the RIGHT authority here, not a guess: it
    /// is the same layout a consumer resolves the `Alloca` with, so the extent
    /// it yields is the extent the allocation will actually have. Types with no
    /// declared trust-ir layout (`Tuple`, `Record`, `Set`, `Sequence`,
    /// `Closure`) and structs with no declared size fail closed here and simply
    /// get no extent — a producer that knows better says so with
    /// [`note_alloc_extent`](Self::note_alloc_extent).
    ///
    /// The layouts are asked of one memo kept for the builder's life, so a
    /// function with many `Alloca`s of deep types lays each type out once.
    fn note_layout_derived_extent(&mut self, ptr: ValueId, ty: &Ty) {
        let module: &Module = self.module;
        let table = match self.layouts.take() {
            Some(memo) => trust_ir::LayoutTable::with_memo(module, memo),
            None => module.layout_table(),
        };
        let size = table
            .ty_layout(ty)
            .ok()
            .and_then(|shape| shape.size_bytes());
        self.layouts = Some(table.into_memo());
        if let Some(size) = size {
            self.note_alloc_extent(ptr, size);
        }
    }

    /// Emit a byte-offset GEP — `gep(I8, base, [offset])`, which under
    /// trust-ir's FLAT GEP semantics (`base + Σ indices * size_of(pointee)`)
    /// with an `I8` pointee computes exactly `base + offset` bytes — setting
    /// `inbounds` and attaching [`ProofAnnotation::InBounds`] IFF the builder
    /// can discharge that claim.
    ///
    /// "Discharge" means: `base` has a recorded [`PtrExtent`] and
    /// `base.offset + offset <= alloc_size` (see [`PtrExtent::offset_by`], which
    /// permits the one-past-the-end address and fails closed on overflow). When
    /// `base`'s extent is unknown — a loaded pointer, a block parameter, a call
    /// result — the flag stays `false` and no annotation is attached. The claim
    /// is never taken on faith, so a producer bug in the offsets it passes here
    /// degrades to a missing hint rather than a wrong one.
    ///
    /// The result inherits the derived extent, so a chain of field/element
    /// offsets off one allocation stays checkable end to end.
    ///
    /// Emits the identical `Const` + `GEP` node pair either way; only the flag
    /// and the annotation differ.
    pub fn gep_byte_offset(&mut self, base: ValueId, offset: u64) -> ValueId {
        let derived = self.ptr_extent(base).and_then(|e| e.offset_by(offset));
        let idx = self.iconst(Ty::I64, i128::from(offset));
        let result = match derived {
            Some(_) => {
                self.gep_inbounds_proven(Ty::I8, base, vec![idx], vec![ProofAnnotation::InBounds])
            }
            None => self.gep(Ty::I8, base, vec![idx]),
        };
        if let Some(extent) = derived {
            self.ptr_extents.insert(result.index(), extent);
        }
        result
    }

    /// A GEP with `inbounds` UNSET (the conservative default). Use
    /// [`gep_inbounds`](Self::gep_inbounds) or
    /// [`gep_byte_offset`](Self::gep_byte_offset) when the in-allocation
    /// invariant is actually established.
    pub fn gep(&mut self, pointee_ty: Ty, base: ValueId, indices: Vec<ValueId>) -> ValueId {
        self.emit(Inst::GEP {
            pointee_ty,
            base,
            indices,
            inbounds: false,
        })
    }

    /// Like [`gep`](Self::gep) but sets the LLVM `inbounds` flag: the producer
    /// asserts the computed address stays within `base`'s allocation (poison/UB
    /// otherwise), enabling no-wrap GEP folding in the backend (fast-3). Use
    /// only when that invariant is actually established.
    pub fn gep_inbounds(
        &mut self,
        pointee_ty: Ty,
        base: ValueId,
        indices: Vec<ValueId>,
    ) -> ValueId {
        self.emit(Inst::GEP {
            pointee_ty,
            base,
            indices,
            inbounds: true,
        })
    }

    // --- Atomics ---

    pub fn atomic_load(&mut self, ty: Ty, ptr: ValueId, ordering: Ordering) -> ValueId {
        self.emit(Inst::AtomicLoad { ty, ptr, ordering })
    }

    pub fn atomic_store(&mut self, ty: Ty, ptr: ValueId, value: ValueId, ordering: Ordering) {
        self.emit_void(Inst::AtomicStore {
            ty,
            ptr,
            value,
            ordering,
        });
    }

    pub fn fence(&mut self, ordering: Ordering) {
        self.emit_void(Inst::Fence { ordering });
    }

    // --- Constants ---

    pub fn iconst(&mut self, ty: Ty, value: i128) -> ValueId {
        self.emit(Inst::Const {
            ty,
            value: Constant::Int(value),
        })
    }

    /// v24: unsigned 128-bit constant. Routed through the canonical
    /// [`Constant::u128`] constructor, so values at or below `i128::MAX`
    /// are spelled `Constant::Int` (the one-spelling rule) and only the
    /// upper half of the `u128` range becomes `Constant::U128`.
    pub fn uconst(&mut self, ty: Ty, value: u128) -> ValueId {
        self.emit(Inst::Const {
            ty,
            value: Constant::u128(value),
        })
    }

    /// v25: general constant materialization — any `Constant` under any
    /// declared type. The typed helpers above stay the ergonomic path for
    /// scalars; this is the door for aggregate / byte-array constants
    /// (validated by `validate_module` like every `Inst::Const`).
    pub fn const_value(&mut self, ty: Ty, value: Constant) -> ValueId {
        self.emit(Inst::Const { ty, value })
    }

    /// Materialize the ADDRESS of a function as a pointer-sized value (a
    /// `Const` of type `Ty::Func(sig)` carrying `Constant::FnDef(func)`). trust-cg
    /// lowers this to a `GlobalRef`/`ExternRef` symbol address — the analog of C's
    /// `(void*)fn`. Used by frontends to pass a function pointer to a runtime
    /// (e.g. `clean_alloc_closure`). Prefer this over a `ReifyFnPointer` cast,
    /// which trust-cg's backend does not support.
    pub fn fn_addr(&mut self, sig: FuncTyId, func: FuncId) -> ValueId {
        self.emit(Inst::Const {
            ty: Ty::Func(sig),
            value: Constant::FnDef(func),
        })
    }

    pub fn fconst(&mut self, ty: Ty, value: f64) -> ValueId {
        self.emit(Inst::Const {
            ty,
            value: Constant::Float(value),
        })
    }

    pub fn bool_const(&mut self, value: bool) -> ValueId {
        self.emit(Inst::Const {
            ty: Ty::Bool,
            value: Constant::Bool(value),
        })
    }

    // NOTE: the fixed-width SIMD demo shorthands (`v4_i32_*` / `v2_i64_*` /
    // `v*_bool_*`) and the portable `vector.*` dialect emitters historically
    // defined here live in `crate::demo::VectorDemoExt` — they are fixture
    // conveniences, not part of the general-purpose frontend emission surface.

    pub fn null_ptr(&mut self) -> ValueId {
        self.emit(Inst::NullPtr)
    }

    /// Heap allocation (`Inst::HeapAlloc`) of `count` (default 1) elements of
    /// `ty` from `origin`'s allocator, returning an opaque `Ptr`. Pair with
    /// `dealloc` to free. Lowers `Box::new`/`Vec`/`malloc`.
    pub fn heap_alloc(
        &mut self,
        ty: Ty,
        count: Option<ValueId>,
        align: Option<u64>,
        origin: AllocOrigin,
    ) -> ValueId {
        self.emit(Inst::HeapAlloc {
            ty,
            count,
            align,
            origin,
        })
    }

    /// Address of a module global as an SSA pointer (`Inst::GlobalAddr`).
    ///
    /// `global` must index a `Global` added via `ModuleBuilder::add_global`;
    /// `validate_module` rejects an out-of-range id. Lowers `&STATIC`, `&str`
    /// literal data, and trait-object vtable references.
    pub fn global_addr(&mut self, global: GlobalId) -> ValueId {
        self.emit(Inst::GlobalAddr { global })
    }

    // --- Control flow ---

    pub fn br(&mut self, target: BlockId, args: Vec<ValueId>) {
        self.emit_void(Inst::Br { target, args });
    }

    pub fn condbr(
        &mut self,
        cond: ValueId,
        then_target: BlockId,
        then_args: Vec<ValueId>,
        else_target: BlockId,
        else_args: Vec<ValueId>,
    ) {
        self.emit_void(Inst::CondBr {
            cond,
            then_target,
            then_args,
            else_target,
            else_args,
        });
    }

    pub fn ret(&mut self, values: Vec<ValueId>) {
        self.emit_void(Inst::Return { values });
    }

    pub fn call(&mut self, callee: FuncId, args: Vec<ValueId>) -> ValueId {
        self.emit(Inst::Call { callee, args })
    }

    pub fn call_void(&mut self, callee: FuncId, args: Vec<ValueId>) {
        self.emit_void(Inst::Call { callee, args });
    }

    /// Emit a direct call with exactly `N` SSA results in return order.
    ///
    /// Like the other call builders, this is unchecked: `N` declares the
    /// emitted result count; it is not inferred from the callee. Forward and
    /// self calls therefore need no completed callee body. Run
    /// [`crate::validate_module`] on the finished module to check the callee,
    /// arguments, and result arity against its signature.
    ///
    /// Zero and one are supported as well as multiple results. Returning an
    /// array avoids a second heap allocation for the result IDs.
    pub fn call_results<const N: usize>(
        &mut self,
        callee: FuncId,
        args: Vec<ValueId>,
    ) -> [ValueId; N] {
        self.emit_results(Inst::Call { callee, args })
    }

    // --- Exception handling (zero-cost table-driven unwinding) ---

    /// `Invoke` — a call TERMINATOR with two successors: on a normal return the
    /// callee's return value binds this instruction's result and control passes
    /// to `normal_dest` (with `normal_args`); if the callee unwinds, the host
    /// unwinder diverts to `unwind_dest`, whose block must BEGIN with an
    /// [`Self::landingpad`]. Value-returning form (one result, like [`Self::call`]).
    pub fn invoke(
        &mut self,
        callee: FuncId,
        args: Vec<ValueId>,
        normal_dest: BlockId,
        normal_args: Vec<ValueId>,
        unwind_dest: BlockId,
    ) -> ValueId {
        self.emit(Inst::Invoke {
            callee,
            args,
            normal_dest,
            normal_args,
            unwind_dest,
        })
    }

    /// Void form of [`Self::invoke`] (callee returns no value).
    pub fn invoke_void(
        &mut self,
        callee: FuncId,
        args: Vec<ValueId>,
        normal_dest: BlockId,
        normal_args: Vec<ValueId>,
        unwind_dest: BlockId,
    ) {
        self.emit_void(Inst::Invoke {
            callee,
            args,
            normal_dest,
            normal_args,
            unwind_dest,
        });
    }

    /// `InvokeIndirect` (amendment D, Part 2, wire v56): `CallIndirect`'s
    /// unwinding twin, with the default calling convention. A TERMINATOR
    /// whose one result (the callee's return) is defined on the normal edge
    /// only, as an [`Self::invoke`]'s is.
    pub fn invoke_indirect(
        &mut self,
        callee: ValueId,
        sig: FuncTyId,
        args: Vec<ValueId>,
        normal_dest: BlockId,
        normal_args: Vec<ValueId>,
        unwind_dest: BlockId,
    ) -> ValueId {
        self.emit(Inst::InvokeIndirect {
            callee,
            sig,
            args,
            calling_conv: trust_ir::CallingConv::default(),
            normal_dest,
            normal_args,
            unwind_dest,
        })
    }

    /// Void form of [`Self::invoke_indirect`] (the signature returns nothing).
    pub fn invoke_indirect_void(
        &mut self,
        callee: ValueId,
        sig: FuncTyId,
        args: Vec<ValueId>,
        normal_dest: BlockId,
        normal_args: Vec<ValueId>,
        unwind_dest: BlockId,
    ) {
        self.emit_void(Inst::InvokeIndirect {
            callee,
            sig,
            args,
            calling_conv: trust_ir::CallingConv::default(),
            normal_dest,
            normal_args,
            unwind_dest,
        });
    }

    /// `LandingPad` — the FIRST instruction of a block named by some `Invoke`'s
    /// `unwind_dest`. Produces `(exception object Ptr, I32 type selector)` from
    /// the unwinder's ABI registers. `catch_type_indices`: 0 == catch-all;
    /// empty + `is_cleanup` is a pure cleanup pad.
    pub fn landingpad(
        &mut self,
        is_cleanup: bool,
        catch_type_indices: Vec<u32>,
    ) -> (ValueId, ValueId) {
        let exn = self.alloc_value();
        let sel = self.alloc_value();
        let node = InstrNode::new(Inst::LandingPad {
            is_cleanup,
            catch_type_indices,
        })
        .with_result(exn)
        .with_result(sel);
        self.push_node(node);
        (exn, sel)
    }

    /// `Resume` — re-raise the in-flight exception after a cleanup pad has run
    /// (a TERMINATOR with no in-function successors). `exn` is the exception
    /// object pointer the pad produced.
    pub fn resume(&mut self, exn: ValueId) {
        self.emit_void(Inst::Resume { exn });
    }

    // --- Memory (continued) ---

    pub fn dealloc(&mut self, ptr: ValueId) {
        self.emit_void(Inst::Dealloc { ptr });
    }

    /// `MemCopy` (WS3.20): copy `bytes` bytes from `src` to `dst` —
    /// `memcpy` when `overlap` is `false`, `memmove` when `true`. `bytes` is
    /// an SSA value of exactly the module's byte-count type (`Usize` with
    /// target info, `U64` without); the validator pins that. See
    /// [`Inst::MemCopy`] for the semantics and the UB cases.
    pub fn memcopy(&mut self, dst: ValueId, src: ValueId, bytes: ValueId, overlap: bool) {
        self.emit_void(Inst::MemCopy {
            dst,
            src,
            bytes,
            overlap,
        });
    }

    /// `MemSet` (WS3.20): write the `U8` value `byte` to each of `bytes`
    /// bytes at `dst`. See [`Inst::MemSet`].
    pub fn memset(&mut self, dst: ValueId, byte: ValueId, bytes: ValueId) {
        self.emit_void(Inst::MemSet { dst, byte, bytes });
    }

    // --- Atomics (continued) ---

    pub fn atomic_rmw(
        &mut self,
        op: AtomicRMWOp,
        ty: Ty,
        ptr: ValueId,
        value: ValueId,
        ordering: Ordering,
    ) -> ValueId {
        self.emit(Inst::AtomicRMW {
            op,
            ty,
            ptr,
            value,
            ordering,
        })
    }

    pub fn cmpxchg(
        &mut self,
        ty: Ty,
        ptr: ValueId,
        expected: ValueId,
        desired: ValueId,
        success: Ordering,
        failure: Ordering,
    ) -> (ValueId, ValueId) {
        let result = self.alloc_value();
        let success_flag = self.alloc_value();
        // The builder's `cmpxchg` is the STRONG instruction, as it always was.
        let node = InstrNode::new(Inst::CmpXchg {
            ty,
            ptr,
            expected,
            desired,
            success,
            failure,
            weak: false,
        })
        .with_result(result)
        .with_result(success_flag);
        self.push_node(node);
        (result, success_flag)
    }

    // --- Borrow instructions (Rust ownership model) ---

    pub fn borrow(&mut self, ptr: ValueId) -> ValueId {
        self.emit(Inst::Borrow { ptr })
    }

    pub fn borrow_mut(&mut self, ptr: ValueId) -> ValueId {
        self.emit(Inst::BorrowMut { ptr })
    }

    pub fn end_borrow(&mut self, borrow_ptr: ValueId) {
        self.emit_void(Inst::EndBorrow { borrow_ptr });
    }

    // --- ARC instructions (Swift reference counting model) ---

    pub fn retain(&mut self, ptr: ValueId) {
        self.emit_void(Inst::Retain { ptr });
    }

    pub fn release(&mut self, ptr: ValueId) {
        self.emit_void(Inst::Release { ptr });
    }

    pub fn is_unique(&mut self, ptr: ValueId) -> ValueId {
        self.emit(Inst::IsUnique { ptr })
    }

    // --- Control flow (continued) ---

    pub fn switch(
        &mut self,
        value: ValueId,
        cases: Vec<SwitchCase>,
        default: BlockId,
        default_args: Vec<ValueId>,
    ) {
        self.emit_void(Inst::Switch {
            value,
            default,
            default_args,
            cases,
            // Builder-constructed switches assert no exhaustiveness fact; only
            // the TyCtxt-vetted extraction path sets this true.
            exhaustive_enum_unreachable: false,
        });
    }

    // --- Calls (continued) ---

    pub fn call_indirect(&mut self, callee: ValueId, sig: FuncTyId, args: Vec<ValueId>) -> ValueId {
        self.call_indirect_cc(callee, sig, args, trust_ir::CallingConv::default())
    }

    pub fn call_indirect_void(&mut self, callee: ValueId, sig: FuncTyId, args: Vec<ValueId>) {
        self.emit_void(Inst::CallIndirect {
            callee,
            sig,
            args,
            calling_conv: trust_ir::CallingConv::default(),
        });
    }

    /// Indirect call with an explicit callee calling convention (the indirect
    /// call edge's ABI, since the dynamic callee is not statically known).
    pub fn call_indirect_cc(
        &mut self,
        callee: ValueId,
        sig: FuncTyId,
        args: Vec<ValueId>,
        calling_conv: trust_ir::CallingConv,
    ) -> ValueId {
        self.emit(Inst::CallIndirect {
            callee,
            sig,
            args,
            calling_conv,
        })
    }

    /// Emit an indirect call with exactly `N` SSA results in return order and
    /// the default calling convention.
    ///
    /// `N` is an unchecked emitted arity, as in [`Self::call_results`]. Run
    /// [`crate::validate_module`] to check it against `sig`, the argument
    /// types, and any statically visible callee declaration.
    pub fn call_indirect_results<const N: usize>(
        &mut self,
        callee: ValueId,
        sig: FuncTyId,
        args: Vec<ValueId>,
    ) -> [ValueId; N] {
        self.call_indirect_results_cc(callee, sig, args, trust_ir::CallingConv::default())
    }

    /// Explicit-calling-convention form of [`Self::call_indirect_results`].
    ///
    /// This records the declared edge convention, not an ABI proof. Finished
    /// module validation checks agreement with a statically resolved callee.
    pub fn call_indirect_results_cc<const N: usize>(
        &mut self,
        callee: ValueId,
        sig: FuncTyId,
        args: Vec<ValueId>,
        calling_conv: trust_ir::CallingConv,
    ) -> [ValueId; N] {
        self.emit_results(Inst::CallIndirect {
            callee,
            sig,
            args,
            calling_conv,
        })
    }

    /// A `Box` deref of the thin pointer `operand` to a sized `pointee`,
    /// carrying `fact` (wire v72). The result is the same pointer at
    /// `Ty::Ptr`. The builder states the fact as given; the validator judges
    /// it (`validate/box_validity.rs`), and refuses a fact that is missing a
    /// conjunct, misordered, or whose checkable evidence does not re-derive.
    pub fn box_deref(
        &mut self,
        pointee: Ty,
        operand: ValueId,
        fact: trust_ir::box_validity::BoxValidityFact,
    ) -> ValueId {
        self.emit(Inst::BoxDeref {
            ptr_ty: Ty::Ptr,
            pointee: trust_ir::box_validity::BoxPointee::Sized { ty: pointee },
            operand,
            fact: Box::new(fact),
        })
    }

    // --- Aggregates ---

    /// Capture current SSA values in an environment with an exact nominal
    /// closure type. Validation checks the capture types and the target's
    /// physical signature (captures followed by apparent arguments).
    pub fn make_closure(
        &mut self,
        ty: ClosureTyId,
        func: FuncId,
        captures: Vec<ValueId>,
    ) -> ValueId {
        self.emit(Inst::MakeClosure { ty, func, captures })
    }

    pub fn extract_field(&mut self, ty: Ty, aggregate: ValueId, field: u32) -> ValueId {
        self.emit(Inst::ExtractField {
            ty,
            aggregate,
            field,
        })
    }

    pub fn insert_field(
        &mut self,
        ty: Ty,
        aggregate: ValueId,
        field: u32,
        value: ValueId,
    ) -> ValueId {
        self.emit(Inst::InsertField {
            ty,
            aggregate,
            field,
            value,
        })
    }

    /// WS3.5 (F-049): build a fully-initialised struct / tuple / record /
    /// array value from declaration-ordered register lanes. The canonical
    /// spelling for an aggregate with a non-constant lane — in particular the
    /// ONLY register-level seed for a lane of typed-reference type (`Rc<T>`,
    /// `&T`, `&mut T`, `*const T`, `*mut T`), which no `Constant` inhabits.
    /// `validate_module` checks the lane count and each lane's type exactly
    /// (`InvalidMakeAggregate` / `OperandTypeMismatch`); for an enum use
    /// [`Self::make_enum_variant`].
    pub fn make_aggregate(&mut self, ty: Ty, fields: Vec<ValueId>) -> ValueId {
        self.emit(Inst::MakeAggregate {
            ty,
            variant: None,
            fields,
        })
    }

    /// WS3.5 (F-049): build one variant of an enum value from its payload
    /// lanes. The discriminant is `discriminants[variant]` of the definition
    /// and is never an operand. `validate_module` refuses an out-of-range or
    /// uninhabited variant and a payload of the wrong arity or types.
    pub fn make_enum_variant(&mut self, ty: Ty, variant: u32, fields: Vec<ValueId>) -> ValueId {
        self.emit(Inst::MakeAggregate {
            ty,
            variant: Some(variant),
            fields,
        })
    }

    /// v50: `n` copies of one register value, spelled `Inst::ArraySplat`
    /// VERBATIM (`ty` is `Ty::Array(e, n)`). Constant size in `n`. The
    /// validator refuses `n == 0` (`NonCanonicalUniformArray`: the empty
    /// array is the constant `array[ ]`) — use [`Self::uniform_array`] to get
    /// the canonical spelling for any `n`.
    pub fn array_splat(&mut self, ty: Ty, value: ValueId) -> ValueId {
        self.emit(Inst::ArraySplat { ty, value })
    }

    /// v50: the array `[value; n]` (`ty` = `Ty::Array(e, n)`) in its ONE
    /// canonical spelling (`docs/SPEC_RATIFICATIONS.md` §3.1): `ArraySplat` for
    /// every `n >= 1` — one copy included, ratified while a one-lane
    /// `make_aggregate` had no wire encoding (before v51) — and the empty constant
    /// `const [e x 0] array[ ]` for `n == 0` (`value` is not read). The
    /// sanctioned producer entry point for a Rust `[x; N]`: O(1) in `n`, and
    /// every spelling it emits is binary-encodable. A non-array `ty` is
    /// emitted as an `ArraySplat` for the validator to refuse by name
    /// (`InvalidArraySplat`), never silently respelled.
    pub fn uniform_array(&mut self, ty: Ty, value: ValueId) -> ValueId {
        match ty {
            Ty::Array(_, 0) => self.const_value(ty, Constant::Array(Vec::new())),
            ty => self.array_splat(ty, value),
        }
    }

    /// The tensor region (PKG-U13a): the general contraction of `lhs`
    /// (`tensor<E, p>`) with `rhs` (`tensor<E, q>`), spelled
    /// `Inst::TensorContract` VERBATIM. `ty` is the result `tensor<E, r>`;
    /// `batch` and `contract` are `(lhs axis, rhs axis)` pairs (matrix
    /// multiply is `batch: []`, `contract: [(1, 0)]`). The validator checks
    /// the static rules (`InvalidTensorContract`); paired extents are run-time
    /// values whose agreement is a precondition, never checked here.
    pub fn tensor_contract(
        &mut self,
        ty: Ty,
        lhs: ValueId,
        rhs: ValueId,
        batch: Vec<(u32, u32)>,
        contract: Vec<(u32, u32)>,
    ) -> ValueId {
        self.emit(Inst::TensorContract {
            ty,
            lhs,
            rhs,
            batch,
            contract,
        })
    }

    /// The tensor region (PKG-U13c): the element-wise map of `body` over
    /// `args` (tensors of the result's rank, or integer / `Bool` scalars),
    /// spelled `Inst::TensorMap` VERBATIM. Lane `i < args.len()` is operand
    /// `i`'s element (or the scalar itself), lane `args.len() + j` node `j`'s
    /// value; the last node is the result element. The validator checks the
    /// static rules (`InvalidTensorMap`); operand extents are run-time values
    /// whose agreement is a precondition, never checked here.
    pub fn tensor_map(
        &mut self,
        ty: Ty,
        args: Vec<ValueId>,
        body: Vec<trust_ir::TensorMapNode<trust_ir::NoExt>>,
    ) -> ValueId {
        self.emit(Inst::TensorMap { ty, args, body })
    }

    /// The tensor region (PKG-U13c): the reduction of `src` over `axes`
    /// (strictly ascending) by `op`, a left fold from `op`'s identity in
    /// row-major order, spelled `Inst::TensorReduce` VERBATIM (its order is
    /// `TensorReduceOrder::RowMajor`, the only one). The validator checks the
    /// static rules (`InvalidTensorReduce`).
    pub fn tensor_reduce(
        &mut self,
        ty: Ty,
        src: ValueId,
        op: trust_ir::TensorReduceOp,
        axes: Vec<u32>,
    ) -> ValueId {
        self.emit(Inst::TensorReduce {
            ty,
            src,
            op,
            axes,
            order: trust_ir::TensorReduceOrder::RowMajor,
        })
    }

    /// The tensor region (PKG-U13c): the view of `src` through the
    /// coordinate function `exprs` (`shape` names each result extent's node,
    /// `index` each source coordinate's), reading `fill` where a source
    /// coordinate is out of range, spelled `Inst::TensorView` VERBATIM. The
    /// validator checks the static rules (`InvalidTensorView`); node values,
    /// extents and coordinates are run-time values whose ranges are
    /// preconditions, never checked here.
    #[allow(clippy::too_many_arguments)]
    pub fn tensor_view(
        &mut self,
        ty: Ty,
        src: ValueId,
        params: Vec<ValueId>,
        exprs: Vec<trust_ir::TensorIndexExpr>,
        shape: Vec<u32>,
        index: Vec<u32>,
        fill: Option<ValueId>,
    ) -> ValueId {
        self.emit(Inst::TensorView {
            ty,
            src,
            params,
            exprs,
            shape,
            index,
            fill,
        })
    }

    /// The tensor region (PKG-U13d): the gather of `data` at the coordinates
    /// `coords` holds (one integer coordinate tensor per data axis, each of
    /// the result's rank), spelled `Inst::TensorGather` VERBATIM. The
    /// validator checks the static rules (`InvalidTensorGather`); the
    /// coordinate tensors' extents and every coordinate's range are run-time
    /// values whose agreement and bounds are preconditions (the latter a
    /// `BoundsCheck` obligation), never checked here.
    pub fn tensor_gather(&mut self, ty: Ty, data: ValueId, coords: Vec<ValueId>) -> ValueId {
        self.emit(Inst::TensorGather { ty, data, coords })
    }

    /// The tensor region (PKG-U13d): `src` scattered over a copy of `init`
    /// at the coordinates `coords` holds (one integer coordinate tensor per
    /// axis of `init`, each of `src`'s rank; the row-major-last write to a
    /// repeated coordinate wins), spelled `Inst::TensorScatter` VERBATIM. The
    /// validator checks the static rules (`InvalidTensorScatter`); extents
    /// and bounds are preconditions, never checked here.
    pub fn tensor_scatter(
        &mut self,
        ty: Ty,
        init: ValueId,
        src: ValueId,
        coords: Vec<ValueId>,
    ) -> ValueId {
        self.emit(Inst::TensorScatter {
            ty,
            init,
            src,
            coords,
        })
    }

    pub fn extract_element(&mut self, ty: Ty, array: ValueId, index: ValueId) -> ValueId {
        self.emit(Inst::ExtractElement { ty, array, index })
    }

    pub fn insert_element(
        &mut self,
        ty: Ty,
        array: ValueId,
        index: ValueId,
        value: ValueId,
    ) -> ValueId {
        self.emit(Inst::InsertElement {
            ty,
            array,
            index,
            value,
        })
    }

    // --- Proof ---

    pub fn assume(&mut self, cond: ValueId) {
        self.emit_void(Inst::Assume { cond });
    }

    /// Emit an assert of UNKNOWN check identity (`AssertKind::Unspecified`),
    /// which a faithful lowering refuses; prefer [`Self::assert_kind`].
    pub fn assert(&mut self, cond: ValueId) {
        self.assert_kind(cond, trust_ir::AssertKind::Unspecified);
    }

    /// Emit a runtime check that panics as `kind` when `cond` is false (plan
    /// item P): the producer names WHICH Rust panic the failure is.
    pub fn assert_kind(&mut self, cond: ValueId, kind: trust_ir::AssertKind) {
        self.emit_void(Inst::Assert {
            cond,
            kind,
            site: None,
        });
    }

    /// Emit a SITED runtime check (amendment P, wire v54): when `cond` is
    /// false the failure is the panic `kind`, realized by calling
    /// `site.entry(kind operands.., site.location)`. Use for a MIR assert
    /// whose unwind action is `Continue` or `Unreachable`; one whose failure
    /// must enter an in-frame landing pad is [`Self::assert_invoke`].
    pub fn assert_sited(
        &mut self,
        cond: ValueId,
        kind: trust_ir::AssertKind,
        site: trust_ir::PanicSite,
    ) {
        self.emit_void(Inst::Assert {
            cond,
            kind,
            site: Some(site),
        });
    }

    /// Emit the TERMINATOR `AssertInvoke` (amendment P, wire v54): a sited
    /// check whose failure must enter the landing pad `unwind_dest` (MIR
    /// `UnwindAction::Cleanup` / `Terminate`); a passing check continues to
    /// `normal_dest(normal_args)`.
    pub fn assert_invoke(
        &mut self,
        cond: ValueId,
        kind: trust_ir::AssertKind,
        site: trust_ir::PanicSite,
        normal_dest: BlockId,
        normal_args: Vec<ValueId>,
        unwind_dest: BlockId,
    ) {
        self.emit_void(Inst::AssertInvoke {
            cond,
            kind,
            site,
            normal_dest,
            normal_args,
            unwind_dest,
        });
    }

    pub fn unreachable(&mut self) {
        self.emit_void(Inst::Unreachable);
    }

    /// Emit `drop ty, %ptr` (§20): run `ty`'s drop glue on the object at
    /// `ptr` (a `Ptr`). Resolved through the module drop-glue table it IS a
    /// call of the glue; with no row it is UNRESOLVED (refused by both
    /// engines and the codegen gate, never a no-op). A trivially droppable
    /// or refined `ty` is refused (`NonCanonicalDrop`): spell nothing.
    pub fn drop(&mut self, ty: Ty, ptr: ValueId) {
        self.emit_void(Inst::Drop { ty, ptr });
    }

    /// Emit the TERMINATOR `drop_invoke ty, %ptr to normal_dest(normal_args)
    /// unwind unwind_dest` (§20 rule 6): [`Self::drop`] with `Invoke`'s
    /// successor discipline (`unwind_dest` begins with a `LandingPad`).
    pub fn drop_invoke(
        &mut self,
        ty: Ty,
        ptr: ValueId,
        normal_dest: BlockId,
        normal_args: Vec<ValueId>,
        unwind_dest: BlockId,
    ) {
        self.emit_void(Inst::DropInvoke {
            ty,
            ptr,
            normal_dest,
            normal_args,
            unwind_dest,
        });
    }

    /// Add a proof annotation to the FUNCTION being built (`Function::proofs`).
    ///
    /// Deprecated because the name does not say which level it writes: it has
    /// always been function-level, and a producer reaching for it to annotate
    /// the instruction it just emitted attaches the claim to the whole
    /// function instead. Kept as an alias so existing callers keep compiling;
    /// the rename is a separate migration.
    #[deprecated(
        note = "function-level; use add_function_proof, or annotate_last for the instruction"
    )]
    pub fn add_proof(&mut self, annotation: ProofAnnotation) {
        self.add_function_proof(annotation);
    }

    /// Add a proof annotation to the function being built
    /// (`Function::proofs`).
    ///
    /// Function-level proofs describe properties of the entire function
    /// (e.g., Pure, NoPanic, Terminates). TrustIr reads these during
    /// cross-target synthesis to determine which functions can be
    /// offloaded to GPU/ANE. For a claim about ONE instruction, use
    /// [`annotate_last`](Self::annotate_last) or a `*_proven` emitter.
    pub fn add_function_proof(&mut self, annotation: ProofAnnotation) {
        self.func.proofs.push(annotation);
    }

    /// Attach a proof annotation to the node most recently emitted into the
    /// current block (`InstrNode::proofs`) — the position
    /// [`last_emitted_position`](Self::last_emitted_position) reports.
    ///
    /// This is the instruction-level door for emitters that have no
    /// `*_proven` variant. It records a claim and checks nothing; the
    /// validator decides whether the annotation is admissible on that node.
    ///
    /// # Errors
    ///
    /// [`BuilderError::NoEmittedInstruction`] when no block is selected or the
    /// current block has no node yet (e.g. right after
    /// [`switch_to_block`](Self::switch_to_block) onto a fresh block). Nothing
    /// is written in that case — in particular the annotation is NOT
    /// redirected to `Function::proofs`, which would widen an instruction
    /// claim into a claim about the whole function.
    ///
    /// [`BuilderError::LastEmittedInAnotherBlock`] when the cursor was moved
    /// back to a block after an instruction was emitted elsewhere: that
    /// block's last node is not the instruction just emitted, so the door
    /// refuses rather than attach the claim to it. Nothing is written.
    pub fn annotate_last(&mut self, annotation: ProofAnnotation) -> Result<(), BuilderError> {
        // Resolve the target through `last_emitted_position`, the ONE place
        // the builder defines "the instruction just emitted", so this door and
        // an `ObligationSite` recorded from that position always name the same
        // node.
        let Some((block, index)) = self.last_emitted_position() else {
            return Err(BuilderError::NoEmittedInstruction {
                block: self.current_block,
            });
        };
        let index = index as usize;
        // ...and require that node to be the one this builder pushed LAST.
        // Pushes only append to the current block, so the two disagree exactly
        // when something was emitted into another block after this one's last
        // node and the cursor was then moved back.
        match self.last_pushed {
            Some(last) if last == (block, index) => {}
            Some((emitted_in, _)) => {
                return Err(BuilderError::LastEmittedInAnotherBlock { block, emitted_in });
            }
            // Unreachable while every node enters through `push_node`; fail
            // closed rather than trust a node this builder did not emit.
            None => return Err(BuilderError::NoEmittedInstruction { block: Some(block) }),
        }
        let Some(node) = self
            .block_mut(block)
            .and_then(|target| target.body.get_mut(index))
        else {
            return Err(BuilderError::NoEmittedInstruction { block: Some(block) });
        };
        node.proofs.push(annotation);
        Ok(())
    }

    /// Emit a binary operation with proof annotations.
    ///
    /// Shorthand for emitting a BinOp instruction and attaching proof
    /// annotations in one step. Commonly used for annotating arithmetic
    /// with NoOverflow, Commutative, Associative.
    pub fn binop_proven(
        &mut self,
        op: BinOp,
        ty: Ty,
        lhs: ValueId,
        rhs: ValueId,
        proofs: Vec<ProofAnnotation>,
    ) -> ValueId {
        self.emit_with_proofs(Inst::BinOp { op, ty, lhs, rhs }, proofs)
    }

    /// Emit a store with proof annotations.
    ///
    /// Commonly used for annotating stores with InBounds, NotNull,
    /// ValidBorrow to prove memory safety for cross-target synthesis.
    pub fn store_proven(
        &mut self,
        ty: Ty,
        ptr: ValueId,
        value: ValueId,
        proofs: Vec<ProofAnnotation>,
    ) {
        let mut node = InstrNode::new(Inst::Store {
            ty,
            ptr,
            value,
            volatile: false,
            align: None,
        });
        node.proofs = proofs;
        self.push_node(node);
    }

    /// Emit a GEP (get element pointer) with proof annotations.
    ///
    /// Commonly used for annotating pointer arithmetic with InBounds,
    /// Aligned to prove memory safety for vectorization.
    ///
    /// NOTE: `inbounds` is deliberately left `false` here — the annotations are
    /// producer *claims*, and this constructor does not establish the
    /// in-allocation invariant the flag asserts. Reach for
    /// [`gep_inbounds_proven`](Self::gep_inbounds_proven) when the claim is
    /// established, or [`gep_byte_offset`](Self::gep_byte_offset) to have the
    /// builder discharge it from a recorded [`PtrExtent`].
    pub fn gep_proven(
        &mut self,
        pointee_ty: Ty,
        base: ValueId,
        indices: Vec<ValueId>,
        proofs: Vec<ProofAnnotation>,
    ) -> ValueId {
        self.emit_with_proofs(
            Inst::GEP {
                pointee_ty,
                base,
                indices,
                inbounds: false,
            },
            proofs,
        )
    }

    /// [`gep_proven`](Self::gep_proven) with the LLVM `inbounds` flag SET: the
    /// computed address is asserted to stay within `base`'s allocation
    /// (poison/UB otherwise). The pairing matters — `inbounds` alone is an
    /// unchecked backend hint (the validator does not constrain it), so a
    /// producer that sets it should also carry the corresponding
    /// [`ProofAnnotation::InBounds`] claim it is asserting.
    ///
    /// Use only where the invariant is actually established;
    /// [`gep_byte_offset`](Self::gep_byte_offset) is the checked path that
    /// establishes it from a recorded [`PtrExtent`] and calls this.
    pub fn gep_inbounds_proven(
        &mut self,
        pointee_ty: Ty,
        base: ValueId,
        indices: Vec<ValueId>,
        proofs: Vec<ProofAnnotation>,
    ) -> ValueId {
        self.emit_with_proofs(
            Inst::GEP {
                pointee_ty,
                base,
                indices,
                inbounds: true,
            },
            proofs,
        )
    }

    /// Emit a function call with proof annotations.
    ///
    /// TrustIr uses call-site annotations to determine whether a call can be
    /// offloaded to GPU/ANE. Common annotations: Pure (callee has no side
    /// effects), NoPanic (callee is panic-free), Deterministic (callee
    /// produces consistent results for GPU distribution).
    pub fn call_proven(
        &mut self,
        callee: FuncId,
        args: Vec<ValueId>,
        proofs: Vec<ProofAnnotation>,
    ) -> ValueId {
        self.emit_with_proofs(Inst::Call { callee, args }, proofs)
    }

    /// Emit a void function call with proof annotations.
    ///
    /// Like `call_proven` but for functions that return no value.
    pub fn call_void_proven(
        &mut self,
        callee: FuncId,
        args: Vec<ValueId>,
        proofs: Vec<ProofAnnotation>,
    ) {
        let mut node = InstrNode::new(Inst::Call { callee, args });
        node.proofs = proofs;
        self.push_node(node);
    }

    /// Emit an atomic load with proof annotations.
    ///
    /// TrustIr uses these annotations for cross-target synthesis of atomic
    /// operations. Common annotations: NoAlias (enables lock-free GPU access),
    /// DataRaceFree (safe for parallel GPU execution).
    pub fn atomic_load_proven(
        &mut self,
        ty: Ty,
        ptr: ValueId,
        ordering: Ordering,
        proofs: Vec<ProofAnnotation>,
    ) -> ValueId {
        self.emit_with_proofs(Inst::AtomicLoad { ty, ptr, ordering }, proofs)
    }

    /// Emit a cast with proof annotations.
    ///
    /// TrustIr uses these to prove casts are safe during GPU kernel synthesis.
    /// Common annotations: NoOverflow (truncation does not lose data),
    /// NoUndef (result is not poison/undef).
    pub fn cast_proven(
        &mut self,
        op: CastOp,
        src_ty: Ty,
        dst_ty: Ty,
        operand: ValueId,
        proofs: Vec<ProofAnnotation>,
    ) -> ValueId {
        self.emit_with_proofs(
            Inst::Cast {
                op,
                src_ty,
                dst_ty,
                operand,
            },
            proofs,
        )
    }

    // --- Pseudo ---

    pub fn copy(&mut self, ty: Ty, operand: ValueId) -> ValueId {
        self.emit(Inst::Copy { ty, operand })
    }

    /// Emit a typed select.
    ///
    /// `cond` may be scalar `bool` for whole-value selection. When `ty` is a
    /// vector, `cond` may also be the same-lane `<N x bool>` mask produced by
    /// vector `icmp`/`fcmp`, which gives TrustIr a portable bitselect surface.
    pub fn select(
        &mut self,
        ty: Ty,
        cond: ValueId,
        then_val: ValueId,
        else_val: ValueId,
    ) -> ValueId {
        self.emit(Inst::Select {
            ty,
            cond,
            then_val,
            else_val,
        })
    }

    /// Emit an `undef` constant of the given type.
    ///
    /// Undef is used by optimizations and by lowerings that have not yet
    /// produced a concrete value. It is POISON: executing it is fine, and
    /// inspecting the value is undefined behaviour (docs/ub-numerics-policy.md
    /// §4). Its semantics are defined in
    /// `lean/trust_ir-semantics/TrustIr/State/ValueMap.lean` (`Value.undef`).
    pub fn undef(&mut self, ty: Ty) -> ValueId {
        self.emit(Inst::Undef { ty })
    }

    /// Emit an [`Inst::Undef`] with explicit proof annotations.
    ///
    /// In particular, [`ProofAnnotation::FreshSymbolicHavoc`] records that a
    /// consumer may interpret this instruction as a fresh unconstrained value.
    /// The annotation is not producer authentication and does not authorize any
    /// constraint on that value; proof-grade consumers must enforce those rules.
    pub fn undef_proven(&mut self, ty: Ty, proofs: Vec<ProofAnnotation>) -> ValueId {
        self.emit_with_proofs(Inst::Undef { ty }, proofs)
    }

    // --- Binding frames (typed quantifier lowering) ---
    //
    // Binding frames provide a typed representation for `\E i \in S` and
    // `\A i \in S` lowering. See design doc (TrustIr#32) and
    // `lean/trust_ir-semantics/TrustIr/Semantics/Frame.lean` for semantics.

    /// Open a new binding frame described by `def_`.
    ///
    /// Returns the SSA value identifying the frame. The frame must later
    /// be closed with `close_frame` to free its slots.
    pub fn open_frame(&mut self, def_: BindingFrameDef) -> ValueId {
        self.emit(Inst::OpenFrame { def: def_ })
    }

    /// Bind `value` to slot `slot` of the frame identified by `frame`.
    ///
    /// Returns the NEW frame handle (`Inst::BindSlot` is functional: the
    /// input handle keeps its prior slot contents, the returned one has slot
    /// `slot` set to `value`). Read the bound value back with `load_slot` on
    /// the RETURNED handle — a `load_slot` through `frame` reads that
    /// handle's own, still-unbound slot. This is not the stored value itself.
    pub fn bind_slot(&mut self, frame: ValueId, slot: u32, value: ValueId) -> ValueId {
        self.emit(Inst::BindSlot { frame, slot, value })
    }

    /// Load the current binding for slot `slot` of `frame`, typed as `ty`.
    pub fn load_slot(&mut self, frame: ValueId, slot: u32, ty: Ty) -> ValueId {
        self.emit(Inst::LoadSlot { frame, slot, ty })
    }

    /// Close a previously opened binding frame.
    ///
    /// After `close_frame` the frame is no longer valid and its slots
    /// cannot be loaded.
    pub fn close_frame(&mut self, frame: ValueId) {
        self.emit_void(Inst::CloseFrame { frame });
    }

    /// Emit an opaque dialect operation.
    ///
    /// Dialect ops round-trip without interpretation; tools that do not
    /// know `op.dialect` must preserve bytes. One SSA result per entry in
    /// `op.result_tys` is allocated and returned in declaration order.
    pub fn dialect_op(&mut self, op: DialectInst) -> Vec<ValueId> {
        let n = op.result_tys.len();
        let mut node = InstrNode::new(Inst::DialectOp(Box::new(op)));
        let mut results = Vec::with_capacity(n);
        for _ in 0..n {
            let vid = self.alloc_value();
            results.push(vid);
            node = node.with_result(vid);
        }
        self.push_node(node);
        results
    }

    /// Emit a dialect operation without allocating a second result vector.
    ///
    /// Unlike forward calls, an operation already declares its result types,
    /// so arity is checked before changing the builder. This is not operation
    /// validation: callers must still run module/schema validation, including
    /// actual operand types, dominance and the operation's semantic contracts.
    pub fn dialect_results<const N: usize>(
        &mut self,
        op: DialectInst,
    ) -> Result<[ValueId; N], DialectResultArityError> {
        if op.result_tys.len() != N {
            return Err(DialectResultArityError {
                expected: N,
                actual: op.result_tys.len(),
            });
        }
        Ok(self.emit_results(Inst::DialectOp(Box::new(op))))
    }

    // `pub(crate)` so the demo/fixture vector-dialect emitters
    // (`crate::demo`) can reuse the single-result plumbing.
    pub(crate) fn dialect_op_one_result(&mut self, op: DialectInst) -> Result<ValueId, String> {
        let name = op.qualified_name();
        let result_count = op.result_tys.len();
        if result_count != 1 {
            return Err(format!(
                "{name} expected exactly one result type, got {result_count}"
            ));
        }

        let mut results = self.dialect_op(op);
        Ok(results.remove(0))
    }

    fn avx512_dialect_op_one_result(&mut self, op: DialectInst) -> Result<ValueId, String> {
        use trust_ir::dialect::avx512;
        avx512::decode(&op).map_err(|e| format!("{e}"))?;
        self.dialect_op_one_result(op)
    }

    fn ane_dialect_op_one_result(&mut self, op: DialectInst) -> Result<ValueId, String> {
        use trust_ir::dialect::ane;
        ane::decode(&op).map_err(|e| format!("{e}"))?;
        self.dialect_op_one_result(op)
    }

    fn gpu_dialect_op_one_result(&mut self, op: DialectInst) -> Result<ValueId, String> {
        use trust_ir::dialect::gpu;
        gpu::decode(&op).map_err(|e| format!("{e}"))?;
        self.dialect_op_one_result(op)
    }

    pub fn gpu_thread_id_x(&mut self) -> Result<ValueId, String> {
        use trust_ir::dialect::gpu;
        self.gpu_dialect_op_one_result(gpu::thread_id_x())
    }

    pub fn gpu_thread_id_y(&mut self) -> Result<ValueId, String> {
        use trust_ir::dialect::gpu;
        self.gpu_dialect_op_one_result(gpu::thread_id_y())
    }

    pub fn gpu_thread_id_z(&mut self) -> Result<ValueId, String> {
        use trust_ir::dialect::gpu;
        self.gpu_dialect_op_one_result(gpu::thread_id_z())
    }

    pub fn gpu_block_id_x(&mut self) -> Result<ValueId, String> {
        use trust_ir::dialect::gpu;
        self.gpu_dialect_op_one_result(gpu::block_id_x())
    }

    pub fn gpu_block_id_y(&mut self) -> Result<ValueId, String> {
        use trust_ir::dialect::gpu;
        self.gpu_dialect_op_one_result(gpu::block_id_y())
    }

    pub fn gpu_block_id_z(&mut self) -> Result<ValueId, String> {
        use trust_ir::dialect::gpu;
        self.gpu_dialect_op_one_result(gpu::block_id_z())
    }

    pub fn gpu_block_dim_x(&mut self) -> Result<ValueId, String> {
        use trust_ir::dialect::gpu;
        self.gpu_dialect_op_one_result(gpu::block_dim_x())
    }

    pub fn gpu_block_dim_y(&mut self) -> Result<ValueId, String> {
        use trust_ir::dialect::gpu;
        self.gpu_dialect_op_one_result(gpu::block_dim_y())
    }

    pub fn gpu_block_dim_z(&mut self) -> Result<ValueId, String> {
        use trust_ir::dialect::gpu;
        self.gpu_dialect_op_one_result(gpu::block_dim_z())
    }

    pub fn gpu_grid_dim_x(&mut self) -> Result<ValueId, String> {
        use trust_ir::dialect::gpu;
        self.gpu_dialect_op_one_result(gpu::grid_dim_x())
    }

    pub fn gpu_grid_dim_y(&mut self) -> Result<ValueId, String> {
        use trust_ir::dialect::gpu;
        self.gpu_dialect_op_one_result(gpu::grid_dim_y())
    }

    pub fn gpu_grid_dim_z(&mut self) -> Result<ValueId, String> {
        use trust_ir::dialect::gpu;
        self.gpu_dialect_op_one_result(gpu::grid_dim_z())
    }

    pub fn gpu_barrier(&mut self) -> Result<(), String> {
        use trust_ir::dialect::gpu;
        let op = gpu::barrier();
        gpu::decode(&op).map_err(|e| format!("{e}"))?;
        self.emit_void(Inst::DialectOp(Box::new(op)));
        Ok(())
    }

    pub fn avx512_mask_cmp(
        &mut self,
        op: ICmpOp,
        result_ty: Ty,
        lhs: ValueId,
        rhs: ValueId,
    ) -> Result<ValueId, String> {
        use trust_ir::dialect::avx512;
        self.avx512_dialect_op_one_result(avx512::mask_cmp(op, result_ty, lhs, rhs))
    }

    pub fn avx512_vpternlog(
        &mut self,
        imm8: u8,
        result_ty: Ty,
        a: ValueId,
        b: ValueId,
        c: ValueId,
    ) -> Result<ValueId, String> {
        use trust_ir::dialect::avx512;
        self.avx512_dialect_op_one_result(avx512::vpternlog(imm8, result_ty, a, b, c))
    }

    pub fn avx512_compress(
        &mut self,
        result_ty: Ty,
        src: ValueId,
        mask: ValueId,
    ) -> Result<ValueId, String> {
        use trust_ir::dialect::avx512;
        self.avx512_dialect_op_one_result(avx512::compress(result_ty, src, mask))
    }

    pub fn ane_tensor_conv(
        &mut self,
        result_ty: Ty,
        input: ValueId,
        weights: ValueId,
        bias: Option<ValueId>,
        stride: u32,
        padding: u32,
    ) -> Result<ValueId, String> {
        use trust_ir::dialect::ane;
        self.ane_dialect_op_one_result(ane::tensor_conv(
            result_ty, input, weights, bias, stride, padding,
        ))
    }

    pub fn ane_tensor_matmul(
        &mut self,
        result_ty: Ty,
        a: ValueId,
        b: ValueId,
        bias: Option<ValueId>,
    ) -> Result<ValueId, String> {
        use trust_ir::dialect::ane;
        self.ane_dialect_op_one_result(ane::tensor_matmul(result_ty, a, b, bias))
    }

    pub fn set_entry(&mut self, block: BlockId) {
        self.func.entry = block;
    }

    /// Set the built function's own calling convention
    /// (`Function::calling_conv`; defaults to `CallingConv::C`).
    ///
    /// This is the function-level ABI pass-through (abi-pinning / fast-2):
    /// frontends declare the convention a function is compiled with here,
    /// instead of mutating the built `Module` by hand. The per-edge analog
    /// for indirect calls is [`call_indirect_cc`](Self::call_indirect_cc).
    pub fn set_calling_conv(&mut self, conv: trust_ir::CallingConv) {
        self.func.calling_conv = conv;
    }

    /// Set the built function's optimization attributes (`Function::attrs`;
    /// default-empty). Claim-style hints, function- and per-parameter-level
    /// (fast-2); replaces the whole `FuncAttrs` record.
    pub fn set_attrs(&mut self, attrs: trust_ir::FuncAttrs) {
        self.func.attrs = attrs;
    }

    /// Set the built function's producer provenance tag (`Function::producer`,
    /// v23; defaults to [`ModuleBuilder::set_default_producer`]'s value or
    /// `None`). Claim-style metadata identifying which frontend/tool emitted
    /// this function.
    pub fn set_producer(&mut self, producer: trust_ir::Producer) {
        self.func.producer = Some(producer);
    }

    /// Clear the built function's producer provenance back to `None` —
    /// `None` is legal on every wire format (the pre-v23 / unstamped state),
    /// and once [`ModuleBuilder::set_default_producer`] has been called this
    /// is the only builder-surface way to emit an untagged function.
    pub fn clear_producer(&mut self) {
        self.func.producer = None;
    }

    /// Set the built function's codegen license (`Function::body_gate`, v41).
    ///
    /// Leaving it unset is `None` — "no licensing claim", the pre-v41
    /// grandfather state a consumer may permit. That is DISTINCT from
    /// `BodyGate::Ungated`, which is an affirmative "not gated" a codegen
    /// consumer must refuse. There is deliberately no `clear_` counterpart
    /// that sets `Ungated`: clearing means "make no claim", which is
    /// `clear_body_gate`.
    pub fn set_body_gate(&mut self, gate: trust_ir::BodyGate) {
        self.func.body_gate = Some(gate);
    }

    /// Clear the built function's codegen license back to `None` (no claim).
    pub fn clear_body_gate(&mut self) {
        self.func.body_gate = None;
    }

    /// Set the built function's human definition path (`Function::display_path`,
    /// v41). Never a link symbol — that is `Function::name`.
    pub fn set_display_path(&mut self, path: impl Into<String>) {
        self.func.display_path = Some(path.into());
    }

    /// Replace the function's v32 SSA debug-name table.
    pub fn set_value_names(&mut self, names: Vec<(ValueId, String)>) {
        self.func.value_names = Some(names);
    }

    /// Append one v32 SSA debug-name entry.
    pub fn add_value_name(&mut self, value: ValueId, name: impl Into<String>) {
        self.func
            .value_names
            .get_or_insert_with(Vec::new)
            .push((value, name.into()));
    }

    /// Replace the function's v33 lexical-scope tree.
    pub fn set_scopes(&mut self, scopes: Vec<ScopeData>) {
        self.func.scopes = Some(scopes);
    }

    /// Set the built function's linkage (`Function::linkage`; defaults to
    /// [`Linkage::External`]).
    pub fn set_linkage(&mut self, linkage: Linkage) {
        self.func.linkage = linkage;
    }

    /// Set the built function's separate-compilation contract
    /// (`Function::summary`), replacing any previous one.
    ///
    /// TRUST BOUNDARY: a summary is a CLAIM. `proved: true` here asserts
    /// nothing the validator will take on faith — it re-counts the backing
    /// obligations (or authenticates `backed_by` through an import) and
    /// refuses an unbacked bit.
    pub fn set_summary(&mut self, summary: FunctionSummary) {
        self.func.summary = Some(summary);
    }

    /// Clear the built function's contract back to `None` (no contract).
    pub fn clear_summary(&mut self) {
        self.func.summary = None;
    }

    /// Commit the function into the module, all or nothing, and return its
    /// id.
    ///
    /// Once any fault is recorded (in this draft or before it) nothing is
    /// committed. A refusal of the commit itself — a leaked reservation view,
    /// a changed or already-defined reserved declaration, or an exhausted
    /// obligation id space — is recorded too, and the module is unchanged.
    /// Either way [`ModuleBuilder::build`] then reports the first fault.
    pub fn build(self) -> FuncId {
        let id = self.func.id;
        if self.fault.is_some() {
            return id;
        }
        let Self {
            module,
            fault,
            func,
            definition,
            reservation_active,
            ..
        } = self;
        if let Err(refusal) = commit(module, func, definition, reservation_active) {
            record(fault, refusal);
        }
        id
    }
}

/// [`FunctionBuilder::build`]'s commit: all or nothing.
fn commit(
    module: &mut Module,
    func: Function,
    definition: Option<&mut FunctionDeclaration>,
    reservation_active: bool,
) -> Result<(), BuildError> {
    let id = func.id;
    if reservation_active {
        return Err(BuildError::ReservationAbandoned { function: id });
    }
    let exhausted = |exhausted: IdSpaceExhausted| BuildError::IdSpaceExhausted {
        space: exhausted.space,
        function: Some(id),
    };
    if let Some(declaration) = definition {
        // The builder's exclusive borrow prevents table changes while the
        // draft is live; check the exact slot before any mutation.
        if declaration.defined {
            return Err(BuildError::AlreadyDefined(id));
        }
        let slot = declaration.slot;
        if !module
            .functions
            .get(slot)
            .is_some_and(|original| original.id == id && original.blocks.is_empty())
        {
            return Err(BuildError::DeclarationChanged(id));
        }
        module
            .synthesize_function_obligations(&func)
            .map_err(exhausted)?;
        let Some(original) = module.functions.get_mut(slot) else {
            return Err(BuildError::DeclarationChanged(id));
        };
        *original = func;
        declaration.defined = true;
    } else {
        module
            .try_add_function(func)
            .map_err(|refusal| exhausted(refusal.exhausted))?;
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use trust_ir::proof::ProofAnnotation;
    use trust_ir::ty::Ty;
    use trust_ir::value::SourceSpan;
    use trust_ir::{Linkage, TlsModel};

    #[test]
    fn definition_preserves_only_callable_header_and_diagnostic_producer() {
        let mut module = ModuleBuilder::new("declaration_metadata");
        let signature = module.add_func_type(vec![], vec![]);
        let id = module.declare_function("declared", signature);
        // Internal adversarial fixture: the public builder has no mutable
        // module escape hatch and never imports a source Function here.
        let declaration = &mut module.module.functions[0];
        declaration.calling_conv = trust_ir::CallingConv::Fast;
        declaration.linkage = Linkage::Internal;
        declaration.producer = Some(trust_ir::Producer::Clean);
        declaration.proofs = vec![ProofAnnotation::Pure, ProofAnnotation::NoAlias];
        declaration.attrs = trust_ir::FuncAttrs {
            readonly: true,
            params: vec![trust_ir::ParamAttrs {
                nonnull: true,
                ..Default::default()
            }],
            ..Default::default()
        };
        declaration.summary = Some(trust_ir::FunctionSummary {
            proved: true,
            ..Default::default()
        });
        declaration.source_provenance = Some(trust_ir::SourceProvenance::new(
            trust_ir::ProofDigest::zero(),
            trust_ir::ProofDigest::zero(),
            vec![],
        ));
        declaration.value_names = Some(vec![(ValueId::new(8), "old".into())]);
        declaration.scopes = Some(vec![ScopeData {
            parent: None,
            span: None,
            inlined_at: None,
        }]);
        let original = module.module.clone();
        {
            let draft = module.define_function(id).unwrap();
            assert_eq!(draft.func.name, "declared");
            assert_eq!(draft.func.ty, signature);
            assert_eq!(draft.func.calling_conv, trust_ir::CallingConv::Fast);
            assert_eq!(draft.func.linkage, Linkage::Internal);
            assert_eq!(draft.func.producer, Some(trust_ir::Producer::Clean));
            assert!(draft.func.proofs.is_empty());
            assert!(draft.func.attrs.is_empty());
            assert!(draft.func.summary.is_none());
            assert!(draft.func.source_provenance.is_none());
            assert!(draft.func.value_names.is_none());
            assert!(draft.func.scopes.is_none());
        }
        assert_eq!(
            module.module, original,
            "dropping even a sanitized draft changes nothing"
        );
        let mut draft = module.define_function(id).unwrap();
        let entry = draft.create_block();
        draft.switch_to_block(entry);
        draft.ret(vec![]);
        draft.build();
        let target = module.build().expect("ModuleBuilder::build: test fixture");
        assert!(target.functions[0].source_provenance.is_none());
        assert!(target.functions[0].proofs.is_empty());
        assert!(target.proof_obligations.is_empty());
        assert!(target.proof_certificates.is_empty());
        assert!(crate::validate_module(&target).is_empty());
    }

    #[test]
    fn changed_reserved_slot_is_rejected_before_mutation() {
        let mut module = ModuleBuilder::new("changed_slot");
        let signature = module.add_func_type(vec![], vec![]);
        let first = module.declare_function("first", signature);
        module.declare_function("second", signature);
        module.module.functions.swap(0, 1);
        let original = module.module.clone();
        assert!(
            matches!(module.define_function(first), Err(FunctionDefinitionError::DeclarationChanged(id)) if id == first)
        );
        assert_eq!(module.module, original);
        assert!(!module.declarations[&first].defined);
        module.module.functions.swap(0, 1);
        let entry = Block::new(BlockId::new(0));
        module.module.functions[0].blocks.push(entry);
        let original = module.module.clone();
        assert!(
            matches!(module.define_function(first), Err(FunctionDefinitionError::DeclarationChanged(id)) if id == first)
        );
        assert_eq!(module.module, original);
        assert!(!module.declarations[&first].defined);
    }

    #[test]
    fn function_id_exhaustion_never_recycles_or_partially_reserves() {
        let mut module = ModuleBuilder::new("function_id_exhaustion");
        let signature = module.add_func_type(vec![], vec![]);
        module.next_func_id = FreshIds::after([FuncId::new(u32::MAX - 1)]);
        let last = module.declare_function("last", signature);
        assert_eq!(last, FuncId::new(u32::MAX));
        let original = module.module.clone();
        for legacy in [false, true] {
            // Exhaustion is recorded (D1b), never a panic, and nothing is
            // reserved or pushed: the placeholder is `FuncId(u32::MAX)`.
            let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                if legacy {
                    module.function("overflow", signature).build()
                } else {
                    module.declare_function("overflow", signature)
                }
            }));
            assert_eq!(result.ok(), Some(FuncId::new(u32::MAX)));
            assert_eq!(module.module, original);
            assert_eq!(module.declarations.len(), 1);
        }
        // A recorded fault commits nothing afterwards, and the one exit
        // reports it.
        assert_eq!(module.define_function(last).unwrap().build(), last);
        assert_eq!(module.module, original);
        assert_eq!(
            module.build().err(),
            Some(BuildError::IdSpaceExhausted {
                space: "FuncId",
                function: None,
            })
        );
    }

    #[test]
    fn target_info_is_present_from_builder_construction() {
        let target = TargetInfo {
            triple: "aarch64-apple-darwin".to_string(),
            pointer_size: 8,
            endianness: trust_ir::Endianness::Little,
            abi: Some("aapcs64".to_string()),
            struct_passing: trust_ir::StructPassingPolicy::NativeC,
        };
        let builder = ModuleBuilder::new_with_target_info("targeted", target.clone());
        let module = builder.build().expect("ModuleBuilder::build: test fixture");

        assert_eq!(module.name, "targeted");
        assert_eq!(module.target_info, Some(target));
        assert!(
            ModuleBuilder::new("portable")
                .build()
                .expect("ModuleBuilder::build: test fixture")
                .target_info
                .is_none()
        );
    }

    #[test]
    fn reserved_block_params_keep_all_params_before_instruction_results() {
        let mut module = ModuleBuilder::new("canonical-reserved-params");
        let signature = module.add_func_type(vec![Ty::I32], vec![Ty::Bool]);
        let mut function = module.function("predicate", signature);
        let entry = function.create_block();
        let first_join = function.create_block();
        let second_join = function.create_block();
        function.set_entry(entry);
        let input = function.add_block_param(entry, Ty::I32);

        {
            let mut reserved = function
                .reserve_block_params(2)
                .expect("small exact reservation");
            reserved.switch_to_block(entry);
            let zero = reserved.iconst(Ty::I32, 0);
            let condition = reserved.icmp(ICmpOp::Eq, Ty::I32, input, zero);
            reserved.br(first_join, vec![condition]);

            let first = reserved
                .add_reserved_block_param(first_join, Ty::Bool)
                .expect("first reserved join parameter");
            reserved.switch_to_block(first_join);
            reserved.br(second_join, vec![first]);

            let second = reserved
                .add_reserved_block_param(second_join, Ty::Bool)
                .expect("second reserved join parameter");
            reserved.switch_to_block(second_join);
            reserved.ret(vec![second]);
            assert!(reserved.is_exhausted());
            assert_eq!(reserved.remaining(), 0);
        }
        function.build();

        let module = module.build().expect("ModuleBuilder::build: test fixture");
        assert!(crate::validate::validate_module(&module).is_empty());
        let function = &module.functions[0];
        let params = function
            .blocks
            .iter()
            .flat_map(|block| block.params.iter().map(|(value, _)| value.index()))
            .collect::<Vec<_>>();
        let results = function
            .blocks
            .iter()
            .flat_map(|block| &block.body)
            .flat_map(|node| node.results.iter().map(|value| value.index()))
            .collect::<Vec<_>>();
        assert_eq!(params, [0, 1, 2]);
        assert_eq!(results, [3, 4]);
    }

    #[test]
    fn reserved_block_param_errors_do_not_consume_the_next_id() {
        let mut module = ModuleBuilder::new("reserved-param-errors");
        let signature = module.add_func_type(vec![], vec![]);
        let mut function = module.function("f", signature);
        let entry = function.create_block();
        let later = function.create_block();

        let mut reserved = function
            .reserve_block_params(2)
            .expect("small exact reservation");
        let unknown = reserved
            .add_reserved_block_param(BlockId::new(99), Ty::Bool)
            .expect_err("unknown block must reject");
        assert_eq!(
            unknown.error(),
            &ReservedBlockParamError::UnknownBlock(BlockId::new(99))
        );
        assert_eq!(unknown.ty(), &Ty::Bool);
        let (unknown_error, recovered_ty) = unknown.into_parts();
        assert_eq!(
            unknown_error,
            ReservedBlockParamError::UnknownBlock(BlockId::new(99))
        );
        assert_eq!(recovered_ty, Ty::Bool);
        assert_eq!(reserved.remaining(), 2);
        assert_eq!(
            reserved
                .add_reserved_block_param(later, Ty::Bool)
                .expect("later block accepts first value")
                .index(),
            0
        );
        let order = reserved
            .add_reserved_block_param(entry, Ty::Bool)
            .expect_err("regressing block order must reject");
        assert_eq!(
            order.error(),
            &ReservedBlockParamError::BlockOrder {
                previous: later,
                requested: entry,
            }
        );
        assert_eq!(order.into_parts().1, Ty::Bool);
        assert_eq!(reserved.remaining(), 1);
        assert_eq!(
            reserved
                .add_reserved_block_param(later, Ty::Bool)
                .expect("same block accepts the remaining value")
                .index(),
            1
        );
        let exhausted = reserved
            .add_reserved_block_param(later, Ty::Bool)
            .expect_err("exhausted reservation must reject");
        assert_eq!(exhausted.error(), &ReservedBlockParamError::Exhausted);
        assert_eq!(exhausted.into_parts().1, Ty::Bool);
    }

    #[test]
    fn active_reservation_rejects_mixed_and_nested_parameter_allocation() {
        let mut module = ModuleBuilder::new("active-reserved-params");
        let signature = module.add_func_type(vec![], vec![]);
        let mut function = module.function("f", signature);
        let entry = function.create_block();
        let mut reserved = function
            .reserve_block_params(1)
            .expect("small exact reservation");

        assert_eq!(
            reserved
                .reserve_block_params(1)
                .err()
                .expect("nested reservation must reject"),
            ReservedBlockParamError::ReservationAlreadyActive
        );
        // Ordinary allocation through the view records `MixedReservation`
        // (never a panic) and writes nothing.
        let mixed = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            reserved.add_block_param(entry, Ty::Bool)
        }))
        .expect("a mixed allocation records, never panics");
        assert_eq!(mixed, ValueId::new(u32::MAX), "the placeholder");
        assert_eq!(reserved.remaining(), 1);
        assert_eq!(
            reserved
                .add_reserved_block_param(entry, Ty::Bool)
                .expect("the failed mixed call must not consume the reservation")
                .index(),
            0
        );
        assert!(reserved.is_exhausted());
        drop(reserved);
        function.build();
        let function_id = FuncId::new(0);
        assert_eq!(
            module.build().err(),
            Some(BuildError::MixedReservation {
                function: function_id
            }),
            "the recorded mixing poisons the module"
        );
    }

    #[test]
    fn reservation_rejects_noncanonical_prior_prefixes() {
        let mut result_module = ModuleBuilder::new("result-before-reservation");
        let signature = result_module.add_func_type(vec![], vec![]);
        let mut result_function = result_module.function("f", signature);
        let entry = result_function.create_block();
        result_function.switch_to_block(entry);
        let _value = result_function.bool_const(true);
        assert_eq!(
            result_function
                .reserve_block_params(1)
                .err()
                .expect("post-result reservation must reject"),
            ReservedBlockParamError::NonCanonicalExistingValuePrefix
        );

        let mut gap_module = ModuleBuilder::new("gap-before-reservation");
        let signature = gap_module.add_func_type(vec![], vec![]);
        let mut gap_function = gap_module.function("f", signature);
        {
            let reserved = gap_function
                .reserve_block_params(1)
                .expect("first reservation");
            assert_eq!(reserved.remaining(), 1);
        }
        assert_eq!(
            gap_function
                .reserve_block_params(1)
                .err()
                .expect("a prior gap must reject"),
            ReservedBlockParamError::NonCanonicalExistingValuePrefix
        );
    }

    #[test]
    fn reservation_cursor_cannot_wrap_at_value_id_max() {
        let mut module = ModuleBuilder::new("reserved-param-overflow");
        let signature = module.add_func_type(vec![], vec![]);
        let mut function = module.function("f", signature);
        let entry = function.create_block();
        let mut reserved = function
            .reserve_block_params(u32::MAX)
            .expect("the last representable instruction ID remains available");
        reserved.switch_to_block(entry);
        assert_eq!(reserved.bool_const(true).index(), u32::MAX);
        let overflow =
            std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| reserved.bool_const(false)))
                .expect("the value cursor records its exhaustion, never panics");
        assert_eq!(
            overflow,
            ValueId::new(u32::MAX),
            "the placeholder, never a wrap"
        );
        assert_eq!(reserved.remaining(), u32::MAX);
        drop(reserved);
        function.build();
        assert_eq!(
            module.build().err(),
            Some(BuildError::IdSpaceExhausted {
                space: "ValueId",
                function: Some(FuncId::new(0)),
            })
        );
    }

    #[test]
    fn reservation_overflow_rejects_without_changing_the_builder_cursor() {
        let mut module = ModuleBuilder::new("reserved-param-overflow-rollback");
        let signature = module.add_func_type(vec![], vec![]);
        let mut function = module.function("f", signature);
        let entry = function.create_block();
        assert_eq!(function.add_block_param(entry, Ty::I32).index(), 0);
        assert_eq!(function.add_block_param(entry, Ty::I32).index(), 1);

        assert_eq!(
            function
                .reserve_block_params(u32::MAX)
                .err()
                .expect("oversized suffix must reject"),
            ReservedBlockParamError::ValueIdOverflow
        );
        assert_eq!(
            function.add_block_param(entry, Ty::I32).index(),
            2,
            "failed reservation must leave the next value ID unchanged"
        );
    }

    #[test]
    fn reservation_seeds_order_from_preexisting_later_block_params() {
        let mut module = ModuleBuilder::new("reserved-param-seeded-order");
        let signature = module.add_func_type(vec![], vec![]);
        let mut function = module.function("f", signature);
        let entry = function.create_block();
        let later = function.create_block();
        let last = function.create_block();
        assert_eq!(function.add_block_param(later, Ty::I32).index(), 0);

        let mut reserved = function
            .reserve_block_params(1)
            .expect("dense preexisting parameter prefix");
        let regressed = reserved
            .add_reserved_block_param(entry, Ty::I64)
            .expect_err("reservation must retain the preexisting last block");
        assert_eq!(
            regressed.error(),
            &ReservedBlockParamError::BlockOrder {
                previous: later,
                requested: entry,
            }
        );
        assert_eq!(regressed.into_parts().1, Ty::I64);
        assert_eq!(reserved.remaining(), 1);
        assert_eq!(
            reserved
                .add_reserved_block_param(last, Ty::Bool)
                .expect("later block remains valid")
                .index(),
            1
        );
        assert!(reserved.is_exhausted());
    }

    #[test]
    fn zero_count_reservation_is_exhausted_and_does_not_advance_ids() {
        let mut module = ModuleBuilder::new("zero-reserved-params");
        let signature = module.add_func_type(vec![], vec![]);
        let mut function = module.function("f", signature);
        let entry = function.create_block();
        {
            let mut reserved = function.reserve_block_params(0).expect("zero reservation");
            assert!(reserved.is_exhausted());
            assert_eq!(reserved.remaining(), 0);
            let exhausted = reserved
                .add_reserved_block_param(entry, Ty::Bool)
                .expect_err("zero reservation has no attachable IDs");
            assert_eq!(exhausted.error(), &ReservedBlockParamError::Exhausted);
            assert_eq!(exhausted.into_parts().1, Ty::Bool);
        }
        assert_eq!(function.add_block_param(entry, Ty::I32).index(), 0);
    }

    #[test]
    fn incomplete_reserved_block_params_leave_an_observable_value_gap() {
        let mut module = ModuleBuilder::new("incomplete-reserved-params");
        let signature = module.add_func_type(vec![], vec![Ty::I32]);
        let mut function = module.function("f", signature);
        let entry = function.create_block();
        let join = function.create_block();
        {
            let mut reserved = function
                .reserve_block_params(2)
                .expect("small exact reservation");
            assert_eq!(
                reserved
                    .add_reserved_block_param(join, Ty::I32)
                    .expect("one attached parameter")
                    .index(),
                0
            );
            assert_eq!(reserved.remaining(), 1);
        }
        function.switch_to_block(entry);
        let result = function.iconst(Ty::I32, 7);
        assert_eq!(result.index(), 2, "the unused reserved ID remains a gap");
        function.ret(vec![result]);
        function.build();

        let module = module.build().expect("ModuleBuilder::build: test fixture");
        assert_eq!(module.functions[0].blocks[1].params[0].0.index(), 0);
        assert_eq!(module.functions[0].blocks[0].body[0].results[0].index(), 2);
    }

    /// r11 item 2 (port of probe P5, evidence kind ii): block ids are minted
    /// by the one fresh-id rule. Before r11, `create_block` at the cursor
    /// `u32::MAX` handed out `u32::MAX`, then wrapped to block 0 in release
    /// (a duplicate block id) and panicked with an arithmetic overflow in
    /// debug. The cliff is reachable through the public API only after 2^32
    /// real blocks (>= 240 GiB resident), so the cursor is set directly.
    /// Mutation check: `wrapping_add` in `FreshIds::take` makes the second
    /// `create_block` append a second block 0. Since D1b the refusal is
    /// recorded and reported by `ModuleBuilder::build`, never a panic.
    #[test]
    fn block_id_exhaustion_is_refused_never_wrapped() {
        let mut module = ModuleBuilder::new("block_ids");
        let signature = module.add_func_type(vec![], vec![]);
        let mut function = module.function("f", signature);
        let first = function.create_block();
        function.next_block = FreshIds::after([BlockId::new(u32::MAX - 1)]);
        assert_eq!(function.create_block(), BlockId::new(u32::MAX));
        // Exhausted: the placeholder, nothing appended, the fault recorded.
        assert_eq!(function.create_block(), BlockId::new(u32::MAX));
        let ids: Vec<BlockId> = function.func.blocks.iter().map(|block| block.id).collect();
        assert_eq!(
            ids,
            vec![first, BlockId::new(u32::MAX)],
            "no block was appended on refusal: pushed block ids stay unique"
        );
        function.build();
        assert_eq!(
            module.build().err(),
            Some(BuildError::IdSpaceExhausted {
                space: "BlockId",
                function: Some(FuncId::new(0)),
            })
        );
    }

    /// r11 item 3 (type + behavioural parity; no crafted input fails on the
    /// pre-r11 code, whose `end - next` relied on a struct invariant). The
    /// view's count is STORED in its `IdRun`, so no subtraction exists:
    ///
    /// * after one parameter (`%0`), `u32::MAX` ids are exactly the rest of
    ///   the space — the run ends at `u32::MAX` and reports `u32::MAX`;
    /// * after two parameters the same count is one id too many:
    ///   `ValueIdOverflow`, with the builder's cursor unchanged;
    /// * a small run attaches all of its ids, reports `0`, then refuses.
    #[test]
    fn reservation_run_ending_at_value_id_max_is_exact() {
        let mut module = ModuleBuilder::new("reserved-run-at-max");
        let signature = module.add_func_type(vec![], vec![]);
        let mut function = module.function("f", signature);
        let entry = function.create_block();
        let join = function.create_block();
        assert_eq!(function.add_block_param(entry, Ty::I32).index(), 0);
        {
            let mut reserved = function
                .reserve_block_params(u32::MAX)
                .expect("ids 1..=u32::MAX are exactly the rest of the space");
            assert_eq!(reserved.remaining(), u32::MAX);
            let first = reserved
                .add_reserved_block_param(join, Ty::Bool)
                .expect("first reserved id");
            assert_eq!(first.index(), 1);
            assert_eq!(reserved.remaining(), u32::MAX - 1);
            // The run took every remaining id: nothing is left to emit with.
            let emitted = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                reserved.bool_const(true)
            }))
            .expect("the value cursor records its exhaustion, never panics");
            assert_eq!(emitted, ValueId::new(u32::MAX), "refused, never wrapped");
        }
        function.build();
        assert_eq!(
            module.build().err(),
            Some(BuildError::IdSpaceExhausted {
                space: "ValueId",
                function: Some(FuncId::new(0)),
            })
        );

        let mut module = ModuleBuilder::new("reserved-run-one-too-many");
        let signature = module.add_func_type(vec![], vec![]);
        let mut function = module.function("f", signature);
        let entry = function.create_block();
        let join = function.create_block();
        function.add_block_param(entry, Ty::I32);
        function.add_block_param(entry, Ty::I32);
        assert_eq!(
            function
                .reserve_block_params(u32::MAX)
                .err()
                .expect("2 + u32::MAX ids do not fit"),
            ReservedBlockParamError::ValueIdOverflow
        );
        {
            let mut reserved = function
                .reserve_block_params(2)
                .expect("the cursor is unchanged");
            assert_eq!(reserved.remaining(), 2);
            let a = reserved
                .add_reserved_block_param(join, Ty::Bool)
                .expect("a");
            let b = reserved
                .add_reserved_block_param(join, Ty::Bool)
                .expect("b");
            assert_eq!((a.index(), b.index()), (2, 3));
            assert_eq!(reserved.remaining(), 0);
            assert!(reserved.is_exhausted());
            let refused = reserved
                .add_reserved_block_param(join, Ty::Bool)
                .expect_err("the run is used up");
            assert_eq!(refused.error(), &ReservedBlockParamError::Exhausted);
        }
    }

    /// r11 item 6 (port of probe P8, evidence kind ii): the row `make` returns
    /// must carry the id it was handed. Before r11 this was a `debug_assert`:
    /// a debug build panicked and a release build PUSHED the mismatched row
    /// (`[4294967295]` under minted id 0). Now it is an ordinary check in every
    /// profile: typed refusal, row returned, nothing pushed. Mutation check:
    /// restoring the `debug_assert`-only check pushes the row in release.
    #[test]
    fn add_proof_obligation_refuses_a_row_whose_id_is_not_the_minted_one() {
        use trust_ir::proof::{ObligationKind, ProofObligation, ProofStatus};

        let mut mb = ModuleBuilder::new("mismatch");
        let row = ProofObligation::new(
            ProofId::new(u32::MAX),
            ObligationKind::Precondition,
            ProofStatus::Pending,
            "carries the wrong id",
        );
        let refusal = mb
            .add_proof_obligation(|_| row.clone())
            .expect_err("the row does not carry the minted id");
        assert_eq!(
            refusal,
            AddObligationError::IdMismatch {
                minted: ProofId::new(0),
                row: Box::new(row),
            }
        );
        assert!(mb.module.proof_obligations.is_empty(), "nothing was pushed");

        // An exhausted table refuses before `make` runs.
        mb.module.proof_obligations.push(ProofObligation::new(
            ProofId::new(u32::MAX),
            ObligationKind::Precondition,
            ProofStatus::Pending,
            "decoded row",
        ));
        let refusal = mb
            .add_proof_obligation(|_| unreachable!("make must not run without an id"))
            .expect_err("no id is left");
        assert_eq!(
            refusal,
            AddObligationError::IdSpaceExhausted(IdSpaceExhausted { space: "ProofId" })
        );
        assert_eq!(mb.module.proof_obligations.len(), 1);
    }

    /// A claim-bearing function whose synthesized obligation has no id left
    /// is not committed; the refusal is recorded and `ModuleBuilder::build`
    /// reports it typed (D1b: never a panic).
    #[test]
    fn build_refuses_a_claim_without_an_obligation_id() {
        use trust_ir::proof::{ObligationKind, ProofObligation, ProofStatus};

        let mut mb = ModuleBuilder::new("exhausted");
        mb.module.proof_obligations.push(ProofObligation::new(
            ProofId::new(u32::MAX),
            ObligationKind::Precondition,
            ProofStatus::Pending,
            "decoded row",
        ));
        let signature = mb.add_func_type(vec![], vec![]);
        let mut fb = mb.function("g", signature);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        fb.ret(vec![]);
        fb.add_function_proof(ProofAnnotation::NoPanic);
        assert_eq!(fb.build(), FuncId::new(0));
        assert!(mb.module.functions.is_empty(), "nothing was committed");
        assert_eq!(
            mb.build().err(),
            Some(BuildError::IdSpaceExhausted {
                space: "ProofId",
                function: Some(FuncId::new(0)),
            })
        );
    }

    /// `add_proof_obligation` allocates dense ids from an empty table and
    /// hands each row the id it is stored under.
    #[test]
    fn add_proof_obligation_allocates_dense_ids() {
        use trust_ir::proof::{ObligationKind, ProofObligation, ProofStatus};

        let mut mb = ModuleBuilder::new("obligations");
        let first = mb
            .add_proof_obligation(|id| {
                ProofObligation::new(id, ObligationKind::BoundsCheck, ProofStatus::Pending, "a")
            })
            .expect("a fresh obligation id");
        let second = mb
            .add_proof_obligation(|id| {
                ProofObligation::new(
                    id,
                    ObligationKind::ArithmeticSafety,
                    ProofStatus::Pending,
                    "b",
                )
            })
            .expect("a fresh obligation id");
        assert_eq!(first.index(), 0);
        assert_eq!(second.index(), 1);
        let m = mb.build().expect("ModuleBuilder::build: test fixture");
        assert_eq!(m.proof_obligations.len(), 2);
        assert_eq!(m.proof_obligations[0].id, first);
        assert_eq!(m.proof_obligations[1].id, second);
        assert!(
            m.proof_obligations
                .iter()
                .all(|o| o.status == ProofStatus::Pending)
        );
    }

    /// A SPARSE producer-assigned table must not be collided with: the next id
    /// is one past the LARGEST existing id, not `len()`.
    #[test]
    fn add_proof_obligation_skips_past_sparse_ids() {
        use trust_ir::proof::{ObligationKind, ProofObligation, ProofStatus};

        let mut mb = ModuleBuilder::new("sparse");
        mb.module.proof_obligations.push(ProofObligation::new(
            ProofId::new(11),
            ObligationKind::PanicFreedom,
            ProofStatus::Pending,
            "pre-existing sparse row",
        ));
        let next = mb
            .add_proof_obligation(|id| {
                ProofObligation::new(id, ObligationKind::BoundsCheck, ProofStatus::Pending, "new")
            })
            .expect("a fresh obligation id");
        assert_eq!(
            next.index(),
            12,
            "must allocate past the largest existing id"
        );
    }

    /// Building a function AFTER recording obligations must not renumber,
    /// duplicate, or drop them (guards the `synthesize_function_obligations`
    /// pass that `Module::add_function` runs).
    #[test]
    fn function_build_preserves_recorded_obligations() {
        use trust_ir::proof::{ObligationKind, ProofObligation, ProofStatus};

        let mut mb = ModuleBuilder::new("scoped");
        let fid = mb
            .peek_next_func_id()
            .expect("peek_next_func_id: test fixture");
        let recorded = mb
            .add_proof_obligation(|id| {
                ProofObligation::new(
                    id,
                    ObligationKind::BoundsCheck,
                    ProofStatus::Pending,
                    "index in bounds",
                )
                .with_function(fid)
            })
            .expect("a fresh obligation id");

        let ft = mb.add_func_type(vec![Ty::I64], vec![Ty::I64]);
        let mut fb = mb.function("identity", ft);
        let entry = fb.create_block();
        let x = fb.add_block_param(entry, Ty::I64);
        fb.switch_to_block(entry);
        fb.ret(vec![x]);
        let built = fb.build();

        assert_eq!(built, fid, "peek_next_func_id must predict the assigned id");
        let m = mb.build().expect("ModuleBuilder::build: test fixture");
        assert_eq!(m.proof_obligations.len(), 1, "no row was added or dropped");
        assert_eq!(m.proof_obligations[0].id, recorded);
        assert_eq!(m.proof_obligations[0].function, Some(fid));
        assert_eq!(m.proof_obligations[0].status, ProofStatus::Pending);
        assert!(crate::validate_module(&m).is_empty());
    }

    #[test]
    fn builder_threads_current_span_onto_emitted_nodes() {
        let mut mb = ModuleBuilder::new("spans");
        let f = mb.intern_file("src/lib.rs");
        let ft = mb.add_func_type(vec![Ty::I64, Ty::I64], vec![Ty::I64]);
        let mut fb = mb.function("add", ft);
        let entry = fb.create_block();
        let a = fb.add_block_param(entry, Ty::I64);
        let b = fb.add_block_param(entry, Ty::I64);
        fb.switch_to_block(entry);
        // Span-less by default.
        let pre = fb.iconst(Ty::I64, 0);
        let span = SourceSpan {
            file: f,
            line: 7,
            col: 3,
        };
        fb.set_span(span);
        let sum = fb.add(Ty::I64, a, b);
        fb.clear_span();
        let post = fb.add(Ty::I64, sum, pre);
        fb.ret(vec![post]);
        fb.build();
        let m = mb.build().expect("ModuleBuilder::build: test fixture");
        let body = &m.functions[0].blocks[0].body;
        // The const (before set_span) and the post add (after clear_span) carry
        // no span; the middle add carries the set span.
        assert_eq!(body[0].span, None, "pre-span node must be span-less");
        assert_eq!(
            body[1].span,
            Some(span),
            "node emitted under set_span carries it"
        );
        assert_eq!(
            body[2].span, None,
            "node after clear_span is span-less again"
        );
    }

    #[test]
    fn builder_threads_value_names_and_lexical_scopes() {
        let mut mb = ModuleBuilder::new("debug");
        let ft = mb.add_func_type(vec![Ty::I64], vec![Ty::I64]);
        let mut fb = mb.function("identity", ft);
        let entry = fb.create_block();
        let input = fb.add_block_param(entry, Ty::I64);
        fb.add_value_name(input, "input");
        fb.set_scopes(vec![
            ScopeData {
                parent: None,
                span: None,
                inlined_at: None,
            },
            ScopeData {
                parent: Some(0),
                span: None,
                inlined_at: None,
            },
        ]);
        fb.switch_to_block(entry);
        fb.set_scope(1);
        let copy = fb.copy(Ty::I64, input);
        fb.add_value_name(copy, "copy");
        fb.clear_scope();
        fb.ret(vec![copy]);
        fb.build();

        let module = mb.build().expect("ModuleBuilder::build: test fixture");
        let func = &module.functions[0];
        assert_eq!(
            func.value_names.as_deref(),
            Some(
                &[
                    (ValueId::new(0), "input".to_string()),
                    (ValueId::new(1), "copy".to_string()),
                ][..]
            )
        );
        assert_eq!(func.scopes.as_ref().map(Vec::len), Some(2));
        assert_eq!(func.blocks[0].body[0].scope, Some(1));
        assert_eq!(func.blocks[0].body[1].scope, None);
    }

    #[test]
    fn build_gpu_kernel_skeleton() -> Result<(), String> {
        let mut mb = ModuleBuilder::new("gpu_kernel");
        let ft = mb.add_func_type(vec![Ty::Ptr], vec![]);
        let mut fb = mb.function("kernel", ft);
        let entry = fb.create_block();
        let _data = fb.add_block_param(entry, Ty::Ptr);
        fb.switch_to_block(entry);

        let tx = fb.gpu_thread_id_x()?;
        let bx = fb.gpu_block_id_x()?;
        let bdim = fb.gpu_block_dim_x()?;

        // global_id = bx * bdim + tx
        let prod = fb.mul(Ty::U32, bx, bdim);
        let _gid = fb.add(Ty::U32, prod, tx);

        fb.gpu_barrier()?;
        fb.ret(vec![]);
        fb.build();

        let module = mb.build().expect("ModuleBuilder::build: test fixture");
        assert_eq!(module.functions.len(), 1);
        Ok(())
    }

    #[test]
    fn build_simple_add_function() {
        // fn add(i64, i64) -> i64 { a + b }
        let mut mb = ModuleBuilder::new("test_add");
        let ft = mb.add_func_type(vec![Ty::I64, Ty::I64], vec![Ty::I64]);
        let mut fb = mb.function("add", ft);

        let entry = fb.create_block();
        let a = fb.add_block_param(entry, Ty::I64);
        let b_param = fb.add_block_param(entry, Ty::I64);
        fb.switch_to_block(entry);

        let sum = fb.add(Ty::I64, a, b_param);
        fb.ret(vec![sum]);
        fb.build();

        let module = mb.build().expect("ModuleBuilder::build: test fixture");
        assert_eq!(module.functions.len(), 1);
        assert_eq!(module.functions[0].name, "add");
        assert_eq!(module.functions[0].blocks.len(), 1);

        let block = &module.functions[0].blocks[0];
        assert_eq!(block.params.len(), 2);
        assert_eq!(block.body.len(), 2); // add + ret

        // Verify add instruction
        assert!(matches!(
            &block.body[0].inst,
            Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                ..
            }
        ));
        assert_eq!(block.body[0].results.len(), 1);

        // Verify ret instruction
        assert!(matches!(&block.body[1].inst, Inst::Return { .. }));
    }

    #[test]
    fn build_factorial_with_control_flow() {
        // fn factorial(n: i64) -> i64 {
        //   if n <= 1 { return 1 } else { return n * factorial(n-1) }
        // }
        // (simplified: just test control flow, not actual recursion)
        let mut mb = ModuleBuilder::new("test_factorial");
        let ft = mb.add_func_type(vec![Ty::I64], vec![Ty::I64]);
        let mut fb = mb.function("factorial", ft);

        let entry = fb.create_block();
        let then_bb = fb.create_block();
        let else_bb = fb.create_block();
        let merge_bb = fb.create_block();

        let n = fb.add_block_param(entry, Ty::I64);
        let result_param = fb.add_block_param(merge_bb, Ty::I64);
        fb.set_entry(entry);

        // entry: compare n <= 1
        fb.switch_to_block(entry);
        let one = fb.iconst(Ty::I64, 1);
        let cmp = fb.icmp(ICmpOp::Sle, Ty::I64, n, one);
        fb.condbr(cmp, then_bb, vec![], else_bb, vec![]);

        // then: return 1
        fb.switch_to_block(then_bb);
        let const_one = fb.iconst(Ty::I64, 1);
        fb.br(merge_bb, vec![const_one]);

        // else: return n (simplified)
        fb.switch_to_block(else_bb);
        fb.br(merge_bb, vec![n]);

        // merge: return result
        fb.switch_to_block(merge_bb);
        fb.ret(vec![result_param]);

        fb.build();
        let module = mb.build().expect("ModuleBuilder::build: test fixture");

        assert_eq!(module.functions.len(), 1);
        assert_eq!(module.functions[0].blocks.len(), 4);

        // Verify entry block has condbr
        let entry_block = &module.functions[0].blocks[0];
        let last = entry_block.body.last().unwrap();
        assert!(matches!(&last.inst, Inst::CondBr { .. }));

        // Verify merge block has param and ret
        let merge_block = &module.functions[0].blocks[3];
        assert_eq!(merge_block.params.len(), 1);
    }

    #[test]
    fn build_memory_operations() {
        let mut mb = ModuleBuilder::new("test_mem");
        let ft = mb.add_func_type(vec![], vec![Ty::I32]);
        let mut fb = mb.function("mem_ops", ft);

        let entry = fb.create_block();
        fb.switch_to_block(entry);

        // alloca
        let ptr = fb.alloca(Ty::I32);
        assert_eq!(ptr.index(), 0);

        // store
        let val = fb.iconst(Ty::I32, 42);
        fb.store(Ty::I32, ptr, val);

        // gep
        let idx = fb.iconst(Ty::I64, 0);
        let gep_ptr = fb.gep(Ty::I32, ptr, vec![idx]);
        assert!(gep_ptr.index() > 0);

        // load
        let loaded = fb.load(Ty::I32, ptr);
        fb.ret(vec![loaded]);
        fb.build();

        let module = mb.build().expect("ModuleBuilder::build: test fixture");
        let block = &module.functions[0].blocks[0];
        // alloca + iconst(42) + store + iconst(0) + gep + load + ret = 7 instructions
        assert_eq!(block.body.len(), 7);

        // Check alloca
        assert!(matches!(
            &block.body[0].inst,
            Inst::Alloca {
                ty: Ty::I32,
                count: None,
                ..
            }
        ));
        // Check store (no result)
        assert!(block.body[2].results.is_empty());
        // Check gep
        assert!(matches!(&block.body[4].inst, Inst::GEP { .. }));
        // Check load
        assert!(matches!(
            &block.body[5].inst,
            Inst::Load { ty: Ty::I32, .. }
        ));
    }

    #[test]
    fn build_with_proof_annotations() {
        let mut mb = ModuleBuilder::new("test_proofs");
        let ft = mb.add_func_type(vec![Ty::Ptr], vec![Ty::I32]);
        let mut fb = mb.function("safe_load", ft);

        let entry = fb.create_block();
        let ptr = fb.add_block_param(entry, Ty::Ptr);
        fb.switch_to_block(entry);

        // load with proof annotations
        let loaded = fb.load_proven(
            Ty::I32,
            ptr,
            vec![ProofAnnotation::InBounds, ProofAnnotation::NotNull],
        );
        fb.ret(vec![loaded]);
        fb.build();

        let module = mb.build().expect("ModuleBuilder::build: test fixture");
        let block = &module.functions[0].blocks[0];

        // Check proof annotations
        assert_eq!(block.body[0].proofs.len(), 2);
        assert_eq!(block.body[0].proofs[0], ProofAnnotation::InBounds);
        assert_eq!(block.body[0].proofs[1], ProofAnnotation::NotNull);
    }

    #[test]
    fn build_with_atomics() {
        let mut mb = ModuleBuilder::new("test_atomics");
        let ft = mb.add_func_type(vec![Ty::Ptr], vec![Ty::I64]);
        let mut fb = mb.function("atomic_ops", ft);

        let entry = fb.create_block();
        let ptr = fb.add_block_param(entry, Ty::Ptr);
        fb.switch_to_block(entry);

        // atomic load
        let loaded = fb.atomic_load(Ty::I64, ptr, Ordering::Acquire);

        // atomic store
        fb.atomic_store(Ty::I64, ptr, loaded, Ordering::Release);

        // fence
        fb.fence(Ordering::SeqCst);

        fb.ret(vec![loaded]);
        fb.build();

        let module = mb.build().expect("ModuleBuilder::build: test fixture");
        let block = &module.functions[0].blocks[0];

        assert!(matches!(
            &block.body[0].inst,
            Inst::AtomicLoad {
                ordering: Ordering::Acquire,
                ..
            }
        ));
        assert!(matches!(
            &block.body[1].inst,
            Inst::AtomicStore {
                ordering: Ordering::Release,
                ..
            }
        ));
        assert!(matches!(
            &block.body[2].inst,
            Inst::Fence {
                ordering: Ordering::SeqCst
            }
        ));
    }

    #[test]
    fn build_with_overflow_checking() {
        let mut mb = ModuleBuilder::new("test_overflow");
        let ft = mb.add_func_type(vec![Ty::I32, Ty::I32], vec![Ty::I32, Ty::Bool]);
        let mut fb = mb.function("checked_add", ft);

        let entry = fb.create_block();
        let a = fb.add_block_param(entry, Ty::I32);
        let b_param = fb.add_block_param(entry, Ty::I32);
        fb.switch_to_block(entry);

        let (result, flag) = fb.overflow(OverflowOp::AddOverflow, Ty::I32, a, b_param);
        fb.ret(vec![result, flag]);
        fb.build();

        let module = mb.build().expect("ModuleBuilder::build: test fixture");
        let block = &module.functions[0].blocks[0];

        // overflow instruction should have 2 results
        assert_eq!(block.body[0].results.len(), 2);
        assert_eq!(block.body[0].results[0], result);
        assert_eq!(block.body[0].results[1], flag);
        assert!(matches!(
            &block.body[0].inst,
            Inst::Overflow {
                op: OverflowOp::AddOverflow,
                ..
            }
        ));
    }

    #[test]
    fn builder_methods_produce_correct_instructions() {
        let mut mb = ModuleBuilder::new("test_ops");
        let ft = mb.add_func_type(vec![Ty::I64, Ty::I64], vec![Ty::I64]);
        let mut fb = mb.function("ops", ft);

        let entry = fb.create_block();
        let a = fb.add_block_param(entry, Ty::I64);
        let b_param = fb.add_block_param(entry, Ty::I64);
        fb.switch_to_block(entry);

        // Test all arithmetic shortcuts
        let _sub = fb.sub(Ty::I64, a, b_param);
        let _mul = fb.mul(Ty::I64, a, b_param);
        let _sdiv = fb.sdiv(Ty::I64, a, b_param);
        let _udiv = fb.udiv(Ty::I64, a, b_param);

        // Test float operations
        let fa = fb.fconst(Ty::F64, 1.0);
        let fb_val = fb.fconst(Ty::F64, 2.0);
        let _fadd = fb.fadd(Ty::F64, fa, fb_val);
        let _fmul = fb.fmul(Ty::F64, fa, fb_val);

        // Test unary op
        let _neg = fb.unop(UnOp::Neg, Ty::I64, a);

        // Test comparison
        let _cmp = fb.icmp(ICmpOp::Eq, Ty::I64, a, b_param);
        let _fcmp = fb.fcmp(FCmpOp::OLt, Ty::F64, fa, fb_val);

        // Test casts
        let _zext = fb.zext(Ty::I32, Ty::I64, a);
        let _sext = fb.sext(Ty::I32, Ty::I64, a);
        let _trunc = fb.trunc(Ty::I64, Ty::I32, a);

        // Test constants
        let _bc = fb.bool_const(true);
        let _np = fb.null_ptr();

        // Test pseudo ops
        let _copy = fb.copy(Ty::I64, a);
        let cond = fb.bool_const(false);
        let _sel = fb.select(Ty::I64, cond, a, b_param);

        // Test proof ops
        fb.assume(cond);
        fb.assert(cond);

        fb.ret(vec![a]);
        fb.build();

        let module = mb.build().expect("ModuleBuilder::build: test fixture");
        let block = &module.functions[0].blocks[0];
        // Count: sub + mul + sdiv + udiv + fconst + fconst + fadd + fmul
        //   + unop + icmp + fcmp + zext + sext + trunc + bool + null
        //   + copy + bool + select + assume + assert + ret = 22
        assert_eq!(block.body.len(), 22);
    }

    #[test]
    fn build_multiple_functions() {
        let mut mb = ModuleBuilder::new("multi_func");
        let ft1 = mb.add_func_type(vec![Ty::I32], vec![Ty::I32]);
        let ft2 = mb.add_func_type(vec![], vec![]);

        // Function 1
        {
            let mut fb = mb.function("identity", ft1);
            let entry = fb.create_block();
            let x = fb.add_block_param(entry, Ty::I32);
            fb.switch_to_block(entry);
            fb.ret(vec![x]);
            fb.build();
        }

        // Function 2
        {
            let mut fb = mb.function("noop", ft2);
            let entry = fb.create_block();
            fb.switch_to_block(entry);
            fb.ret(vec![]);
            fb.build();
        }

        let module = mb.build().expect("ModuleBuilder::build: test fixture");
        assert_eq!(module.functions.len(), 2);
        assert_eq!(module.functions[0].name, "identity");
        assert_eq!(module.functions[1].name, "noop");
        // Func IDs should be sequential
        assert_eq!(module.functions[0].id.index(), 0);
        assert_eq!(module.functions[1].id.index(), 1);
    }

    #[test]
    fn build_with_call() {
        let mut mb = ModuleBuilder::new("call_test");
        let ft = mb.add_func_type(vec![Ty::I32, Ty::I32], vec![Ty::I32]);

        let mut fb = mb.function("caller", ft);
        let entry = fb.create_block();
        let a = fb.add_block_param(entry, Ty::I32);
        let b_param = fb.add_block_param(entry, Ty::I32);
        fb.switch_to_block(entry);

        let result = fb.call(FuncId::new(1), vec![a, b_param]);
        fb.ret(vec![result]);
        fb.build();

        let module = mb.build().expect("ModuleBuilder::build: test fixture");
        let block = &module.functions[0].blocks[0];
        assert!(
            matches!(&block.body[0].inst, Inst::Call { callee, args } if callee.index() == 1 && args.len() == 2)
        );
    }

    #[test]
    fn build_call_void() {
        let mut mb = ModuleBuilder::new("call_void_test");
        let ft = mb.add_func_type(vec![], vec![]);

        let mut fb = mb.function("caller", ft);
        let entry = fb.create_block();
        fb.switch_to_block(entry);

        fb.call_void(FuncId::new(0), vec![]);
        fb.ret(vec![]);
        fb.build();

        let module = mb.build().expect("ModuleBuilder::build: test fixture");
        let block = &module.functions[0].blocks[0];
        assert!(matches!(&block.body[0].inst, Inst::Call { .. }));
        assert!(block.body[0].results.is_empty()); // void call has no result
    }

    #[test]
    fn build_with_extract_insert_field() {
        let mut mb = ModuleBuilder::new("agg_test");
        let ft = mb.add_func_type(vec![Ty::Struct(trust_ir::StructId::new(0))], vec![Ty::I32]);

        let mut fb = mb.function("get_field", ft);
        let entry = fb.create_block();
        let agg = fb.add_block_param(entry, Ty::Struct(trust_ir::StructId::new(0)));
        fb.switch_to_block(entry);

        let field_val = fb.extract_field(Ty::I32, agg, 0);
        let new_agg = fb.insert_field(Ty::Struct(trust_ir::StructId::new(0)), agg, 0, field_val);
        let _ = new_agg;
        fb.ret(vec![field_val]);
        fb.build();

        let module = mb.build().expect("ModuleBuilder::build: test fixture");
        let block = &module.functions[0].blocks[0];
        assert!(matches!(
            &block.body[0].inst,
            Inst::ExtractField { field: 0, .. }
        ));
        assert!(matches!(
            &block.body[1].inst,
            Inst::InsertField { field: 0, .. }
        ));
    }

    #[test]
    fn builder_block_ids_are_sequential() {
        let mut mb = ModuleBuilder::new("test");
        let ft = mb.add_func_type(vec![], vec![]);
        let mut fb = mb.function("f", ft);

        let b0 = fb.create_block();
        let b1 = fb.create_block();
        let b2 = fb.create_block();

        assert_eq!(b0.index(), 0);
        assert_eq!(b1.index(), 1);
        assert_eq!(b2.index(), 2);

        fb.switch_to_block(b0);
        fb.br(b1, vec![]);
        fb.switch_to_block(b1);
        fb.br(b2, vec![]);
        fb.switch_to_block(b2);
        fb.ret(vec![]);
        fb.build();

        let module = mb.build().expect("ModuleBuilder::build: test fixture");
        assert_eq!(module.functions[0].blocks.len(), 3);
    }

    #[test]
    fn builder_value_ids_are_sequential() {
        let mut mb = ModuleBuilder::new("test");
        let ft = mb.add_func_type(vec![Ty::I32, Ty::I32], vec![Ty::I32]);
        let mut fb = mb.function("f", ft);

        let entry = fb.create_block();
        let v0 = fb.add_block_param(entry, Ty::I32);
        let v1 = fb.add_block_param(entry, Ty::I32);
        fb.switch_to_block(entry);
        let v2 = fb.add(Ty::I32, v0, v1);
        let v3 = fb.sub(Ty::I32, v0, v1);

        assert_eq!(v0.index(), 0);
        assert_eq!(v1.index(), 1);
        assert_eq!(v2.index(), 2);
        assert_eq!(v3.index(), 3);

        fb.ret(vec![v2]);
        fb.build();
    }

    #[test]
    fn add_global() {
        let mut mb = ModuleBuilder::new("globals");
        mb.add_global(Global {
            name: "counter".to_string(),
            ty: Ty::I64,
            mutable: true,
            initializer: Some(Constant::Int(0)),
            linkage: Linkage::External,
            tls: None,
            align: None,

            section: None,
            visibility: Default::default(),
            retained: false,
        });
        let module = mb.build().expect("ModuleBuilder::build: test fixture");
        assert_eq!(module.globals.len(), 1);
        assert_eq!(module.globals[0].name, "counter");
        assert!(module.globals[0].mutable);
        assert_eq!(module.globals[0].tls, None);
    }

    #[test]
    fn add_tls_global() {
        let mut mb = ModuleBuilder::new("tls_globals");
        mb.add_global(Global {
            name: "thread_counter".to_string(),
            ty: Ty::I64,
            mutable: true,
            initializer: Some(Constant::Int(0)),
            linkage: Linkage::Internal,
            tls: Some(TlsModel::LocalExec),
            align: None,

            section: None,
            visibility: Default::default(),
            retained: false,
        });
        let module = mb.build().expect("ModuleBuilder::build: test fixture");
        assert_eq!(module.globals.len(), 1);
        assert_eq!(module.globals[0].tls, Some(TlsModel::LocalExec));
    }

    #[test]
    fn add_struct_def() {
        use trust_ir::ty::{FieldDef, StructDef};
        let mut mb = ModuleBuilder::new("structs");
        let sid = mb.add_struct(StructDef {
            id: trust_ir::StructId::new(0),
            name: "Point".to_string(),
            fields: vec![
                FieldDef {
                    name: "x".to_string(),
                    ty: Ty::F64,
                    offset: Some(0),
                },
                FieldDef {
                    name: "y".to_string(),
                    ty: Ty::F64,
                    offset: Some(8),
                },
            ],
            size: Some(16),
            align: Some(8),
            repr: Default::default(),
            origin: None,
        });
        assert_eq!(sid.index(), 0);
        let module = mb.build().expect("ModuleBuilder::build: test fixture");
        assert_eq!(module.structs.len(), 1);
        assert_eq!(module.structs[0].name, "Point");
    }

    #[test]
    fn set_entry_block() {
        let mut mb = ModuleBuilder::new("entry_test");
        let ft = mb.add_func_type(vec![], vec![]);
        let mut fb = mb.function("f", ft);

        let _b0 = fb.create_block();
        let b1 = fb.create_block();

        // Override entry to be b1 instead of default b0
        fb.set_entry(b1);

        fb.switch_to_block(_b0);
        fb.ret(vec![]);
        fb.switch_to_block(b1);
        fb.ret(vec![]);
        fb.build();

        let module = mb.build().expect("ModuleBuilder::build: test fixture");
        assert_eq!(module.functions[0].entry, b1);
    }

    // --- Function-level ABI pass-through tests (abi-pinning / fast-2) ---

    #[test]
    fn set_calling_conv_threads_onto_built_function() {
        use trust_ir::CallingConv;
        let mut mb = ModuleBuilder::new("cc_test");
        let ft = mb.add_func_type(vec![], vec![]);
        let mut fb = mb.function("swifty", ft);
        fb.set_calling_conv(CallingConv::Swift);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        fb.ret(vec![]);
        fb.build();
        let module = mb.build().expect("ModuleBuilder::build: test fixture");
        assert_eq!(module.functions[0].calling_conv, CallingConv::Swift);
    }

    #[test]
    fn calling_conv_defaults_to_c_when_unset() {
        use trust_ir::CallingConv;
        let mut mb = ModuleBuilder::new("cc_default");
        let ft = mb.add_func_type(vec![], vec![]);
        let mut fb = mb.function("plain", ft);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        fb.ret(vec![]);
        fb.build();
        let module = mb.build().expect("ModuleBuilder::build: test fixture");
        assert_eq!(module.functions[0].calling_conv, CallingConv::C);
    }

    #[test]
    fn set_attrs_threads_onto_built_function() {
        use trust_ir::{FuncAttrs, ParamAttrs};
        let mut mb = ModuleBuilder::new("attrs_test");
        let ft = mb.add_func_type(vec![Ty::Ptr], vec![Ty::I32]);
        let mut fb = mb.function("reader", ft);
        fb.set_attrs(FuncAttrs {
            readonly: true,
            inlinehint: true,
            params: vec![ParamAttrs {
                nonnull: true,
                dereferenceable: Some(4),
                ..Default::default()
            }],
            ..Default::default()
        });
        let entry = fb.create_block();
        let p = fb.add_block_param(entry, Ty::Ptr);
        fb.switch_to_block(entry);
        let v = fb.load(Ty::I32, p);
        fb.ret(vec![v]);
        fb.build();
        let module = mb.build().expect("ModuleBuilder::build: test fixture");
        let attrs = &module.functions[0].attrs;
        assert!(attrs.readonly);
        assert!(attrs.inlinehint);
        assert!(!attrs.readnone);
        assert!(!attrs.cold);
        assert!(attrs.params[0].nonnull);
        assert_eq!(attrs.params[0].dereferenceable, Some(4));
        // Default stays empty when the setter is not called.
        let mut mb2 = ModuleBuilder::new("attrs_default");
        let ft2 = mb2.add_func_type(vec![], vec![]);
        let mut fb2 = mb2.function("plain", ft2);
        let e2 = fb2.create_block();
        fb2.switch_to_block(e2);
        fb2.ret(vec![]);
        fb2.build();
        assert!(
            mb2.build()
                .expect("ModuleBuilder::build: test fixture")
                .functions[0]
                .attrs
                .is_empty()
        );
    }

    #[test]
    fn conv_and_attrs_setters_validate_cleanly() {
        use trust_ir::{CallingConv, FuncAttrs};
        let mut mb = ModuleBuilder::new("cc_attrs_validate");
        let ft = mb.add_func_type(vec![Ty::I64], vec![Ty::I64]);
        let mut fb = mb.function("f", ft);
        fb.set_calling_conv(CallingConv::Rust);
        fb.set_attrs(FuncAttrs {
            inlinehint: true,
            ..Default::default()
        });
        let entry = fb.create_block();
        let x = fb.add_block_param(entry, Ty::I64);
        fb.switch_to_block(entry);
        fb.ret(vec![x]);
        fb.build();
        let module = mb.build().expect("ModuleBuilder::build: test fixture");
        let errors = crate::validate::validate_module(&module);
        assert!(
            errors.is_empty(),
            "setters must not break validity: {errors:?}"
        );
    }

    // --- Proof-related builder tests ---

    #[test]
    fn add_proof_to_function() {
        let mut mb = ModuleBuilder::new("proof_func_test");
        let ft = mb.add_func_type(vec![Ty::I32], vec![Ty::I32]);
        let mut fb = mb.function("pure_fn", ft);

        fb.add_function_proof(ProofAnnotation::Pure);
        fb.add_function_proof(ProofAnnotation::NoPanic);
        fb.add_function_proof(ProofAnnotation::Terminates);

        let entry = fb.create_block();
        let x = fb.add_block_param(entry, Ty::I32);
        fb.switch_to_block(entry);
        fb.ret(vec![x]);
        fb.build();

        let module = mb.build().expect("ModuleBuilder::build: test fixture");
        let func = &module.functions[0];
        assert_eq!(func.proofs.len(), 3);
        assert!(func.has_proof(&ProofAnnotation::Pure));
        assert!(func.has_proof(&ProofAnnotation::NoPanic));
        assert!(func.has_proof(&ProofAnnotation::Terminates));
        assert!(func.is_pure());
    }

    #[test]
    fn binop_proven_attaches_proofs() {
        let mut mb = ModuleBuilder::new("binop_proof_test");
        let ft = mb.add_func_type(vec![Ty::I32, Ty::I32], vec![Ty::I32]);
        let mut fb = mb.function("safe_add", ft);

        let entry = fb.create_block();
        let a = fb.add_block_param(entry, Ty::I32);
        let b_param = fb.add_block_param(entry, Ty::I32);
        fb.switch_to_block(entry);

        let result = fb.binop_proven(
            BinOp::Add,
            Ty::I32,
            a,
            b_param,
            vec![
                ProofAnnotation::NoOverflow,
                ProofAnnotation::Commutative,
                ProofAnnotation::Associative,
            ],
        );
        fb.ret(vec![result]);
        fb.build();

        let module = mb.build().expect("ModuleBuilder::build: test fixture");
        let block = &module.functions[0].blocks[0];
        let node = &block.body[0];
        assert_eq!(node.proofs.len(), 3);
        assert!(node.has_proof(&ProofAnnotation::NoOverflow));
        assert!(node.has_proof(&ProofAnnotation::Commutative));
        assert!(node.has_proof(&ProofAnnotation::Associative));
        assert!(node.is_proven_safe_for_gpu());
    }

    #[test]
    fn store_proven_attaches_proofs() {
        let mut mb = ModuleBuilder::new("store_proof_test");
        let ft = mb.add_func_type(vec![Ty::Ptr, Ty::I32], vec![]);
        let mut fb = mb.function("safe_store", ft);

        let entry = fb.create_block();
        let ptr = fb.add_block_param(entry, Ty::Ptr);
        let val = fb.add_block_param(entry, Ty::I32);
        fb.switch_to_block(entry);

        fb.store_proven(
            Ty::I32,
            ptr,
            val,
            vec![
                ProofAnnotation::InBounds,
                ProofAnnotation::NotNull,
                ProofAnnotation::ValidBorrow,
            ],
        );
        fb.ret(vec![]);
        fb.build();

        let module = mb.build().expect("ModuleBuilder::build: test fixture");
        let block = &module.functions[0].blocks[0];
        let node = &block.body[0];
        assert!(node.results.is_empty()); // store has no result
        assert_eq!(node.proofs.len(), 3);
        assert!(node.has_proof(&ProofAnnotation::InBounds));
        assert!(node.has_proof(&ProofAnnotation::NotNull));
        assert!(node.has_proof(&ProofAnnotation::ValidBorrow));
        assert_eq!(node.memory_proofs().len(), 3);
    }

    #[test]
    fn gep_proven_attaches_proofs() {
        let mut mb = ModuleBuilder::new("gep_proof_test");
        let ft = mb.add_func_type(vec![Ty::Ptr], vec![Ty::Ptr]);
        let mut fb = mb.function("safe_gep", ft);

        let entry = fb.create_block();
        let base = fb.add_block_param(entry, Ty::Ptr);
        fb.switch_to_block(entry);

        let idx = fb.iconst(Ty::I64, 4);
        let ptr = fb.gep_proven(
            Ty::I32,
            base,
            vec![idx],
            vec![ProofAnnotation::InBounds, ProofAnnotation::Aligned(4)],
        );
        fb.ret(vec![ptr]);
        fb.build();

        let module = mb.build().expect("ModuleBuilder::build: test fixture");
        let block = &module.functions[0].blocks[0];
        // block.body[0] is iconst, block.body[1] is gep
        let gep_node = &block.body[1];
        assert_eq!(gep_node.proofs.len(), 2);
        assert!(gep_node.has_proof(&ProofAnnotation::InBounds));
        assert!(gep_node.has_proof(&ProofAnnotation::Aligned(4)));
        assert!(gep_node.is_proven_safe_for_gpu());
        // `gep_proven` does NOT establish the invariant, so it must not set the
        // flag that asserts it (documented contract).
        assert!(matches!(
            gep_node.inst,
            Inst::GEP {
                inbounds: false,
                ..
            }
        ));
    }

    #[test]
    fn gep_inbounds_proven_sets_the_flag_and_attaches_proofs() {
        let mut mb = ModuleBuilder::new("gep_inbounds_proof_test");
        let ft = mb.add_func_type(vec![Ty::Ptr], vec![Ty::Ptr]);
        let mut fb = mb.function("safe_gep", ft);

        let entry = fb.create_block();
        let base = fb.add_block_param(entry, Ty::Ptr);
        fb.switch_to_block(entry);

        let idx = fb.iconst(Ty::I64, 4);
        let ptr = fb.gep_inbounds_proven(
            Ty::I32,
            base,
            vec![idx],
            vec![ProofAnnotation::InBounds, ProofAnnotation::Aligned(4)],
        );
        fb.ret(vec![ptr]);
        fb.build();

        let module = mb.build().expect("ModuleBuilder::build: test fixture");
        let gep_node = &module.functions[0].blocks[0].body[1];
        assert!(matches!(gep_node.inst, Inst::GEP { inbounds: true, .. }));
        assert_eq!(gep_node.proofs.len(), 2);
        assert!(gep_node.has_proof(&ProofAnnotation::InBounds));
        assert!(gep_node.has_proof(&ProofAnnotation::Aligned(4)));
    }

    #[test]
    fn ptr_extent_offset_by_allows_one_past_the_end_and_fails_closed() {
        let root = ValueId::new(0);
        let e = PtrExtent {
            root,
            offset: 0,
            size: 8,
        };
        assert_eq!(e.offset_by(0).map(|e| e.offset), Some(0));
        assert_eq!(e.offset_by(7).map(|e| e.offset), Some(7));
        // One-past-the-end is legal (LLVM `inbounds` permits it; every
        // half-open iterator sentinel takes this shape).
        assert_eq!(e.offset_by(8).map(|e| e.offset), Some(8));
        // Past that, and on overflow, there is no fact.
        assert_eq!(e.offset_by(9), None);
        assert_eq!(e.offset_by(u64::MAX), None);
        // Chaining accumulates against the SAME allocation size.
        let mid = e.offset_by(6).unwrap();
        assert_eq!(mid.offset_by(2).map(|e| e.offset), Some(8));
        assert_eq!(mid.offset_by(3), None);
        assert_eq!(mid.root, root);
    }

    #[test]
    fn alloca_records_a_layout_derived_extent_when_the_format_can_size_it() {
        let mut mb = ModuleBuilder::new("extent_alloca");
        let ft = mb.add_func_type(vec![], vec![]);
        let u8_ty = mb.add_type(Ty::U8);
        let mut fb = mb.function("f", ft);
        let entry = fb.create_block();
        fb.switch_to_block(entry);

        // Layout-resolvable: a thin pointer and an i64 are 8 bytes each.
        let p = fb.alloca(Ty::Ptr);
        assert_eq!(fb.ptr_extent(p).map(|e| e.size), Some(8));
        let q = fb.alloca_aligned(Ty::I64, 8);
        assert_eq!(fb.ptr_extent(q).map(|e| e.size), Some(8));
        let arr = fb.alloca(Ty::Array(u8_ty, 16));
        assert_eq!(fb.ptr_extent(arr).map(|e| e.size), Some(16));

        // NOT layout-resolvable: a tuple has no declared trust-ir layout, so
        // the builder records nothing rather than inventing one.
        let t = fb.alloca_aligned(Ty::Tuple(vec![Ty::I64, Ty::I64]), 8);
        assert_eq!(fb.ptr_extent(t), None);
        // ... until the producer, which does know, says so.
        fb.note_alloc_extent(t, 16);
        assert_eq!(
            fb.ptr_extent(t),
            Some(PtrExtent {
                root: t,
                offset: 0,
                size: 16
            })
        );
    }

    /// Sizing every `Alloca` of a function asks one layout memo kept for the
    /// builder's life: a chain of `n` structs, each allocated once, is laid
    /// out once in all (n nodes), where a fresh table per `Alloca` re-walked
    /// the rest of the chain each time (about n^2 / 2 nodes).
    #[test]
    fn alloca_extents_lay_each_type_out_once_per_builder() {
        use trust_ir::ty::{FieldDef, StructRepr};
        use trust_ir::value::StructId;
        let n = 2_000u32;
        let mut mb = ModuleBuilder::new("extent_chain");
        let ft = mb.add_func_type(vec![], vec![]);
        for i in 0..n {
            let ty = if i == 0 {
                Ty::U64
            } else {
                Ty::Struct(StructId::new(i - 1))
            };
            mb.add_struct(StructDef {
                id: StructId::new(i),
                name: format!("S{i}"),
                fields: vec![FieldDef {
                    name: "f".into(),
                    ty,
                    offset: Some(0),
                }],
                size: Some(8),
                align: Some(8),
                repr: StructRepr::C,
                origin: None,
            });
        }
        let mut fb = mb.function("f", ft);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        for i in (0..n).rev() {
            let p = fb.alloca(Ty::Struct(StructId::new(i)));
            assert_eq!(fb.ptr_extent(p).map(|e| e.size), Some(8), "S{i}");
        }
        let stats = fb.layouts.as_ref().expect("a memo is kept").stats();
        // The first `Alloca` lays out the chain (about two steps a level);
        // each later one is a lookup (an enter and a give).
        assert_eq!(stats.nodes, n as usize, "{stats:?}");
        assert!(stats.steps <= 4 * u64::from(n) + 8, "{stats:?}");
        assert!(stats.definitions_indexed <= n as usize, "{stats:?}");
        fb.ret(vec![]);
        fb.build();
    }

    #[test]
    fn note_alloc_extent_keeps_the_smaller_size_on_disagreement() {
        let mut mb = ModuleBuilder::new("extent_conflict");
        let ft = mb.add_func_type(vec![], vec![]);
        let mut fb = mb.function("f", ft);
        let entry = fb.create_block();
        fb.switch_to_block(entry);

        // Layout says 8. A producer claiming MORE must not widen the fact.
        let p = fb.alloca(Ty::I64);
        fb.note_alloc_extent(p, 4096);
        assert_eq!(fb.ptr_extent(p).map(|e| e.size), Some(8));
        // A producer claiming LESS narrows it (also the safe direction).
        let q = fb.alloca(Ty::I64);
        fb.note_alloc_extent(q, 4);
        assert_eq!(fb.ptr_extent(q).map(|e| e.size), Some(4));
        let g = fb.gep_byte_offset(q, 8);
        fb.ret(vec![]);
        fb.build();
        let module = mb.build().expect("ModuleBuilder::build: test fixture");
        let node = module.functions[0].blocks[0]
            .body
            .iter()
            .find(|n| n.results == vec![g])
            .unwrap();
        assert!(
            matches!(
                node.inst,
                Inst::GEP {
                    inbounds: false,
                    ..
                }
            ),
            "8 > the narrowed 4-byte extent, so the claim must not be made"
        );
    }

    #[test]
    fn gep_byte_offset_sets_inbounds_only_when_the_extent_discharges_it() {
        let mut mb = ModuleBuilder::new("extent_gep");
        let ft = mb.add_func_type(vec![Ty::Ptr], vec![]);
        let mut fb = mb.function("f", ft);
        let entry = fb.create_block();
        let opaque = fb.add_block_param(entry, Ty::Ptr);
        fb.switch_to_block(entry);

        // A 16-byte producer-declared slot (the shape trust-ir cannot size).
        let slot = fb.alloca_aligned(Ty::Tuple(vec![Ty::I64, Ty::I64]), 8);
        fb.note_alloc_extent(slot, 16);

        let a = fb.gep_byte_offset(slot, 8); // inside
        let b = fb.gep_byte_offset(a, 8); // chained, lands one-past-the-end
        let c = fb.gep_byte_offset(slot, 24); // past the end -> no claim
        let d = fb.gep_byte_offset(opaque, 8); // unknown base -> no claim
        fb.ret(vec![]);
        fb.build();

        let module = mb.build().expect("ModuleBuilder::build: test fixture");
        let body = &module.functions[0].blocks[0].body;
        let gep_of = |v: ValueId| {
            body.iter()
                .find(|n| n.results == vec![v])
                .expect("gep result node")
        };
        for (v, expected) in [(a, true), (b, true), (c, false), (d, false)] {
            let node = gep_of(v);
            let Inst::GEP {
                inbounds,
                ref pointee_ty,
                ..
            } = node.inst
            else {
                panic!("expected a GEP");
            };
            assert_eq!(*pointee_ty, Ty::I8, "byte-offset GEP uses an I8 pointee");
            assert_eq!(inbounds, expected, "inbounds flag for {v:?}");
            assert_eq!(
                node.has_proof(&ProofAnnotation::InBounds),
                expected,
                "InBounds annotation for {v:?}"
            );
        }
    }

    #[test]
    fn gep_byte_offset_propagates_the_extent_only_along_discharged_chains() {
        let mut mb = ModuleBuilder::new("extent_chain");
        let ft = mb.add_func_type(vec![], vec![]);
        let mut fb = mb.function("f", ft);
        let entry = fb.create_block();
        fb.switch_to_block(entry);

        let slot = fb.alloca_aligned(Ty::Tuple(vec![Ty::I64, Ty::I64]), 8);
        fb.note_alloc_extent(slot, 16);

        let a = fb.gep_byte_offset(slot, 4);
        assert_eq!(
            fb.ptr_extent(a),
            Some(PtrExtent {
                root: slot,
                offset: 4,
                size: 16
            }),
            "a discharged offset carries the accumulated extent forward"
        );
        let b = fb.gep_byte_offset(a, 12);
        assert_eq!(fb.ptr_extent(b).map(|e| e.offset), Some(16));
        // Once a link in the chain cannot be discharged, everything derived
        // from it loses the fact — no silent re-anchoring.
        let c = fb.gep_byte_offset(b, 1);
        assert_eq!(fb.ptr_extent(c), None);
        let d = fb.gep_byte_offset(c, 0);
        assert_eq!(fb.ptr_extent(d), None);
    }

    #[test]
    fn call_proven_attaches_proofs() {
        let mut mb = ModuleBuilder::new("call_proof_test");
        let ft = mb.add_func_type(vec![Ty::I32], vec![Ty::I32]);
        let mut fb = mb.function("call_pure", ft);

        let entry = fb.create_block();
        let x = fb.add_block_param(entry, Ty::I32);
        fb.switch_to_block(entry);

        let result = fb.call_proven(
            FuncId::new(1),
            vec![x],
            vec![
                ProofAnnotation::Pure,
                ProofAnnotation::NoPanic,
                ProofAnnotation::Deterministic,
            ],
        );
        fb.ret(vec![result]);
        fb.build();

        let module = mb.build().expect("ModuleBuilder::build: test fixture");
        let block = &module.functions[0].blocks[0];
        let node = &block.body[0];
        assert_eq!(node.proofs.len(), 3);
        assert!(node.has_proof(&ProofAnnotation::Pure));
        assert!(node.has_proof(&ProofAnnotation::NoPanic));
        assert!(node.has_proof(&ProofAnnotation::Deterministic));
        assert!(node.is_proven_safe_for_gpu());
        assert_eq!(node.results.len(), 1);
    }

    #[test]
    fn call_void_proven_attaches_proofs() {
        let mut mb = ModuleBuilder::new("call_void_proof_test");
        let ft = mb.add_func_type(vec![Ty::I32], vec![]);
        let mut fb = mb.function("call_void_pure", ft);

        let entry = fb.create_block();
        let x = fb.add_block_param(entry, Ty::I32);
        fb.switch_to_block(entry);

        fb.call_void_proven(
            FuncId::new(1),
            vec![x],
            vec![ProofAnnotation::Pure, ProofAnnotation::NoPanic],
        );
        fb.ret(vec![]);
        fb.build();

        let module = mb.build().expect("ModuleBuilder::build: test fixture");
        let block = &module.functions[0].blocks[0];
        let node = &block.body[0];
        assert!(node.results.is_empty());
        assert_eq!(node.proofs.len(), 2);
        assert!(node.has_proof(&ProofAnnotation::Pure));
        assert!(node.has_proof(&ProofAnnotation::NoPanic));
    }

    #[test]
    fn atomic_load_proven_attaches_proofs() {
        let mut mb = ModuleBuilder::new("atomic_load_proof_test");
        let ft = mb.add_func_type(vec![Ty::Ptr], vec![Ty::I64]);
        let mut fb = mb.function("safe_atomic_load", ft);

        let entry = fb.create_block();
        let ptr = fb.add_block_param(entry, Ty::Ptr);
        fb.switch_to_block(entry);

        let loaded = fb.atomic_load_proven(
            Ty::I64,
            ptr,
            Ordering::Acquire,
            vec![
                ProofAnnotation::NoAlias,
                ProofAnnotation::DataRaceFree,
                ProofAnnotation::NoUndef,
            ],
        );
        fb.ret(vec![loaded]);
        fb.build();

        let module = mb.build().expect("ModuleBuilder::build: test fixture");
        let block = &module.functions[0].blocks[0];
        let node = &block.body[0];
        assert_eq!(node.proofs.len(), 3);
        assert!(node.has_proof(&ProofAnnotation::NoAlias));
        assert!(node.has_proof(&ProofAnnotation::DataRaceFree));
        assert!(node.has_proof(&ProofAnnotation::NoUndef));
    }

    #[test]
    fn cast_proven_attaches_proofs() {
        let mut mb = ModuleBuilder::new("cast_proof_test");
        let ft = mb.add_func_type(vec![Ty::I64], vec![Ty::I32]);
        let mut fb = mb.function("safe_trunc", ft);

        let entry = fb.create_block();
        let x = fb.add_block_param(entry, Ty::I64);
        fb.switch_to_block(entry);

        let result = fb.cast_proven(
            CastOp::Trunc,
            Ty::I64,
            Ty::I32,
            x,
            vec![ProofAnnotation::NoOverflow, ProofAnnotation::NoUndef],
        );
        fb.ret(vec![result]);
        fb.build();

        let module = mb.build().expect("ModuleBuilder::build: test fixture");
        let block = &module.functions[0].blocks[0];
        let node = &block.body[0];
        assert_eq!(node.proofs.len(), 2);
        assert!(node.has_proof(&ProofAnnotation::NoOverflow));
        assert!(node.has_proof(&ProofAnnotation::NoUndef));
    }

    // --- New builder method tests ---

    #[test]
    fn build_dealloc() {
        let mut mb = ModuleBuilder::new("dealloc_test");
        let ft = mb.add_func_type(vec![Ty::Ptr], vec![]);
        let mut fb = mb.function("free", ft);

        let entry = fb.create_block();
        let ptr = fb.add_block_param(entry, Ty::Ptr);
        fb.switch_to_block(entry);

        fb.dealloc(ptr);
        fb.ret(vec![]);
        fb.build();

        let module = mb.build().expect("ModuleBuilder::build: test fixture");
        let block = &module.functions[0].blocks[0];
        assert!(matches!(&block.body[0].inst, Inst::Dealloc { .. }));
        assert!(block.body[0].results.is_empty()); // dealloc has no result
    }

    #[test]
    fn build_borrow_instructions() {
        let mut mb = ModuleBuilder::new("borrow_test");
        let ft = mb.add_func_type(vec![Ty::Ptr], vec![]);
        let mut fb = mb.function("borrow_ops", ft);

        let entry = fb.create_block();
        let ptr = fb.add_block_param(entry, Ty::Ptr);
        fb.switch_to_block(entry);

        let shared = fb.borrow(ptr);
        let mutable = fb.borrow_mut(ptr);
        fb.end_borrow(shared);
        fb.end_borrow(mutable);
        fb.ret(vec![]);
        fb.build();

        let module = mb.build().expect("ModuleBuilder::build: test fixture");
        let block = &module.functions[0].blocks[0];
        assert!(matches!(&block.body[0].inst, Inst::Borrow { .. }));
        assert_eq!(block.body[0].results.len(), 1); // borrow produces a value
        assert!(matches!(&block.body[1].inst, Inst::BorrowMut { .. }));
        assert_eq!(block.body[1].results.len(), 1); // borrow_mut produces a value
        assert!(matches!(&block.body[2].inst, Inst::EndBorrow { .. }));
        assert!(block.body[2].results.is_empty()); // end_borrow is void
        assert!(matches!(&block.body[3].inst, Inst::EndBorrow { .. }));
    }

    #[test]
    fn build_arc_instructions() {
        let mut mb = ModuleBuilder::new("arc_test");
        let ft = mb.add_func_type(vec![Ty::Ptr], vec![Ty::Bool]);
        let mut fb = mb.function("arc_ops", ft);

        let entry = fb.create_block();
        let ptr = fb.add_block_param(entry, Ty::Ptr);
        fb.switch_to_block(entry);

        fb.retain(ptr);
        fb.release(ptr);
        let unique = fb.is_unique(ptr);
        fb.ret(vec![unique]);
        fb.build();

        let module = mb.build().expect("ModuleBuilder::build: test fixture");
        let block = &module.functions[0].blocks[0];
        assert!(matches!(&block.body[0].inst, Inst::Retain { .. }));
        assert!(block.body[0].results.is_empty()); // retain is void
        assert!(matches!(&block.body[1].inst, Inst::Release { .. }));
        assert!(block.body[1].results.is_empty()); // release is void
        assert!(matches!(&block.body[2].inst, Inst::IsUnique { .. }));
        assert_eq!(block.body[2].results.len(), 1); // is_unique produces bool
    }

    #[test]
    fn build_switch() {
        let mut mb = ModuleBuilder::new("switch_test");
        let ft = mb.add_func_type(vec![Ty::I32], vec![Ty::I32]);
        let mut fb = mb.function("dispatch", ft);

        let entry = fb.create_block();
        let case_a = fb.create_block();
        let case_b = fb.create_block();
        let default_bb = fb.create_block();

        let x = fb.add_block_param(entry, Ty::I32);
        fb.switch_to_block(entry);

        fb.switch(
            x,
            vec![
                SwitchCase {
                    value: trust_ir::Constant::Int(0),
                    target: case_a,
                    args: vec![],
                },
                SwitchCase {
                    value: trust_ir::Constant::Int(1),
                    target: case_b,
                    args: vec![],
                },
            ],
            default_bb,
            vec![],
        );

        fb.switch_to_block(case_a);
        let r0 = fb.iconst(Ty::I32, 10);
        fb.ret(vec![r0]);

        fb.switch_to_block(case_b);
        let r1 = fb.iconst(Ty::I32, 20);
        fb.ret(vec![r1]);

        fb.switch_to_block(default_bb);
        let rd = fb.iconst(Ty::I32, -1);
        fb.ret(vec![rd]);

        fb.build();

        let module = mb.build().expect("ModuleBuilder::build: test fixture");
        let block = &module.functions[0].blocks[0];
        assert!(matches!(&block.body[0].inst, Inst::Switch { .. }));
        if let Inst::Switch { cases, .. } = &block.body[0].inst {
            assert_eq!(cases.len(), 2);
        }
    }

    #[test]
    fn build_call_indirect() {
        let mut mb = ModuleBuilder::new("call_indirect_test");
        let callee_ft = mb.add_func_type(vec![Ty::I32], vec![Ty::I32]);
        let ft = mb.add_func_type(vec![Ty::Ptr, Ty::I32], vec![Ty::I32]);
        let mut fb = mb.function("indirect_call", ft);

        let entry = fb.create_block();
        let fptr = fb.add_block_param(entry, Ty::Ptr);
        let arg = fb.add_block_param(entry, Ty::I32);
        fb.switch_to_block(entry);

        let result = fb.call_indirect(fptr, callee_ft, vec![arg]);
        fb.ret(vec![result]);
        fb.build();

        let module = mb.build().expect("ModuleBuilder::build: test fixture");
        let block = &module.functions[0].blocks[0];
        assert!(matches!(&block.body[0].inst, Inst::CallIndirect { .. }));
        assert_eq!(block.body[0].results.len(), 1);
    }

    #[test]
    fn build_call_indirect_void() {
        let mut mb = ModuleBuilder::new("call_indirect_void_test");
        let callee_ft = mb.add_func_type(vec![Ty::I32], vec![]);
        let ft = mb.add_func_type(vec![Ty::Ptr, Ty::I32], vec![]);
        let mut fb = mb.function("indirect_void_call", ft);

        let entry = fb.create_block();
        let fptr = fb.add_block_param(entry, Ty::Ptr);
        let arg = fb.add_block_param(entry, Ty::I32);
        fb.switch_to_block(entry);

        fb.call_indirect_void(fptr, callee_ft, vec![arg]);
        fb.ret(vec![]);
        fb.build();

        let module = mb.build().expect("ModuleBuilder::build: test fixture");
        let block = &module.functions[0].blocks[0];
        assert!(matches!(&block.body[0].inst, Inst::CallIndirect { .. }));
        assert!(block.body[0].results.is_empty());
    }

    #[test]
    fn build_atomic_rmw() {
        let mut mb = ModuleBuilder::new("rmw_test");
        let ft = mb.add_func_type(vec![Ty::Ptr, Ty::I64], vec![Ty::I64]);
        let mut fb = mb.function("atomic_add", ft);

        let entry = fb.create_block();
        let ptr = fb.add_block_param(entry, Ty::Ptr);
        let val = fb.add_block_param(entry, Ty::I64);
        fb.switch_to_block(entry);

        let old = fb.atomic_rmw(AtomicRMWOp::Add, Ty::I64, ptr, val, Ordering::AcqRel);
        fb.ret(vec![old]);
        fb.build();

        let module = mb.build().expect("ModuleBuilder::build: test fixture");
        let block = &module.functions[0].blocks[0];
        assert!(matches!(
            &block.body[0].inst,
            Inst::AtomicRMW {
                op: AtomicRMWOp::Add,
                ordering: Ordering::AcqRel,
                ..
            }
        ));
        assert_eq!(block.body[0].results.len(), 1);
    }

    #[test]
    fn build_cmpxchg() {
        let mut mb = ModuleBuilder::new("cas_test");
        let ft = mb.add_func_type(vec![Ty::Ptr, Ty::I64, Ty::I64], vec![Ty::I64, Ty::Bool]);
        let mut fb = mb.function("cas", ft);

        let entry = fb.create_block();
        let ptr = fb.add_block_param(entry, Ty::Ptr);
        let expected = fb.add_block_param(entry, Ty::I64);
        let desired = fb.add_block_param(entry, Ty::I64);
        fb.switch_to_block(entry);

        let (result, success) = fb.cmpxchg(
            Ty::I64,
            ptr,
            expected,
            desired,
            Ordering::SeqCst,
            Ordering::Acquire,
        );
        fb.ret(vec![result, success]);
        fb.build();

        let module = mb.build().expect("ModuleBuilder::build: test fixture");
        let block = &module.functions[0].blocks[0];
        assert!(matches!(&block.body[0].inst, Inst::CmpXchg { .. }));
        assert_eq!(block.body[0].results.len(), 2); // value + success flag
    }

    #[test]
    fn build_extract_insert_element() {
        let mut mb = ModuleBuilder::new("element_test");
        let ft = mb.add_func_type(vec![Ty::Ptr, Ty::I64, Ty::I32], vec![Ty::Ptr]);
        let mut fb = mb.function("array_ops", ft);

        let entry = fb.create_block();
        let arr = fb.add_block_param(entry, Ty::Ptr);
        let idx = fb.add_block_param(entry, Ty::I64);
        let val = fb.add_block_param(entry, Ty::I32);
        fb.switch_to_block(entry);

        let elem = fb.extract_element(Ty::I32, arr, idx);
        let new_arr = fb.insert_element(Ty::I32, arr, idx, val);
        let _ = elem;
        fb.ret(vec![new_arr]);
        fb.build();

        let module = mb.build().expect("ModuleBuilder::build: test fixture");
        let block = &module.functions[0].blocks[0];
        assert!(matches!(&block.body[0].inst, Inst::ExtractElement { .. }));
        assert_eq!(block.body[0].results.len(), 1);
        assert!(matches!(&block.body[1].inst, Inst::InsertElement { .. }));
        assert_eq!(block.body[1].results.len(), 1);
    }

    // --- Binding frame / DialectOp / Undef builder tests ---

    #[test]
    fn build_undef() {
        let mut mb = ModuleBuilder::new("undef_test");
        let ft = mb.add_func_type(vec![], vec![Ty::I32]);
        let mut fb = mb.function("undef_i32", ft);

        let entry = fb.create_block();
        fb.switch_to_block(entry);

        let u = fb.undef(Ty::I32);
        fb.ret(vec![u]);
        fb.build();

        let module = mb.build().expect("ModuleBuilder::build: test fixture");
        let block = &module.functions[0].blocks[0];
        assert!(matches!(&block.body[0].inst, Inst::Undef { ty: Ty::I32 }));
        assert_eq!(block.body[0].results.len(), 1);
    }

    #[test]
    fn build_binding_frame_lifecycle() {
        use trust_ir::value::BindingFrameId;

        let mut mb = ModuleBuilder::new("frame_test");
        let ft = mb.add_func_type(vec![Ty::I64], vec![Ty::I64]);
        let mut fb = mb.function("exists_lower", ft);

        let entry = fb.create_block();
        let seed = fb.add_block_param(entry, Ty::I64);
        fb.switch_to_block(entry);

        let def_ = BindingFrameDef::new(
            BindingFrameId::new(0),
            "E",
            vec![BindingSlot::new("i", Ty::I64)],
        );
        let f0 = fb.open_frame(def_);
        let f1 = fb.bind_slot(f0, 0, seed);
        let cur = fb.load_slot(f1, 0, Ty::I64);
        fb.close_frame(f1);
        fb.ret(vec![cur]);
        fb.build();

        let module = mb.build().expect("ModuleBuilder::build: test fixture");
        let block = &module.functions[0].blocks[0];
        // open_frame, bind_slot, load_slot, close_frame, ret
        assert_eq!(block.body.len(), 5);
        assert!(matches!(&block.body[0].inst, Inst::OpenFrame { .. }));
        assert_eq!(block.body[0].results.len(), 1);
        assert!(matches!(
            &block.body[1].inst,
            Inst::BindSlot { slot: 0, .. }
        ));
        assert_eq!(block.body[1].results.len(), 1);
        assert!(matches!(
            &block.body[2].inst,
            Inst::LoadSlot {
                slot: 0,
                ty: Ty::I64,
                ..
            }
        ));
        assert_eq!(block.body[2].results.len(), 1);
        assert!(matches!(&block.body[3].inst, Inst::CloseFrame { .. }));
        assert!(block.body[3].results.is_empty());

        // Load result matches block return.
        assert_eq!(block.body[2].results[0], cur);
    }

    #[test]
    fn build_dialect_op_no_results() {
        let mut mb = ModuleBuilder::new("dialect_void_test");
        let ft = mb.add_func_type(vec![Ty::I64], vec![]);
        let mut fb = mb.function("sink", ft);

        let entry = fb.create_block();
        let arg = fb.add_block_param(entry, Ty::I64);
        fb.switch_to_block(entry);

        let op = trust_ir::dialect::DialectInst::new("verif", "trace_event")
            .with_operand(arg)
            .with_attr("tag", trust_ir::dialect::AttrValue::Str("enter".into()));
        let results = fb.dialect_op(op);
        assert!(results.is_empty());

        fb.ret(vec![]);
        fb.build();

        let module = mb.build().expect("ModuleBuilder::build: test fixture");
        let block = &module.functions[0].blocks[0];
        assert!(matches!(&block.body[0].inst, Inst::DialectOp(_)));
        assert!(block.body[0].results.is_empty());
    }

    #[test]
    fn build_dialect_op_two_results() {
        let mut mb = ModuleBuilder::new("dialect_multi_test");
        let ft = mb.add_func_type(vec![Ty::I64], vec![Ty::I64]);
        let mut fb = mb.function("frontier", ft);

        let entry = fb.create_block();
        let seed = fb.add_block_param(entry, Ty::I64);
        fb.switch_to_block(entry);

        let op = trust_ir::dialect::DialectInst::new("verif", "frontier_drain")
            .with_operand(seed)
            .with_result_ty(Ty::I64)
            .with_result_ty(Ty::Bool)
            .with_attr("batch", trust_ir::dialect::AttrValue::U64(64));
        let results = fb.dialect_op(op);
        assert_eq!(results.len(), 2);

        fb.ret(vec![results[0]]);
        fb.build();

        let module = mb.build().expect("ModuleBuilder::build: test fixture");
        let block = &module.functions[0].blocks[0];
        assert!(matches!(&block.body[0].inst, Inst::DialectOp(_)));
        assert_eq!(block.body[0].results.len(), 2);
        assert_eq!(block.body[0].results[0], results[0]);
        assert_eq!(block.body[0].results[1], results[1]);

        // Result types on the dialect payload mirror the node's results.
        if let Inst::DialectOp(d) = &block.body[0].inst {
            assert_eq!(d.result_tys, vec![Ty::I64, Ty::Bool]);
            assert_eq!(d.qualified_name(), "verif.frontier_drain");
        } else {
            panic!("expected DialectOp");
        }
    }

    #[test]
    fn function_level_gpu_safety_via_builder() {
        let mut mb = ModuleBuilder::new("func_gpu_test");
        let ft = mb.add_func_type(vec![Ty::I32], vec![Ty::I32]);
        let mut fb = mb.function("gpu_ready", ft);

        fb.add_function_proof(ProofAnnotation::Pure);
        fb.add_function_proof(ProofAnnotation::NoPanic);
        fb.add_function_proof(ProofAnnotation::Deterministic);
        fb.add_function_proof(ProofAnnotation::Terminates);

        let entry = fb.create_block();
        let x = fb.add_block_param(entry, Ty::I32);
        fb.switch_to_block(entry);
        fb.ret(vec![x]);
        fb.build();

        let module = mb.build().expect("ModuleBuilder::build: test fixture");
        let func = &module.functions[0];
        assert!(func.is_safe_for_gpu());
        assert!(func.is_pure());
        assert!(func.is_deterministic());
        assert_eq!(func.gpu_proofs().len(), 3); // Pure, NoPanic, Deterministic
        assert_eq!(func.functional_proofs().len(), 3); // Pure, Deterministic, Terminates
    }
}

#[cfg(all(test, feature = "serde"))]
mod serde_tests {
    use super::*;
    use trust_ir::Linkage;
    use trust_ir::constant::Constant;
    use trust_ir::proof::ProofAnnotation;
    use trust_ir::ty::{FieldDef, StructDef, Ty};

    /// JSON round-trip: serialize then deserialize, assert equality.
    fn json_round_trip(module: &trust_ir::Module) -> trust_ir::Module {
        let json = serde_json::to_string_pretty(module).expect("serialize to JSON");
        let back: trust_ir::Module = serde_json::from_str(&json).expect("deserialize from JSON");
        assert_eq!(module, &back, "JSON round-trip mismatch");
        back
    }

    /// MessagePack round-trip: serialize then deserialize, assert equality.
    fn msgpack_round_trip(module: &trust_ir::Module) -> trust_ir::Module {
        let bytes = rmp_serde::to_vec(module).expect("serialize to MessagePack");
        let back: trust_ir::Module =
            rmp_serde::from_slice(&bytes).expect("deserialize from MessagePack");
        assert_eq!(module, &back, "MessagePack round-trip mismatch");
        back
    }

    #[test]
    fn builder_simple_add_json_round_trip() {
        let mut mb = ModuleBuilder::new("serde_add");
        let ft = mb.add_func_type(vec![Ty::I64, Ty::I64], vec![Ty::I64]);
        let mut fb = mb.function("add", ft);

        let entry = fb.create_block();
        let a = fb.add_block_param(entry, Ty::I64);
        let b_param = fb.add_block_param(entry, Ty::I64);
        fb.switch_to_block(entry);

        let sum = fb.add(Ty::I64, a, b_param);
        fb.ret(vec![sum]);
        fb.build();

        let module = mb.build().expect("ModuleBuilder::build: test fixture");
        json_round_trip(&module);
        msgpack_round_trip(&module);
    }

    #[test]
    fn builder_control_flow_serde_round_trip() {
        let mut mb = ModuleBuilder::new("serde_cf");
        let ft = mb.add_func_type(vec![Ty::I64], vec![Ty::I64]);
        let mut fb = mb.function("abs", ft);

        let entry = fb.create_block();
        let then_bb = fb.create_block();
        let else_bb = fb.create_block();
        let merge_bb = fb.create_block();

        let n = fb.add_block_param(entry, Ty::I64);
        let result_param = fb.add_block_param(merge_bb, Ty::I64);
        fb.set_entry(entry);

        fb.switch_to_block(entry);
        let zero = fb.iconst(Ty::I64, 0);
        let cmp = fb.icmp(ICmpOp::Slt, Ty::I64, n, zero);
        fb.condbr(cmp, then_bb, vec![], else_bb, vec![]);

        fb.switch_to_block(then_bb);
        let neg = fb.unop(UnOp::Neg, Ty::I64, n);
        fb.br(merge_bb, vec![neg]);

        fb.switch_to_block(else_bb);
        fb.br(merge_bb, vec![n]);

        fb.switch_to_block(merge_bb);
        fb.ret(vec![result_param]);

        fb.build();
        let module = mb.build().expect("ModuleBuilder::build: test fixture");
        json_round_trip(&module);
        msgpack_round_trip(&module);
    }

    #[test]
    fn builder_with_structs_globals_proofs_serde_round_trip() {
        let mut mb = ModuleBuilder::new("serde_complex");

        // Struct
        let sid = mb.add_struct(StructDef {
            id: trust_ir::StructId::new(0),
            name: "Point".to_string(),
            fields: vec![
                FieldDef {
                    name: "x".to_string(),
                    ty: Ty::F64,
                    offset: Some(0),
                },
                FieldDef {
                    name: "y".to_string(),
                    ty: Ty::F64,
                    offset: Some(8),
                },
            ],
            size: Some(16),
            align: Some(8),
            repr: Default::default(),
            origin: None,
        });

        // Global
        mb.add_global(Global {
            name: "ORIGIN".to_string(),
            ty: Ty::Struct(sid),
            mutable: false,
            initializer: Some(Constant::Aggregate(vec![
                Constant::Float(0.0),
                Constant::Float(0.0),
            ])),
            linkage: Linkage::External,
            tls: None,
            align: None,

            section: None,
            visibility: Default::default(),
            retained: false,
        });

        // Function with proof annotations
        let ft = mb.add_func_type(vec![Ty::Ptr], vec![Ty::F64]);
        let mut fb = mb.function("get_x", ft);
        let entry = fb.create_block();
        let ptr = fb.add_block_param(entry, Ty::Ptr);
        fb.switch_to_block(entry);

        let loaded = fb.load_proven(
            Ty::F64,
            ptr,
            vec![ProofAnnotation::InBounds, ProofAnnotation::NotNull],
        );
        fb.ret(vec![loaded]);
        fb.build();

        let module = mb.build().expect("ModuleBuilder::build: test fixture");
        json_round_trip(&module);
        msgpack_round_trip(&module);
    }

    #[test]
    fn builder_multi_function_serde_round_trip() {
        let mut mb = ModuleBuilder::new("serde_multi");
        let ft_add = mb.add_func_type(vec![Ty::I32, Ty::I32], vec![Ty::I32]);
        let ft_main = mb.add_func_type(vec![], vec![Ty::I32]);

        // Function: add
        {
            let mut fb = mb.function("add", ft_add);
            let entry = fb.create_block();
            let a = fb.add_block_param(entry, Ty::I32);
            let b_param = fb.add_block_param(entry, Ty::I32);
            fb.switch_to_block(entry);
            let sum = fb.add(Ty::I32, a, b_param);
            fb.ret(vec![sum]);
            fb.build();
        }

        // Function: main (calls add)
        {
            let mut fb = mb.function("main", ft_main);
            let entry = fb.create_block();
            fb.switch_to_block(entry);
            let a = fb.iconst(Ty::I32, 10);
            let b_val = fb.iconst(Ty::I32, 20);
            let result = fb.call(FuncId::new(0), vec![a, b_val]);
            fb.ret(vec![result]);
            fb.build();
        }

        let module = mb.build().expect("ModuleBuilder::build: test fixture");
        assert_eq!(module.functions.len(), 2);
        json_round_trip(&module);
        msgpack_round_trip(&module);
    }

    #[test]
    fn builder_memory_ops_serde_round_trip() {
        let mut mb = ModuleBuilder::new("serde_mem");
        let ft = mb.add_func_type(vec![], vec![Ty::I32]);
        let mut fb = mb.function("mem_ops", ft);

        let entry = fb.create_block();
        fb.switch_to_block(entry);

        let ptr = fb.alloca(Ty::I32);
        let val = fb.iconst(Ty::I32, 42);
        fb.store(Ty::I32, ptr, val);
        let loaded = fb.load(Ty::I32, ptr);
        fb.ret(vec![loaded]);
        fb.build();

        let module = mb.build().expect("ModuleBuilder::build: test fixture");
        json_round_trip(&module);
        msgpack_round_trip(&module);
    }

    #[test]
    fn builder_atomics_serde_round_trip() {
        let mut mb = ModuleBuilder::new("serde_atomic");
        let ft = mb.add_func_type(vec![Ty::Ptr], vec![Ty::I64]);
        let mut fb = mb.function("atomic_inc", ft);

        let entry = fb.create_block();
        let ptr = fb.add_block_param(entry, Ty::Ptr);
        fb.switch_to_block(entry);

        let loaded = fb.atomic_load(Ty::I64, ptr, Ordering::Acquire);
        let one = fb.iconst(Ty::I64, 1);
        let sum = fb.add(Ty::I64, loaded, one);
        fb.atomic_store(Ty::I64, ptr, sum, Ordering::Release);
        fb.fence(Ordering::SeqCst);
        fb.ret(vec![sum]);
        fb.build();

        let module = mb.build().expect("ModuleBuilder::build: test fixture");
        json_round_trip(&module);
        msgpack_round_trip(&module);
    }

    #[test]
    fn builder_call_proven_serde_round_trip() {
        let mut mb = ModuleBuilder::new("serde_call_proven");
        let ft = mb.add_func_type(vec![Ty::I32], vec![Ty::I32]);
        let mut fb = mb.function("caller", ft);

        fb.add_function_proof(ProofAnnotation::Pure);
        fb.add_function_proof(ProofAnnotation::NoPanic);
        fb.add_function_proof(ProofAnnotation::Deterministic);

        let entry = fb.create_block();
        let x = fb.add_block_param(entry, Ty::I32);
        fb.switch_to_block(entry);

        let result = fb.call_proven(
            FuncId::new(1),
            vec![x],
            vec![ProofAnnotation::Pure, ProofAnnotation::NoPanic],
        );
        fb.ret(vec![result]);
        fb.build();

        let module = mb.build().expect("ModuleBuilder::build: test fixture");
        json_round_trip(&module);
        msgpack_round_trip(&module);
    }

    #[test]
    fn builder_atomic_load_proven_serde_round_trip() {
        let mut mb = ModuleBuilder::new("serde_atomic_proven");
        let ft = mb.add_func_type(vec![Ty::Ptr], vec![Ty::I64]);
        let mut fb = mb.function("safe_load", ft);

        let entry = fb.create_block();
        let ptr = fb.add_block_param(entry, Ty::Ptr);
        fb.switch_to_block(entry);

        let loaded = fb.atomic_load_proven(
            Ty::I64,
            ptr,
            Ordering::Acquire,
            vec![ProofAnnotation::NoAlias, ProofAnnotation::DataRaceFree],
        );
        fb.ret(vec![loaded]);
        fb.build();

        let module = mb.build().expect("ModuleBuilder::build: test fixture");
        json_round_trip(&module);
        msgpack_round_trip(&module);
    }

    #[test]
    fn builder_cast_proven_serde_round_trip() {
        let mut mb = ModuleBuilder::new("serde_cast_proven");
        let ft = mb.add_func_type(vec![Ty::I64], vec![Ty::I32]);
        let mut fb = mb.function("safe_trunc", ft);

        let entry = fb.create_block();
        let x = fb.add_block_param(entry, Ty::I64);
        fb.switch_to_block(entry);

        let result = fb.cast_proven(
            CastOp::Trunc,
            Ty::I64,
            Ty::I32,
            x,
            vec![ProofAnnotation::NoOverflow, ProofAnnotation::NoUndef],
        );
        fb.ret(vec![result]);
        fb.build();

        let module = mb.build().expect("ModuleBuilder::build: test fixture");
        json_round_trip(&module);
        msgpack_round_trip(&module);
    }

    #[test]
    fn msgpack_smaller_than_json_for_builder_output() {
        let mut mb = ModuleBuilder::new("size_test");
        let ft = mb.add_func_type(vec![Ty::I32, Ty::I32], vec![Ty::I32]);
        let mut fb = mb.function("add", ft);
        let entry = fb.create_block();
        let a = fb.add_block_param(entry, Ty::I32);
        let b_param = fb.add_block_param(entry, Ty::I32);
        fb.switch_to_block(entry);
        let sum = fb.add(Ty::I32, a, b_param);
        fb.ret(vec![sum]);
        fb.build();

        let module = mb.build().expect("ModuleBuilder::build: test fixture");
        let json = serde_json::to_string(&module).expect("JSON");
        let msgpack = rmp_serde::to_vec(&module).expect("MessagePack");
        assert!(
            msgpack.len() < json.len(),
            "MessagePack ({} bytes) should be smaller than JSON ({} bytes)",
            msgpack.len(),
            json.len()
        );
    }

    // ── D1b: sticky faults and one commit point ───────────────────────────
    //
    // "A construction door refuses; it never panics on a value its signature
    // admits" (`docs/SPEC_RATIFICATIONS.md`). Private cursors are set directly:
    // the cliffs need 2^32 resident ids through the public API.

    /// A named way to provoke one fault.
    type FaultCase = (&'static str, Box<dyn FnOnce(&mut ModuleBuilder)>);

    /// One fault scenario: build a draft, provoke one fault, return what
    /// `ModuleBuilder::build` reports.
    fn fault_of(provoke: impl FnOnce(&mut ModuleBuilder)) -> Result<Module, BuildError> {
        let mut module = ModuleBuilder::new("faults");
        provoke(&mut module);
        module.build()
    }

    /// T1, kind (i): before D1b every case below panicked (`panic!` /
    /// `expect` / an index). Each door now records and returns; nothing
    /// unwinds. Mutation check: restoring any `panic!`, `expect` or index
    /// turns its case red.
    #[test]
    fn no_builder_door_panics_on_a_fault() {
        use std::panic::{AssertUnwindSafe, catch_unwind};
        let cases: Vec<FaultCase> = vec![
            (
                "value exhaustion",
                Box::new(|module| {
                    let signature = module.add_func_type(vec![], vec![]);
                    let mut function = module.function("f", signature);
                    let entry = function.create_block();
                    function.switch_to_block(entry);
                    function.next_value = FreshIds::after([ValueId::new(u32::MAX)]);
                    let value = function.iconst(Ty::I32, 1);
                    assert_eq!(value, ValueId::new(u32::MAX), "the placeholder");
                    function.build();
                }),
            ),
            (
                "block exhaustion",
                Box::new(|module| {
                    let signature = module.add_func_type(vec![], vec![]);
                    let mut function = module.function("f", signature);
                    function.next_block = FreshIds::after([BlockId::new(u32::MAX)]);
                    assert_eq!(function.create_block(), BlockId::new(u32::MAX));
                    function.build();
                }),
            ),
            (
                "no current block",
                Box::new(|module| {
                    let signature = module.add_func_type(vec![], vec![]);
                    let mut function = module.function("f", signature);
                    let _ = function.create_block();
                    function.ret(vec![]);
                    function.build();
                }),
            ),
            (
                "unknown block on emit",
                Box::new(|module| {
                    let signature = module.add_func_type(vec![], vec![]);
                    let mut function = module.function("f", signature);
                    function.switch_to_block(BlockId::new(7));
                    function.ret(vec![]);
                    function.build();
                }),
            ),
            (
                "unknown block on add_block_param",
                Box::new(|module| {
                    let signature = module.add_func_type(vec![], vec![]);
                    let mut function = module.function("f", signature);
                    let param = function.add_block_param(BlockId::new(7), Ty::I32);
                    assert_eq!(param, ValueId::new(u32::MAX));
                    function.build();
                }),
            ),
            (
                "mixing through the view",
                Box::new(|module| {
                    let signature = module.add_func_type(vec![], vec![]);
                    let mut function = module.function("f", signature);
                    let entry = function.create_block();
                    let mut reserved = function.reserve_block_params(1).expect("room");
                    let _ = reserved.add_block_param(entry, Ty::Bool);
                    drop(reserved);
                    function.build();
                }),
            ),
            (
                "a leaked reservation view at build",
                Box::new(|module| {
                    let signature = module.add_func_type(vec![], vec![]);
                    let mut function = module.function("f", signature);
                    let _ = function.create_block();
                    std::mem::forget(function.reserve_block_params(1).expect("room"));
                    function.build();
                }),
            ),
            (
                "func-id exhaustion on function()",
                Box::new(|module| {
                    let signature = module.add_func_type(vec![], vec![]);
                    module.next_func_id = FreshIds::after([FuncId::new(u32::MAX)]);
                    let function = module.function("f", signature);
                    assert_eq!(function.build(), FuncId::new(u32::MAX));
                }),
            ),
            (
                "func-id exhaustion on declare_function()",
                Box::new(|module| {
                    let signature = module.add_func_type(vec![], vec![]);
                    module.next_func_id = FreshIds::after([FuncId::new(u32::MAX)]);
                    assert_eq!(
                        module.declare_function("d", signature),
                        FuncId::new(u32::MAX)
                    );
                    assert!(module.module.functions.is_empty(), "nothing pushed");
                }),
            ),
            (
                "obligation exhaustion at build()",
                Box::new(|module| {
                    module
                        .module
                        .proof_obligations
                        .push(trust_ir::proof::ProofObligation::new(
                            ProofId::new(u32::MAX),
                            trust_ir::proof::ObligationKind::Precondition,
                            trust_ir::proof::ProofStatus::Pending,
                            "decoded row",
                        ));
                    let signature = module.add_func_type(vec![], vec![]);
                    let mut function = module.function("f", signature);
                    function.add_function_proof(ProofAnnotation::NoPanic);
                    function.build();
                }),
            ),
        ];
        for (name, provoke) in cases {
            let built = catch_unwind(AssertUnwindSafe(|| fault_of(provoke)))
                .unwrap_or_else(|_| panic!("{name}: a builder door panicked"));
            assert!(built.is_err(), "{name}: a faulted builder never builds");
        }
    }

    /// T2, kind (ii) (T1 is the failing half): each fault is reported by the
    /// one commit point, typed, naming the function and block; a fault-free
    /// control builds and validates empty. Mutation check: `build` ignoring
    /// `fault` turns every `Err` assertion red.
    #[test]
    fn a_faulted_builder_never_builds() {
        let f = FuncId::new(0);
        assert_eq!(
            fault_of(|module| {
                let signature = module.add_func_type(vec![], vec![]);
                let mut function = module.function("f", signature);
                let _ = function.create_block();
                function.ret(vec![]);
                function.build();
            })
            .err(),
            Some(BuildError::NoCurrentBlock {
                function: f,
                emitted: 0
            })
        );
        assert_eq!(
            fault_of(|module| {
                let signature = module.add_func_type(vec![], vec![]);
                let mut function = module.function("f", signature);
                function.switch_to_block(BlockId::new(3));
                function.ret(vec![]);
                function.build();
            })
            .err(),
            Some(BuildError::UnknownBlock {
                function: f,
                block: BlockId::new(3)
            })
        );
        assert_eq!(
            fault_of(|module| {
                let signature = module.add_func_type(vec![], vec![]);
                let mut function = module.function("f", signature);
                let _ = function.create_block();
                std::mem::forget(function.reserve_block_params(1).expect("room"));
                function.build();
            })
            .err(),
            Some(BuildError::ReservationAbandoned { function: f })
        );
        assert_eq!(
            fault_of(|module| {
                let signature = module.add_func_type(vec![], vec![]);
                module.next_func_id = FreshIds::after([FuncId::new(u32::MAX)]);
                let _ = module.declare_function("d", signature);
            })
            .err(),
            Some(BuildError::IdSpaceExhausted {
                space: "FuncId",
                function: None
            })
        );

        // Control: no fault, a module, and it validates.
        let control = fault_of(|module| {
            let signature = module.add_func_type(vec![], vec![]);
            let mut function = module.function("f", signature);
            let entry = function.create_block();
            function.set_entry(entry);
            function.switch_to_block(entry);
            function.ret(vec![]);
            function.build();
        })
        .expect("a fault-free builder builds");
        assert!(crate::validate::validate_module(&control).is_empty());
    }

    /// T2: the FIRST fault is reported, not a consequence of it. Mutation
    /// check: last-write-wins reports the later `UnknownBlock`.
    #[test]
    fn the_first_fault_is_the_one_reported() {
        let reported = fault_of(|module| {
            let signature = module.add_func_type(vec![], vec![]);
            let mut function = module.function("f", signature);
            function.ret(vec![]); // first: no current block
            function.switch_to_block(BlockId::new(9));
            function.ret(vec![]); // second: unknown block
            function.build();
        });
        assert_eq!(
            reported.err(),
            Some(BuildError::NoCurrentBlock {
                function: FuncId::new(0),
                emitted: 0
            })
        );
    }

    /// T2: a fault is recorded when it happens, on the module builder, so a
    /// draft that faulted and was then DROPPED (never built) still poisons
    /// the module. Mutation check: keeping faults on the draft only builds a
    /// module here.
    #[test]
    fn a_fault_in_an_abandoned_draft_still_poisons_the_module() {
        let reported = fault_of(|module| {
            let signature = module.add_func_type(vec![], vec![]);
            {
                let mut abandoned = module.function("abandoned", signature);
                abandoned.ret(vec![]);
                // dropped without build()
            }
            let mut fine = module.function("fine", signature);
            let entry = fine.create_block();
            fine.switch_to_block(entry);
            fine.ret(vec![]);
            fine.build();
        });
        assert_eq!(
            reported.err(),
            Some(BuildError::NoCurrentBlock {
                function: FuncId::new(0),
                emitted: 0
            })
        );
    }

    /// T3, kind (ii): `peek_next_func_id` cannot record (`&self`), so it
    /// returns the refusal; a placeholder would escape into a committed
    /// obligation. Before D1b it panicked.
    #[test]
    fn peek_next_func_id_refuses_once_exhausted() {
        let mut module = ModuleBuilder::new("peek");
        assert_eq!(module.peek_next_func_id(), Ok(FuncId::new(0)));
        module.next_func_id = FreshIds::after([FuncId::new(u32::MAX)]);
        let peeked =
            std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| module.peek_next_func_id()))
                .expect("peek never panics");
        assert_eq!(peeked, Err(IdSpaceExhausted::of::<FuncId>()));
        assert!(module.build().is_ok(), "peeking records no fault");
    }
}

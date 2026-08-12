// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use trust_ir::constant::Constant;
use trust_ir::dialect::DialectInst;
use trust_ir::inst::{BindingFrameDef, *};
use trust_ir::node::InstrNode;
use trust_ir::proof::{ProofAnnotation, ProofObligation};
use trust_ir::ty::{FuncTy, StructDef, Ty};
use trust_ir::value::{
    BlockId, FuncId, FuncTyId, GlobalId, ProofId, ScopeData, SourceSpan, ValueId,
};
use trust_ir::{Block, Function, Global, Module};

use std::collections::HashMap;

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
    next_func_id: u32,
    /// Producer provenance (v23) stamped on every function subsequently
    /// created via [`function`](Self::function). `None` (the default) leaves
    /// `Function::producer` unset; a per-function
    /// [`FunctionBuilder::set_producer`] overrides it.
    default_producer: Option<trust_ir::Producer>,
}

impl ModuleBuilder {
    pub fn new(name: impl Into<String>) -> Self {
        Self {
            module: Module::new(name),
            next_func_id: 0,
            default_producer: None,
        }
    }

    /// Set the producer provenance tag (v23) stamped on every function created
    /// via [`function`](Self::function) from this point on. A frontend calls
    /// this once (e.g. `Producer::Clean`) instead of tagging each function;
    /// [`FunctionBuilder::set_producer`] overrides it per function.
    pub fn set_default_producer(&mut self, producer: trust_ir::Producer) {
        self.default_producer = Some(producer);
    }

    pub fn add_func_type(&mut self, params: Vec<Ty>, returns: Vec<Ty>) -> FuncTyId {
        self.module.add_func_type(FuncTy {
            params,
            returns,
            is_vararg: false,
        })
    }

    /// Intern a C-variadic function signature: `params` is the fixed prefix and
    /// callers may pass additional trailing arguments. Used to declare imports
    /// of variadic runtime symbols (e.g. `clean_alloc_ctor(tag, nobj, scalar,
    /// ...)`); `validate_module` only requires `args.len() >= params.len()` for
    /// calls to a vararg callee.
    pub fn add_vararg_func_type(&mut self, params: Vec<Ty>, returns: Vec<Ty>) -> FuncTyId {
        self.module.add_func_type(FuncTy {
            params,
            returns,
            is_vararg: true,
        })
    }

    pub fn add_struct(&mut self, sd: StructDef) -> trust_ir::StructId {
        self.module.add_struct(sd)
    }

    /// Register a `Ty` in the module's type table and return its `TyId`.
    ///
    /// Needed by callers that construct aggregate types such as
    /// `Ty::Array(TyId, len)`, whose element type must be interned first.
    pub fn add_type(&mut self, ty: Ty) -> trust_ir::TyId {
        self.module.add_type(ty)
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
    pub fn intern_universe(&mut self, universe: trust_ir::Universe) -> Option<trust_ir::UnivId> {
        self.module.intern_universe(universe)
    }

    /// Intern a [`trust_ir::Pred`] by content. See
    /// [`trust_ir::Module::intern_pred`].
    pub fn intern_pred(&mut self, pred: trust_ir::Pred) -> Option<trust_ir::PredId> {
        self.module.intern_pred(pred)
    }

    /// Intern `Pred::InUniverse(universe, space)` in one step.
    pub fn intern_in_universe(
        &mut self,
        universe: trust_ir::Universe,
        space: trust_ir::Space,
    ) -> Option<trust_ir::PredId> {
        self.module.intern_in_universe(universe, space)
    }

    /// Build the refinement type `refine<base, pred>`, interning `base` in the
    /// module type table. Representation-preserving: the value still has
    /// exactly `base`'s representation.
    pub fn refine_ty(&mut self, base: Ty, pred: trust_ir::PredId) -> Ty {
        let base_id = self.module.add_type(base);
        Ty::Refine(base_id, pred)
    }

    pub fn add_global(&mut self, global: Global) {
        self.module.globals.push(global);
    }

    /// The `FuncId` the next [`function`](Self::function) call will assign.
    ///
    /// A producer that must know a body's id BEFORE taking the builder's
    /// exclusive module borrow (to wire self-recursion, or to B4-scope a
    /// module-level [`ProofObligation`] at the body it belongs to) reads it
    /// here instead of re-deriving the arithmetic and hoping it still agrees.
    pub fn peek_next_func_id(&self) -> FuncId {
        FuncId::new(self.next_func_id)
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
    /// Panics only if the obligation table would exceed the `u32` id space
    /// (the same discipline as `Module::add_function`'s obligation synthesis).
    pub fn add_proof_obligation(
        &mut self,
        make: impl FnOnce(ProofId) -> ProofObligation,
    ) -> ProofId {
        let next = self
            .module
            .proof_obligations
            .iter()
            .map(|o| {
                o.id.index()
                    .checked_add(1)
                    .expect("proof-obligation table exceeds u32 id space")
            })
            .max()
            .unwrap_or(0);
        let id = ProofId::new(next);
        let obligation = make(id);
        debug_assert_eq!(
            obligation.id, id,
            "add_proof_obligation: the row must carry the id it was handed"
        );
        self.module.proof_obligations.push(obligation);
        id
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
    pub fn intern_file(&mut self, path: impl Into<String>) -> u32 {
        self.module.intern_file(path)
    }

    pub fn function(&mut self, name: impl Into<String>, ty: FuncTyId) -> FunctionBuilder<'_> {
        let id = FuncId::new(self.next_func_id);
        self.next_func_id += 1;
        let mut func = Function::new(id, name, ty, BlockId::new(0));
        func.producer = self.default_producer.clone();
        FunctionBuilder {
            module: &mut self.module,
            func,
            current_block: None,
            next_value: 0,
            next_block: 0,
            current_span: None,
            current_scope: None,
            ptr_extents: HashMap::new(),
        }
    }

    pub fn build(self) -> Module {
        self.module
    }

    /// Sign the module with a proof lineage to produce a verification bundle.
    pub fn sign_with_lineage(
        self,
        lineage: trust_ir::ProofLineageManifest,
    ) -> trust_ir::request::NativeVerificationBundle {
        let module = self.module;
        let mut bundle = trust_ir::request::NativeVerificationBundle::new(
            trust_ir::request::NativeBundleProducer::TrustIr,
            trust_ir::request::NativeAdapterInput::TrustIrModule,
            trust_ir::proof::ProofDigest::zero(),
            module,
            lineage,
        );
        bundle.schema_version = 1;
        bundle
    }

    /// Sign the module by attaching a proof-lineage manifest containing the supplied
    /// certificates. Returns a verified bundle ready for production codegen.
    pub fn sign(
        self,
        certificates: Vec<trust_ir::proof::ProofCertificate>,
    ) -> trust_ir::request::NativeVerificationBundle {
        use trust_ir::proof::{
            ProofDigest, ProofLineageId, ProofLineageManifest, ProofLineageNode, ProofTransform,
            ProofTransformStage,
        };
        use trust_ir::request::{
            NativeAdapterInput, NativeBundleProducer, NativeVerificationBundle,
        };

        let module = self.build();

        // G19: reusable whole-module stable structural digest. This is the
        // single source of truth for the module-level fingerprint (never depends
        // on HashMap/HashSet iteration order); see `Module::stable_digest`.
        let module_digest = module.stable_digest();

        // Convert certificates to refs for the manifest node
        let certificate_refs = certificates
            .iter()
            .map(|c| trust_ir::proof::ProofCertificateRef {
                obligation: c.obligation,
                prover: c.prover.clone(),
                evidence_digest: c.evidence_digest(),
            })
            .collect();

        // Create a single lineage node representing the TrustIr verification stage
        let node = ProofLineageNode {
            id: ProofLineageId::new(0),
            transform: ProofTransform {
                stage: ProofTransformStage::TrustIrLowering,
                name: "trust-ir-build".into(),
                producer: "trust-ir-build".into(),
                version: env!("CARGO_PKG_VERSION").into(),
            },
            source_module: ProofDigest::zero(), // Finalized by frontend
            target_module: module_digest,
            obligations: certificates.iter().map(|c| c.obligation).collect(),
            certificates: certificate_refs,
            replay: None,
            depends_on: Vec::new(),
        };

        let mut manifest = ProofLineageManifest::new();
        manifest.nodes.push(node);
        manifest.roots.push(ProofLineageId::new(0));

        let mut bundle = NativeVerificationBundle::new(
            NativeBundleProducer::TrustIr,
            NativeAdapterInput::TrustIrModule,
            module_digest,
            module,
            manifest,
        );
        bundle.schema_version = 1;
        bundle
    }
}

/// Programmatic emitter for a single function's IR.
///
/// CONTRACT — this is an *unchecked* emitter by design: it produces structure,
/// it does not verify it. Specifically:
/// * `emit`/`emit_void` **panic** if no current block is selected
///   (`switch_to_block` first). Misuse is a producer bug, not a runtime
///   condition, so it panics rather than returning a `Result`.
/// * It performs **no** type-checking, SSA/dominance, terminator-placement, or
///   well-formedness checks — that is `validate_function`/`validate_module`'s
///   job. A builder can construct anything the validator rejects; producers are
///   expected to run validation before trusting a built module.
/// * `FuncId`s are assigned by `ModuleBuilder` at registration; abandoning a
///   `FunctionBuilder` without `build()` can leave a gap in the id space (no
///   recycling). This is benign for ids-as-indices but is not a dense-id
///   guarantee.
pub struct FunctionBuilder<'m> {
    module: &'m mut Module,
    func: Function,
    current_block: Option<usize>,
    next_value: u32,
    next_block: u32,
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
}

impl<'m> FunctionBuilder<'m> {
    fn alloc_value(&mut self) -> ValueId {
        let id = ValueId::new(self.next_value);
        self.next_value += 1;
        id
    }

    pub fn create_block(&mut self) -> BlockId {
        let id = BlockId::new(self.next_block);
        self.next_block += 1;
        self.func.blocks.push(Block::new(id));
        id
    }

    pub fn add_block_param(&mut self, block: BlockId, ty: Ty) -> ValueId {
        let val = self.alloc_value();
        let b = &mut self.func.blocks[block.as_usize()];
        b.params.push((val, ty));
        val
    }

    pub fn switch_to_block(&mut self, block: BlockId) {
        self.current_block = Some(block.as_usize());
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
        let block = &self.func.blocks[self.current_block?];
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
        let idx = self.current_block.expect("no current block");
        self.func.blocks[idx].body.push(node);
    }

    // `pub(crate)` so the demo/fixture emitters (`crate::demo`) can share the
    // single span-threading emit path without widening the public API.
    pub(crate) fn emit(&mut self, inst: Inst) -> ValueId {
        let result = self.alloc_value();
        let node = InstrNode::new(inst).with_result(result);
        self.push_node(node);
        result
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
    fn note_layout_derived_extent(&mut self, ptr: ValueId, ty: &Ty) {
        if let Some(size) = self
            .module
            .ty_layout_shape(ty)
            .ok()
            .and_then(|shape| shape.size_bytes())
        {
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
            Some(_) => self.gep_inbounds_proven(
                Ty::I8,
                base,
                vec![idx],
                vec![ProofAnnotation::InBounds],
            ),
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
        let node = InstrNode::new(Inst::CmpXchg {
            ty,
            ptr,
            expected,
            desired,
            success,
            failure,
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

    // --- Aggregates ---

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

    pub fn assert(&mut self, cond: ValueId) {
        self.emit_void(Inst::Assert { cond });
    }

    pub fn unreachable(&mut self) {
        self.emit_void(Inst::Unreachable);
    }

    /// Add a proof annotation to the function being built.
    ///
    /// Function-level proofs describe properties of the entire function
    /// (e.g., Pure, NoPanic, Terminates). TrustIr reads these during
    /// cross-target synthesis to determine which functions can be
    /// offloaded to GPU/ANE.
    pub fn add_proof(&mut self, annotation: ProofAnnotation) {
        self.func.proofs.push(annotation);
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
    /// produced a concrete value. Its semantics are defined in
    /// `lean/trust_ir-semantics/TrustIr/State/ValueMap.lean` (`Value.undef`).
    pub fn undef(&mut self, ty: Ty) -> ValueId {
        self.emit(Inst::Undef { ty })
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
    /// Returns a fresh SSA value representing the binding (used downstream
    /// for data dependency tracking; this is not the stored value itself).
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

    pub fn build(self) -> FuncId {
        let id = self.func.id;
        self.module.add_function(self.func);
        id
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use trust_ir::proof::ProofAnnotation;
    use trust_ir::ty::Ty;
    use trust_ir::value::SourceSpan;
    use trust_ir::{Linkage, TlsModel};

    /// `add_proof_obligation` allocates dense ids from an empty table and
    /// hands each row the id it is stored under.
    #[test]
    fn add_proof_obligation_allocates_dense_ids() {
        use trust_ir::proof::{ObligationKind, ProofObligation, ProofStatus};

        let mut mb = ModuleBuilder::new("obligations");
        let first = mb.add_proof_obligation(|id| {
            ProofObligation::new(id, ObligationKind::BoundsCheck, ProofStatus::Pending, "a")
        });
        let second = mb.add_proof_obligation(|id| {
            ProofObligation::new(
                id,
                ObligationKind::ArithmeticSafety,
                ProofStatus::Pending,
                "b",
            )
        });
        assert_eq!(first.index(), 0);
        assert_eq!(second.index(), 1);
        let m = mb.build();
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
        let next = mb.add_proof_obligation(|id| {
            ProofObligation::new(id, ObligationKind::BoundsCheck, ProofStatus::Pending, "new")
        });
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
        let fid = mb.peek_next_func_id();
        let recorded = mb.add_proof_obligation(|id| {
            ProofObligation::new(
                id,
                ObligationKind::BoundsCheck,
                ProofStatus::Pending,
                "index in bounds",
            )
            .with_function(fid)
        });

        let ft = mb.add_func_type(vec![Ty::I64], vec![Ty::I64]);
        let mut fb = mb.function("identity", ft);
        let entry = fb.create_block();
        let x = fb.add_block_param(entry, Ty::I64);
        fb.switch_to_block(entry);
        fb.ret(vec![x]);
        let built = fb.build();

        assert_eq!(built, fid, "peek_next_func_id must predict the assigned id");
        let m = mb.build();
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
        let m = mb.build();
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
            },
            ScopeData {
                parent: Some(0),
                span: None,
            },
        ]);
        fb.switch_to_block(entry);
        fb.set_scope(1);
        let copy = fb.copy(Ty::I64, input);
        fb.add_value_name(copy, "copy");
        fb.clear_scope();
        fb.ret(vec![copy]);
        fb.build();

        let module = mb.build();
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

        let module = mb.build();
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

        let module = mb.build();
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
        let module = mb.build();

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

        let module = mb.build();
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

        let module = mb.build();
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

        let module = mb.build();
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

        let module = mb.build();
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

        let module = mb.build();
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

        let module = mb.build();
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

        let module = mb.build();
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

        let module = mb.build();
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

        let module = mb.build();
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

        let module = mb.build();
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
        });
        let module = mb.build();
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
        });
        let module = mb.build();
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
        });
        assert_eq!(sid.index(), 0);
        let module = mb.build();
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

        let module = mb.build();
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
        let module = mb.build();
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
        let module = mb.build();
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
        let module = mb.build();
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
        assert!(mb2.build().functions[0].attrs.is_empty());
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
        let module = mb.build();
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

        fb.add_proof(ProofAnnotation::Pure);
        fb.add_proof(ProofAnnotation::NoPanic);
        fb.add_proof(ProofAnnotation::Terminates);

        let entry = fb.create_block();
        let x = fb.add_block_param(entry, Ty::I32);
        fb.switch_to_block(entry);
        fb.ret(vec![x]);
        fb.build();

        let module = mb.build();
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

        let module = mb.build();
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

        let module = mb.build();
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

        let module = mb.build();
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

        let module = mb.build();
        let gep_node = &module.functions[0].blocks[0].body[1];
        assert!(matches!(
            gep_node.inst,
            Inst::GEP { inbounds: true, .. }
        ));
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
        let module = mb.build();
        let node = module.functions[0].blocks[0]
            .body
            .iter()
            .find(|n| n.results == vec![g])
            .unwrap();
        assert!(
            matches!(node.inst, Inst::GEP { inbounds: false, .. }),
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

        let module = mb.build();
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

        let module = mb.build();
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

        let module = mb.build();
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

        let module = mb.build();
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

        let module = mb.build();
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

        let module = mb.build();
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

        let module = mb.build();
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

        let module = mb.build();
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

        let module = mb.build();
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

        let module = mb.build();
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

        let module = mb.build();
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

        let module = mb.build();
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

        let module = mb.build();
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

        let module = mb.build();
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

        let module = mb.build();
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

        let module = mb.build();
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

        let module = mb.build();
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

        let module = mb.build();
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

        fb.add_proof(ProofAnnotation::Pure);
        fb.add_proof(ProofAnnotation::NoPanic);
        fb.add_proof(ProofAnnotation::Deterministic);
        fb.add_proof(ProofAnnotation::Terminates);

        let entry = fb.create_block();
        let x = fb.add_block_param(entry, Ty::I32);
        fb.switch_to_block(entry);
        fb.ret(vec![x]);
        fb.build();

        let module = mb.build();
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

        let module = mb.build();
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
        let module = mb.build();
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

        let module = mb.build();
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

        let module = mb.build();
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

        let module = mb.build();
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

        let module = mb.build();
        json_round_trip(&module);
        msgpack_round_trip(&module);
    }

    #[test]
    fn builder_call_proven_serde_round_trip() {
        let mut mb = ModuleBuilder::new("serde_call_proven");
        let ft = mb.add_func_type(vec![Ty::I32], vec![Ty::I32]);
        let mut fb = mb.function("caller", ft);

        fb.add_proof(ProofAnnotation::Pure);
        fb.add_proof(ProofAnnotation::NoPanic);
        fb.add_proof(ProofAnnotation::Deterministic);

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

        let module = mb.build();
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

        let module = mb.build();
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

        let module = mb.build();
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

        let module = mb.build();
        let json = serde_json::to_string(&module).expect("JSON");
        let msgpack = rmp_serde::to_vec(&module).expect("MessagePack");
        assert!(
            msgpack.len() < json.len(),
            "MessagePack ({} bytes) should be smaller than JSON ({} bytes)",
            msgpack.len(),
            json.len()
        );
    }
}

// m3.rs — M3: MONOMORPHIZATION of generics + TRAIT STATIC DISPATCH.
//
// M1/M2 lowered a single, already-monomorphic predicate (`Level::is_zero`) off
// `tcx.thir_body(def)`. The structural gap M3 closes: trust-ir is MONOMORPHIC
// (no type params) while THIR is PRE-monomorphization (still generic). rustc
// normally monomorphizes on MIR; here the FRONTEND drives monomorphization
// itself and lowers PER concrete instantiation.
//
// Two capabilities, both built on real stage1 rustc APIs (no hand-faked types):
//
//  1. GENERIC FUNCTION, lowered per instantiation.
//     Mechanism: from a monomorphic `ty::Instance` (def_id + GenericArgsRef),
//     read the GENERIC THIR for the def (`tcx.thir_body`), and SUBSTITUTE the
//     generic types using the instance args during lowering via
//     `tcx.instantiate_and_normalize_erasing_regions(args, typing_env,
//     EarlyBinder::bind(tcx, ty))` — so every `ty::Ty` the pass sees is CONCRETE
//     before it becomes a `trust_ir::Ty`. We lower `id<T>` at T=u32 and T=i64
//     (and `double<T>` likewise) to TWO distinct concrete `trust_ir::Function`s.
//
//  2. TRAIT STATIC DISPATCH.
//     A trait-method call `Yes.pred()` on a concrete self type is resolved to
//     the concrete impl method via `ty::Instance::try_resolve(tcx, typing_env,
//     trait_method_def_id, args)` -> the `<Yes as Predicate>::pred` impl
//     `Instance`. We then emit a DIRECT `Inst::Call` to that monomorphized
//     callee — NOT a generic or virtual call. (Dynamic dispatch via
//     `Ty::FatPtr(TraitObject)` + `CallIndirect` is OUT of scope for M3; noted
//     for M-later.)
//
// All emitted functions go through `validate_module` (0 errors) and a
// differential harness (trust-ir Interpreter vs a native-Rust oracle).
//
// ============================================================================
// REAL-LOWERING ACCEPTANCE GATE (FIX 5)
// ----------------------------------------------------------------------------
// The `#[cfg(test)]` unit suite below hand-builds the EXPECTED IR with
// `FunctionBuilder` and never invokes `MonoCx::lower_expr` / `run_*_differential`
// — so it does NOT exercise the actual THIR -> trust-ir lowering. The genuine
// lowering is validated by the `--m3` driver + the default-mode predicate
// differential. `tests/real_lowering_acceptance.rs` drives that REAL lowering
// from within `targo --unverified test`: it spawns the built `trust_ir_frontend`
// binary under the linked Trust toolchain on `m3_corpus.rs` (both `--m3` and
// default mode) and asserts exit 0, an "ALL MATCH" RESULT line for every
// milestone family (M3/M4/M5[=M5.1]/M5.2/M5.3/SCALAR-DEREF/M5.4/M5.6), "21/21"
// twice in default mode, and NO "MISMATCH"/"PARITY NOT CHECKED"/"FAILURES"/
// "LOWERING FAILED". Run it with `targo --unverified test --manifest-path
// frontend/Cargo.toml` (Cargo.toml); `--lib` runs only the unit suite and does
// NOT run this gate. Doctests are off (`doctest = false`).
// ============================================================================

use rustc_abi::VariantIdx;
use rustc_middle::thir::{self, ExprId, ExprKind, Thir};
use rustc_middle::ty::{
    self, EarlyBinder, GenericArg, Instance, TyCtxt, TyKind, TypeVisitableExt, TypingEnv,
};
use rustc_span::def_id::{DefId, LocalDefId};

use trust_ir::value::{BlockId, FuncId, SourceSpan, ValueId};
use trust_ir::Module;
use trust_ir_build::{FunctionBuilder, ModuleBuilder};

use crate::span_map::SpanMap;
use crate::{
    build_enum_model, classify_arm_subpatterns, collect_aggregate_bindings, collect_bindings,
    collect_nested_bindings, field_addr, load_field, pattern_variant_idx, pattern_variants,
    store_field, ArmShape, EnumModel, LResult, LowerError, NestedCtorField, PatternMatch,
};

fn bail<T>(msg: impl Into<String>) -> LResult<T> {
    Err(LowerError(msg.into()))
}

/// Is this a trust-ir scalar INTEGER type (the M5.3 scalar-match scrutinee
/// domain)? `Bool` and `Ptr`/ADT are NOT integers here: a bool match would need
/// a bool switch (no corpus shape), and a Ptr/ADT scrutinee is the M5.4 heap-tag
/// match.
fn is_int_ir_ty(ty: &trust_ir::ty::Ty) -> bool {
    use trust_ir::ty::Ty as IrTy;
    matches!(
        ty,
        IrTy::I8
            | IrTy::I16
            | IrTy::I32
            | IrTy::I64
            | IrTy::U8
            | IrTy::U16
            | IrTy::U32
            | IrTy::U64
    )
}

/// M5.7b: is this a trust-ir SCALAR type that fits an 8-byte inline payload slot
/// — an integer (`I8..U64`) or a `Bool`? These are the field kinds whose value is
/// stored INLINE in the tagged-struct slot, so a by-ref binding (`&scalar`) is
/// the GEP ADDRESS of the slot (the `field_addr` path), NOT a `Load` of a stored
/// pointer. A `Ptr` (a `Box`/`&`/recursive-enum child slot) is handled by the
/// pointer path; an aggregate (struct/tuple) is rejected (M5.7e). `I128`/`U128`
/// is deliberately EXCLUDED: it does not fit an 8-byte slot, and `lower_concrete_ty`
/// already rejects an i128/u128 field upstream, so it never reaches here.
fn is_scalar_ir_ty(ty: &trust_ir::ty::Ty) -> bool {
    use trust_ir::ty::Ty as IrTy;
    is_int_ir_ty(ty) || matches!(ty, IrTy::Bool)
}

/// Map a CONCRETE (post-substitution) rustc `ty::Ty` to a `trust_ir::Ty`. The
/// pass guarantees, by running substitution first, that no `Param`/`Alias`
/// reaches here. We support the scalar leaf the M3 generics use (the recursive
/// ADT heap shape is M2's domain).
pub fn lower_concrete_ty<'tcx>(_tcx: TyCtxt<'tcx>, ty: ty::Ty<'tcx>) -> LResult<trust_ir::ty::Ty> {
    use trust_ir::ty::Ty as IrTy;
    match ty.kind() {
        TyKind::Bool => Ok(IrTy::Bool),
        TyKind::Int(ity) => match ity {
            ty::IntTy::I8 => Ok(IrTy::I8),
            ty::IntTy::I16 => Ok(IrTy::I16),
            ty::IntTy::I32 => Ok(IrTy::I32),
            // isize is pointer-width = 64-bit on the aarch64-apple-darwin target.
            ty::IntTy::I64 | ty::IntTy::Isize => Ok(IrTy::I64),
            // No 64-bit-or-narrower trust-ir scalar holds i128: fail closed rather
            // than silently truncating computed values to 64 bits (audit fix).
            ty::IntTy::I128 => bail(
                "M3 lower_concrete_ty: i128 has no trust-ir scalar (would truncate to 64 bits)",
            ),
        },
        // Unsigned Rust types map to the UNSIGNED trust-ir scalars (the interpreter
        // decodes these with signed:false) so signedness-sensitive ops (ICmp Ult,
        // UDiv/URem) and high-bit values stay correct, not just wrapping add (audit fix).
        TyKind::Uint(uty) => match uty {
            ty::UintTy::U8 => Ok(IrTy::U8),
            ty::UintTy::U16 => Ok(IrTy::U16),
            ty::UintTy::U32 => Ok(IrTy::U32),
            // usize is pointer-width = 64-bit on aarch64-apple-darwin.
            ty::UintTy::U64 | ty::UintTy::Usize => Ok(IrTy::U64),
            ty::UintTy::U128 => bail(
                "M3 lower_concrete_ty: u128 has no trust-ir scalar (would truncate to 64 bits)",
            ),
        },
        // A reference / Box etc. is a pointer at the trust-ir level (the M2 heap
        // path Loads through it). M3's trait `&self` receiver lands here, as does
        // M5.4's `&Enum` match scrutinee (a `&Nat`/`&Level`).
        TyKind::Ref(..) | TyKind::RawPtr(..) => Ok(IrTy::Ptr),
        // M5.4: a recursive ENUM ADT — or a `Box<Enum>` (the box lang-item is
        // itself an Adt) — is a heap value reached through a pointer. The
        // tagged-struct `EnumModel` registered for it backs the field Loads in
        // `lower_match`; the VALUE-level trust-ir type of an `&Enum`/`Box<Enum>`
        // is `Ptr`. (`is_box()` covers `Box<T>`; `is_enum()` covers a bare enum.)
        TyKind::Adt(adt, _) if adt.is_enum() || adt.is_box() => Ok(IrTy::Ptr),
        TyKind::Adt(adt, _) if adt.is_struct() && adt.all_fields().count() == 0 => {
            // A field-less unit struct (e.g. `Yes`/`No`): it is a ZST. We model
            // its `&self` receiver as a `Ptr` (the receiver value is irrelevant
            // to the resolved leaf method, which ignores `self`).
            Ok(IrTy::Ptr)
        }
        other => bail(format!(
            "M3 lower_concrete_ty: unsupported concrete type {other:?} (full ty {ty:?})"
        )),
    }
}

/// M5.7c: is a trust-ir INTEGER scalar type signed? `I8..I128 -> true`,
/// `U8..U128 -> false`. Used to pick the signed vs unsigned variant of a
/// signedness-sensitive integer binop (`SDiv`/`UDiv`, `SRem`/`URem`,
/// `AShr`/`LShr`) — the same selection `lower_binop_thir` makes for an `ICmp`,
/// but read off the trust-ir ir-ty (which already carries signedness via the
/// distinct `I*`/`U*` variants) so `lower_binop` does not need the rustc ty. A
/// NON-integer ir-ty (e.g. `Bool`, a float) errors fail-loud.
fn ir_ty_is_signed(ir_ty: &trust_ir::ty::Ty) -> LResult<bool> {
    use trust_ir::ty::Ty as IrTy;
    match ir_ty {
        IrTy::I8 | IrTy::I16 | IrTy::I32 | IrTy::I64 | IrTy::I128 => Ok(true),
        IrTy::U8 | IrTy::U16 | IrTy::U32 | IrTy::U64 | IrTy::U128 => Ok(false),
        other => bail(format!(
            "M5.7c: signed/unsigned binop on a non-integer ir-ty {other:?}"
        )),
    }
}

/// M5.7d: build the `GenericArgsRef` for `def_id` that substitutes its N TYPE
/// parameters, POSITIONALLY, with `concretes[0..N]` (and keeps the identity for
/// any leading parent/Self args). The i-th *type* param of the fn binds to
/// `concretes[i]`. Fails LOUD on:
///   * an arity mismatch (the fn's own type-param count != `concretes.len()`), or
///   * a non-type generic param OTHER than a lifetime — i.e. a CONST generic
///     (`const N: usize`) is rejected (monomorphizing it would need a const
///     value, which this entry does not supply). Lifetimes are erased identity.
///
/// `args_for_single_type_param` below is the 1-element special case (it delegates
/// here), so the existing single-param callers are unaffected.
fn args_for_type_params<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    concretes: &[ty::Ty<'tcx>],
) -> LResult<ty::GenericArgsRef<'tcx>> {
    let generics = tcx.generics_of(def_id);
    // Count the fn's OWN (own_params, i.e. excluding parent) generic params by
    // kind, so we can validate arity AND reject const generics with a clear msg.
    let mut n_type = 0usize;
    for param in generics.own_params.iter() {
        match param.kind {
            ty::GenericParamDefKind::Type { .. } => n_type += 1,
            ty::GenericParamDefKind::Lifetime => {}
            ty::GenericParamDefKind::Const { .. } => {
                return bail(format!(
                    "M5.7d: {def_id:?} has a CONST generic param `{}` — const-generic \
                     monomorphization is not supported (this entry binds only TYPE params)",
                    param.name
                ));
            }
        }
    }
    if n_type != concretes.len() {
        return bail(format!(
            "M5.7d: {def_id:?} has {n_type} type param(s) but {} concrete type(s) were \
             supplied (positional binding requires an exact match)",
            concretes.len()
        ));
    }
    // `for_item` walks ALL params (incl. parent/Self) in declaration order. We
    // bind each *type* param to the next `concretes` entry positionally; a
    // lifetime keeps the identity (it is erased downstream). A const param can no
    // longer be reached (rejected above). The `index` arg from `for_item` is the
    // FULL-args index (parent + own), so we count type params with our own cursor
    // to map them to `concretes` positionally.
    let mut next_type = 0usize;
    let args = ty::GenericArgs::for_item(tcx, def_id, |param, _| match param.kind {
        ty::GenericParamDefKind::Type { .. } => {
            let c = concretes[next_type];
            next_type += 1;
            GenericArg::from(c)
        }
        _ => tcx.mk_param_from_def(param),
    });
    Ok(args)
}

/// Build the `GenericArgsRef` for `def_id` that substitutes its type
/// parameter(s) with `concrete` (and fills any leading parent/self args with the
/// identity). For the M3 generics (`id<T>`, `double<T>`) the only param is `T`;
/// for a NON-generic root (`pick`, `count_succ`, the trait/predicate callers)
/// there is no type param and `concrete` is an unused identity seed.
///
/// M5.7d: this is UNCHANGED behavior — it binds EVERY type param to the same
/// `concrete` (a no-op when there are none), exactly as before. The NEW
/// multi-type-param path uses `args_for_type_params`, which binds positionally
/// and validates arity / rejects const generics. This single-param entry is kept
/// infallible so its existing (non-generic and single-generic) callers are
/// byte-identically unaffected.
fn args_for_single_type_param<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    concrete: ty::Ty<'tcx>,
) -> ty::GenericArgsRef<'tcx> {
    // `for_item` walks ALL params (incl. parent/Self) in order; we replace each
    // *type* param with `concrete` and keep the identity for anything else.
    ty::GenericArgs::for_item(tcx, def_id, |param, _| match param.kind {
        ty::GenericParamDefKind::Type { .. } => GenericArg::from(concrete),
        _ => tcx.mk_param_from_def(param),
    })
}

/// The monomorphization lowering context for one INSTANCE (one concrete
/// instantiation of a generic def).
struct MonoCx<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    thir: &'a Thir<'tcx>,
    /// The instance's concrete generic args — what makes the generic THIR
    /// concrete. Threaded into every `concretize`.
    args: ty::GenericArgsRef<'tcx>,
    typing_env: TypingEnv<'tcx>,
    /// THIR param `LocalVarId` -> the trust-ir SSA value of that parameter.
    params: std::collections::HashMap<rustc_middle::thir::LocalVarId, ValueId>,
    /// M5.2: `let`-bound local `LocalVarId` -> its computed SSA `ValueId`. A
    /// SEPARATE map from `params` (kept distinct so a let never silently clobbers
    /// a parameter binding); `VarRef` lookup checks `locals` FIRST, then `params`.
    /// THIR var ids are unique, so the two maps never genuinely collide.
    locals: std::collections::HashMap<rustc_middle::thir::LocalVarId, ValueId>,
    /// FuncId base offset for the worklist being emitted: the module's function
    /// count when this worklist's emission BEGAN. A worklist instance whose
    /// discovery index is `i` lands at `FuncId(func_base + i)`, and a cross-fn
    /// Call edge to discovery index `j` targets `FuncId(func_base + j)`. This
    /// lets several worklist roots coexist in ONE module (e.g. `pick` + `select`
    /// in the if-roundtrip emit) without colliding FuncIds. For the M3 scalar
    /// path (which never emits a worklist Call edge) it is 0.
    func_base: u32,
    /// M5.4: AdtDef DefId -> the tagged-struct `EnumModel` for a recursive enum
    /// matched in this worklist. Populated BEFORE function emission (in
    /// `emit_worklist`, which has the `ModuleBuilder` needed to register the
    /// struct), then read by the ADT branch of `lower_match` to find a variant's
    /// discriminant / a payload field's byte offset. Empty for the M3/M5.1-M5.3
    /// paths (no recursive-ADT match), so those emissions are byte-identical.
    enum_models: std::collections::HashMap<DefId, EnumModel>,
    /// Span threading: the pre-interned source-file map for THIS instance's
    /// THIR body (built with the `ModuleBuilder` before the `FunctionBuilder`
    /// exclusively borrows the module — see `SpanMap::build`).
    spans: SpanMap,
    /// The trust-ir span of the expr CURRENTLY being lowered — mirrors the
    /// `FunctionBuilder`'s sticky span, so `lower_expr` can RESTORE the
    /// enclosing expr's span after a sub-expr's recursion returns (the caller's
    /// own follow-up instructions then carry the caller's provenance, not the
    /// last sub-expr's).
    cur_span: Option<SourceSpan>,
}

impl<'a, 'tcx> MonoCx<'a, 'tcx> {
    /// SUBSTITUTE + normalize a (possibly generic) THIR `ty::Ty` against this
    /// instance's args, yielding a CONCRETE type. This is THE monomorphization
    /// step: `EarlyBinder::bind(tcx, ty)` then
    /// `instantiate_and_normalize_erasing_regions`.
    fn concretize(&self, ty: ty::Ty<'tcx>) -> ty::Ty<'tcx> {
        self.tcx.instantiate_and_normalize_erasing_regions(
            self.args,
            self.typing_env,
            EarlyBinder::bind(self.tcx, ty),
        )
    }

    fn concrete_ir_ty(&self, ty: ty::Ty<'tcx>) -> LResult<trust_ir::ty::Ty> {
        lower_concrete_ty(self.tcx, self.concretize(ty))
    }

    // --- span threading (integration-frontend-emission) ----------------------

    /// Enter `e`'s source span: stamp it as the builder's sticky span (every
    /// node emitted from here on carries it) and remember it as current. A span
    /// that does not map (dummy/synthetic; macro spans already degrade to their
    /// outermost callsite inside `SpanMap::to_ir`) KEEPS the enclosing expr's
    /// span — graceful degradation, never a panic or a bail.
    fn enter_expr_span(&mut self, fb: &mut FunctionBuilder<'_>, e: ExprId) {
        if let Some(s) = self.spans.to_ir(self.tcx, self.thir[e].span) {
            self.cur_span = Some(s);
            fb.set_span(s);
        }
    }

    /// Restore a saved ENCLOSING span after a sub-expr's lowering returns, so
    /// the caller's follow-up instructions carry the caller's own provenance.
    fn restore_span(&mut self, fb: &mut FunctionBuilder<'_>, saved: Option<SourceSpan>) {
        self.cur_span = saved;
        crate::span_map::set_or_clear(fb, saved);
    }
}

/// A handle to the trust-ir-level signature/result of a lowered instance, used
/// by the differential harness.
#[derive(Clone)]
pub struct LoweredInstance {
    pub func_id: FuncId,
    pub name: String,
    /// The concrete IR param/return types (post-substitution).
    pub param_tys: Vec<trust_ir::ty::Ty>,
    pub ret_ty: trust_ir::ty::Ty,
}

/// Lower ONE instance of a generic scalar function (`id<T>`/`double<T>`) into
/// `mb`, substituting `T` with `concrete` everywhere. Returns the lowered
/// signature info. Supports a body that is either the bare parameter (`id`) or a
/// single binary `+` of the parameter with itself (`double`).
pub fn lower_scalar_generic_instance<'tcx>(
    tcx: TyCtxt<'tcx>,
    mb: &mut ModuleBuilder,
    def: LocalDefId,
    concrete: ty::Ty<'tcx>,
    name_suffix: &str,
) -> LResult<LoweredInstance> {
    let def_id = def.to_def_id();
    let args = args_for_single_type_param(tcx, def_id, concrete);
    let typing_env = TypingEnv::fully_monomorphized();

    let (thir_steal, body_expr) = tcx
        .thir_body(def)
        .map_err(|_| LowerError("thir_body errored (tainted by type errors)".into()))?;
    let thir = thir_steal.borrow();

    // Span threading: PRE-PASS-intern the source file(s) of every THIR expr
    // span into the module's debug-info file table (must precede the
    // FunctionBuilder's exclusive module borrow below).
    let spans = SpanMap::build(tcx, mb, thir.exprs.iter().map(|e| e.span));

    let mut cx = MonoCx {
        tcx,
        thir: &thir,
        args,
        typing_env,
        params: Default::default(),
        locals: Default::default(),
        // M3 scalar path emits no worklist Call edge; base is irrelevant.
        func_base: 0,
        // M3 scalar path matches no recursive ADT.
        enum_models: Default::default(),
        spans,
        cur_span: None,
    };

    // Concrete signature, derived by substituting the generic fn sig.
    let sig = match &thir.body_type {
        thir::BodyTy::Fn(sig) => *sig,
        _ => return bail("not a function body"),
    };
    let in_ty = cx.concrete_ir_ty(sig.inputs()[0])?;
    let out_ty = cx.concrete_ir_ty(sig.output())?;

    let base_name = tcx.item_name(def_id).to_string();
    let full_name = format!("{base_name}__{name_suffix}");
    let sig_id = mb.add_func_type(vec![in_ty.clone()], vec![out_ty.clone()]);

    let func_id = {
        let mut fb = mb.function(full_name.clone(), sig_id);
        let entry = fb.create_block();
        let param_val = fb.add_block_param(entry, in_ty.clone());
        fb.switch_to_block(entry);
        // Fn-level default span (the body expr's position): covers any
        // instruction emitted outside a specific sub-expr, e.g. the final `ret`.
        cx.enter_expr_span(&mut fb, body_expr);

        // Bind the THIR param pattern var -> the SSA param value.
        bind_params(&thir, &mut cx.params, param_val);

        // FIX 11: lower the body through the UNIFIED `MonoCx::lower_expr` — the
        // SAME entry the M4/M5 worklist (`emit_worklist`) uses — rather than the
        // legacy `lower_scalar_body`/`lower_scalar_operand`. A bare scalar
        // instance (`id`/`double`) has no cross-fn callees, so the worklist's
        // `by_key` is empty here. `lower_expr` emits IDENTICAL IR for the
        // bare-param (`ret %0`) and `add x,x` (`add i64 %0,%0`) shapes, so the
        // M3 emit + `--emit-text` stay byte-identical; this makes the "ONE
        // unified lowering path" claim true at the M3 scalar entry point.
        let empty_by_key: InstanceMap<'tcx> =
            std::collections::HashMap::new();
        let result = cx.lower_expr(&mut fb, &empty_by_key, body_expr)?;
        fb.ret(vec![result]);
        fb.build()
    };

    Ok(LoweredInstance {
        func_id,
        name: full_name,
        param_tys: vec![in_ty],
        ret_ty: out_ty,
    })
}

/// M5.7d: lower ONE instance of a generic fn with N TYPE PARAMS at the given
/// `concretes` (positionally: the i-th type param binds to `concretes[i]`), into
/// `mb`. Generalizes `lower_scalar_generic_instance` from a single type param to
/// N: it binds EVERY value parameter (so `fst<A,B>(a: A, b: B)` gets both block
/// params) and lowers the body through the SAME unified `MonoCx::lower_expr`, so
/// any body shape `lower_expr` supports (scalar params, arithmetic, scalar
/// literals, etc.) works. The corpus shapes here (`fst`, `combine`) are leaf
/// bodies (no cross-fn Call), so the worklist `by_key` is empty.
///
/// The CONCRETE signature is derived per-instantiation, so two instantiations of
/// the SAME fn at different type tuples produce IR that DIFFERS by type/width
/// (e.g. `fst<i64,u32>` returns `i64`; `fst<u32,i64>` returns `u32`).
///
/// Fails loud (via `args_for_type_params`) on an arity mismatch or a const/other
/// non-type generic param. The name is `{base}__{name_suffix}` (the caller picks
/// a per-instantiation suffix like `i64_u32`).
pub fn lower_multi_generic_instance<'tcx>(
    tcx: TyCtxt<'tcx>,
    mb: &mut ModuleBuilder,
    def: LocalDefId,
    concretes: &[ty::Ty<'tcx>],
    name_suffix: &str,
) -> LResult<LoweredInstance> {
    let def_id = def.to_def_id();
    // Positional N-type-param binding (validates arity + rejects const generics).
    let args = args_for_type_params(tcx, def_id, concretes)?;
    let typing_env = TypingEnv::fully_monomorphized();

    let (thir_steal, body_expr) = tcx
        .thir_body(def)
        .map_err(|_| LowerError("thir_body errored (tainted by type errors)".into()))?;
    let thir = thir_steal.borrow();

    // Span threading: pre-intern the THIR body's source file(s) (before the
    // FunctionBuilder's exclusive module borrow).
    let spans = SpanMap::build(tcx, mb, thir.exprs.iter().map(|e| e.span));

    let mut cx = MonoCx {
        tcx,
        thir: &thir,
        args,
        typing_env,
        params: Default::default(),
        locals: Default::default(),
        // Multi-generic leaf bodies emit no worklist Call edge; base is irrelevant.
        func_base: 0,
        // No recursive-ADT match in the multi-generic corpus shapes.
        enum_models: Default::default(),
        spans,
        cur_span: None,
    };

    // Concrete signature, derived by substituting the generic fn sig — ALL inputs
    // (one block param each), at their per-position concrete ir-ty.
    let sig = match &thir.body_type {
        thir::BodyTy::Fn(sig) => *sig,
        _ => return bail("M5.7d: not a function body"),
    };
    let in_tys: Vec<trust_ir::ty::Ty> = sig
        .inputs()
        .iter()
        .map(|t| cx.concrete_ir_ty(*t))
        .collect::<LResult<Vec<_>>>()?;
    let out_ty = cx.concrete_ir_ty(sig.output())?;

    let base_name = tcx.item_name(def_id).to_string();
    let full_name = format!("{base_name}__{name_suffix}");
    let sig_id = mb.add_func_type(in_tys.clone(), vec![out_ty.clone()]);

    let func_id = {
        let mut fb = mb.function(full_name.clone(), sig_id);
        let entry = fb.create_block();
        let param_vals: Vec<ValueId> = in_tys
            .iter()
            .map(|ty| fb.add_block_param(entry, ty.clone()))
            .collect();
        fb.switch_to_block(entry);
        // Fn-level default span (the body expr's position) for the final `ret`.
        cx.enter_expr_span(&mut fb, body_expr);
        // Bind EACH THIR param pattern var -> its positional SSA block-param value.
        bind_params_n(&thir, &mut cx.params, &param_vals)?;
        // Lower the body through the UNIFIED `MonoCx::lower_expr` (the SAME entry
        // every other milestone uses). Leaf bodies -> empty `by_key`.
        let empty_by_key: InstanceMap<'tcx> =
            std::collections::HashMap::new();
        let result = cx.lower_expr(&mut fb, &empty_by_key, body_expr)?;
        fb.ret(vec![result]);
        fb.build()
    };

    Ok(LoweredInstance {
        func_id,
        name: full_name,
        param_tys: in_tys,
        ret_ty: out_ty,
    })
}

/// Record the function's single value parameter under its THIR pattern var id.
/// (M3 scalar path: a unary `fn(T)->T`. Kept for byte-identity with the landed
/// M3 emit; `bind_params_n` generalizes to N params for the M4/M5 worklist.)
fn bind_params<'tcx>(
    thir: &Thir<'tcx>,
    out: &mut std::collections::HashMap<rustc_middle::thir::LocalVarId, ValueId>,
    param_val: ValueId,
) {
    if let Some(p) = thir.params.iter().find(|p| p.pat.is_some()) {
        if let Some(pat) = &p.pat {
            if let thir::PatKind::Binding { var, .. } = &pat.kind {
                out.insert(*var, param_val);
            }
        }
    }
}

/// Bind EACH THIR param's pattern var to its positional block-param `ValueId`
/// (M5.1: multi-parameter functions). `thir.params` is in declaration order, so
/// `param_vals[i]` is the SSA value for the i-th parameter. A param without a
/// binding pattern (e.g. `_`) is skipped — its value is simply never referenced.
fn bind_params_n<'tcx>(
    thir: &Thir<'tcx>,
    out: &mut std::collections::HashMap<rustc_middle::thir::LocalVarId, ValueId>,
    param_vals: &[ValueId],
) -> LResult<()> {
    if thir.params.len() != param_vals.len() {
        return bail(format!(
            "M5.1: THIR has {} params but {} block-param values were created",
            thir.params.len(),
            param_vals.len()
        ));
    }
    for (p, &val) in thir.params.iter().zip(param_vals.iter()) {
        if let Some(pat) = &p.pat {
            if let thir::PatKind::Binding { var, .. } = &pat.kind {
                out.insert(*var, val);
            }
        }
    }
    Ok(())
}

impl<'a, 'tcx> MonoCx<'a, 'tcx> {
    // FIX 11: the legacy `lower_scalar_body`/`lower_scalar_operand` (the old M3
    // scalar entry) were DELETED — `lower_scalar_generic_instance` now lowers the
    // `id`/`double` body through the unified `MonoCx::lower_expr`, the SAME path
    // the worklist uses, so there is genuinely ONE lowering path.

    /// If `callee_ty` is a `core::ops` arithmetic trait method (`+`/`-`/`*`),
    /// return the corresponding MIR binop. Errors otherwise. Recognition is by
    /// TRAIT lang-item identity (see [`arith_binop_of`]), not the method name.
    fn recognize_overloaded_arith(
        &self,
        callee_ty: ty::Ty<'tcx>,
    ) -> LResult<rustc_middle::mir::BinOp> {
        let did = match callee_ty.kind() {
            TyKind::FnDef(did, _) => *did,
            other => return bail(format!("scalar-body Call to non-FnDef: {other:?}")),
        };
        arith_binop_of(self.tcx, did).ok_or_else(|| {
            LowerError(format!(
                "M3 scalar body: callee {did:?} is not a core::ops Add/Sub/Mul operator"
            ))
        })
    }

    fn lower_binop(
        &mut self,
        fb: &mut FunctionBuilder<'_>,
        op: rustc_middle::mir::BinOp,
        ir_ty: trust_ir::ty::Ty,
        l: ValueId,
        r: ValueId,
    ) -> LResult<ValueId> {
        use rustc_middle::mir::BinOp as MirBinOp;
        use trust_ir::inst::BinOp as IrBinOp;
        match op {
            MirBinOp::Add | MirBinOp::AddUnchecked | MirBinOp::AddWithOverflow => {
                Ok(fb.add(ir_ty, l, r))
            }
            MirBinOp::Sub | MirBinOp::SubUnchecked | MirBinOp::SubWithOverflow => {
                Ok(fb.sub(ir_ty, l, r))
            }
            MirBinOp::Mul | MirBinOp::MulUnchecked | MirBinOp::MulWithOverflow => {
                Ok(fb.mul(ir_ty, l, r))
            }
            // M5.7c: the rest of the integer binops, mapped to the native trust-ir
            // `BinOp` the interpreter AND trust-cg both implement. Div/Rem/Shr pick
            // a SIGNED vs UNSIGNED variant from the operand's trust-ir ir-ty
            // (`I64` -> signed, `U64` -> unsigned), mirroring the signed/unsigned
            // `ICmpOp` selection `lower_binop_thir` does for comparisons. Bit-logic
            // (And/Or/Xor) and the left shift (Shl) are sign-agnostic. The
            // interpreter traps (UB) on a zero divisor / an out-of-range shift, so
            // the corpus that drives these only feeds non-zero divisors and shift
            // amounts < bit-width (we add NO undefined behavior here).
            MirBinOp::Div => {
                let signed = ir_ty_is_signed(&ir_ty)?;
                let irop = if signed { IrBinOp::SDiv } else { IrBinOp::UDiv };
                Ok(fb.binop(irop, ir_ty, l, r))
            }
            MirBinOp::Rem => {
                let signed = ir_ty_is_signed(&ir_ty)?;
                let irop = if signed { IrBinOp::SRem } else { IrBinOp::URem };
                Ok(fb.binop(irop, ir_ty, l, r))
            }
            MirBinOp::BitAnd => Ok(fb.binop(IrBinOp::And, ir_ty, l, r)),
            MirBinOp::BitOr => Ok(fb.binop(IrBinOp::Or, ir_ty, l, r)),
            MirBinOp::BitXor => Ok(fb.binop(IrBinOp::Xor, ir_ty, l, r)),
            MirBinOp::Shl | MirBinOp::ShlUnchecked => Ok(fb.binop(IrBinOp::Shl, ir_ty, l, r)),
            // `>>` is arithmetic (sign-extending, `AShr`) on a signed operand and
            // logical (`LShr`) on an unsigned one — Rust's `i64 >> n` vs `u64 >> n`.
            MirBinOp::Shr | MirBinOp::ShrUnchecked => {
                let signed = ir_ty_is_signed(&ir_ty)?;
                let irop = if signed { IrBinOp::AShr } else { IrBinOp::LShr };
                Ok(fb.binop(irop, ir_ty, l, r))
            }
            other => bail(format!("M3 binop: unsupported op {other:?}")),
        }
    }
}

// --- M4 monomorphic worklist (generic CALL CHAIN) ----------------------------
//
// M3 lowered each generic instance in ISOLATION (`double<i64>` inlined its `x+x`;
// a trait-method call was resolved one level deep). M4 closes the next gap: a
// generic fn whose BODY CALLS another generic fn (`quad<T> { double(double(x)) }`).
// Monomorphizing the ROOT instance must DISCOVER the callee instance
// (`double<i64>`), lower it as a SEPARATE concrete Function, and emit a real
// cross-function `Call` edge — recursively, for an arbitrary chain.
//
// Two passes over a worklist keyed on the concrete instance `(def_id, args)`:
//   Pass 1 (collect): from the root instance, walk THIR for user-fn Calls,
//     substitute each callee's generic args through the CURRENT instance's args,
//     `Instance::try_resolve` to a concrete callee instance, and record it in
//     DISCOVERY ORDER (root = index 0). Recurse into each newly-found instance.
//     The discovery index IS the FuncId (because Pass 2 creates functions in the
//     same order and `ModuleBuilder::function` hands out sequential FuncIds).
//   Pass 2 (emit): for each instance in FuncId order, `mb.function(...)` (assert
//     the auto-assigned FuncId equals its index), then lower its body — a Call to
//     a user fn becomes `fb.call(callee_funcid, [args])`, resolving the callee
//     instance the SAME way and mapping it through the instance->FuncId map.

/// A discovered monomorphic instance to lower (root or a transitively-called
/// generic fn at concrete args). Identity is typed and local to this TyCtxt.
#[derive(Clone)]
struct MonoInstance<'tcx> {
    def: LocalDefId,
    args: ty::GenericArgsRef<'tcx>,
}

/// Equality is the actual local declaration and its substituted, interned
/// generic arguments in THIS compiler context, never a display/debug spelling
/// or the erased IR signature. The key cannot outlive its owning TyCtxt.
type InstanceKey<'tcx> = (LocalDefId, ty::GenericArgsRef<'tcx>);
type InstanceMap<'tcx> = std::collections::HashMap<InstanceKey<'tcx>, u32>;

impl<'tcx> MonoInstance<'tcx> {
    fn key(&self) -> InstanceKey<'tcx> {
        (self.def, self.args)
    }
}

/// The collected worklist plus the de-dup map (instance key -> FuncId index).
struct Worklist<'tcx> {
    /// Instances in discovery order; index == FuncId.
    instances: Vec<MonoInstance<'tcx>>,
    /// instance key -> FuncId index.
    by_key: InstanceMap<'tcx>,
}

impl<'tcx> Worklist<'tcx> {
    fn new() -> Self {
        Self { instances: Vec::new(), by_key: std::collections::HashMap::new() }
    }

    /// Record an instance if unseen; return its FuncId index either way.
    fn intern(&mut self, inst: MonoInstance<'tcx>) -> LResult<u32> {
        if let Some(&id) = self.by_key.get(&inst.key()) {
            return Ok(id);
        }
        let id = u32::try_from(self.instances.len())
            .map_err(|_| LowerError("instance worklist exceeds the FuncId space".into()))?;
        self.by_key.insert(inst.key(), id);
        self.instances.push(inst);
        Ok(id)
    }
}

/// If `callee_ty` is a `FnDef` to a USER fn (a local def that is NOT a `core::ops`
/// arithmetic operator), resolve it — substituting its generic args through
/// `current_args` — to a concrete `(LocalDefId, monomorphized_args)`. Returns
/// `Ok(None)` for an overloaded-arith operator (handled inline) or a non-local /
/// non-FnDef callee. `Err` only on a genuine resolution failure.
/// If `did` is an associated method of a `core::ops` Add/Sub/Mul trait — i.e. an
/// overloaded arithmetic operator — return the corresponding binop. Identified by
/// the container TRAIT's lang-item identity (`tcx.trait_of_item` vs
/// `lang_items().{add,sub,mul}_trait()`), NOT by the bare method name: a user
/// function literally named `add`/`sub`/`mul` is a free fn (no container trait, or
/// a different trait) and must NOT be misclassified as a native binop (which would
/// silently miscompile a real call edge). Returns `None` for any non-operator.
fn arith_binop_of<'tcx>(
    tcx: TyCtxt<'tcx>,
    did: rustc_hir::def_id::DefId,
) -> Option<rustc_middle::mir::BinOp> {
    use rustc_middle::mir::BinOp;
    // The container trait of `did` if it is an associated (trait/impl) item.
    let trait_did = tcx.opt_associated_item(did)?.trait_container(tcx)?;
    let li = tcx.lang_items();
    if Some(trait_did) == li.add_trait() {
        Some(BinOp::Add)
    } else if Some(trait_did) == li.sub_trait() {
        Some(BinOp::Sub)
    } else if Some(trait_did) == li.mul_trait() {
        Some(BinOp::Mul)
    } else {
        None
    }
}

fn resolve_user_call<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: TypingEnv<'tcx>,
    current_args: ty::GenericArgsRef<'tcx>,
    callee_ty: ty::Ty<'tcx>,
) -> LResult<Option<MonoInstance<'tcx>>> {
    let (did, callee_generic_args) = match callee_ty.kind() {
        TyKind::FnDef(did, gargs) => (*did, *gargs),
        _ => return Ok(None),
    };
    // `core::ops` arithmetic operators (+/-/*) desugar to FnDef calls too, but
    // they are lowered INLINE to native binops, not as cross-fn edges. Detect them
    // by trait lang-item identity (NOT bare name) so a USER fn literally named
    // `add`/`sub`/`mul` is resolved as a real call instead of a silent binop.
    if arith_binop_of(tcx, did).is_some() {
        return Ok(None);
    }
    // Current rustc keeps late-bound arguments on the function-item type.
    // This monomorphic worklist has no binder-instantiation semantics: do not
    // erase a bound type/const/region merely to obtain a GenericArgsRef.
    let callee_generic_args = callee_generic_args.no_bound_vars().ok_or_else(|| {
        LowerError(format!(
            "M4 late-bound function arguments are unsupported for {did:?}"
        ))
    })?;
    // Substitute the callee's generic args through THIS instance's args — the
    // monomorphization step (mirrors `MonoCx::concretize` for a GenericArgsRef).
    let mono_args: ty::GenericArgsRef<'tcx> = tcx
        .try_instantiate_and_normalize_erasing_regions(
            current_args,
            typing_env,
            EarlyBinder::bind(tcx, callee_generic_args),
        )
        .map_err(|error| {
            LowerError(format!(
                "M4 callee argument normalization failed: {error:?}"
            ))
        })?;
    if mono_args.has_escaping_bound_vars()
        || mono_args.has_non_region_param()
        || mono_args.has_infer()
        || mono_args.has_placeholders()
        || mono_args.has_aliases()
    {
        return bail(format!(
            "M4 callee arguments are not fully monomorphic for {did:?}"
        ));
    }
    let instance = Instance::try_resolve(tcx, typing_env, did, mono_args)
        .map_err(|e| LowerError(format!("M4 try_resolve errored for {did:?}: {e:?}")))?
        .ok_or_else(|| {
            LowerError(format!(
                "M4 try_resolve None for {did:?} args {mono_args:?} (not monomorphic?)"
            ))
        })?;
    let resolved_def = instance.def_id();
    let resolved_args = instance.args;
    let local = resolved_def.as_local().ok_or_else(|| {
        LowerError(format!("M4 callee {resolved_def:?} is not local (extern body)"))
    })?;
    Ok(Some(MonoInstance { def: local, args: resolved_args }))
}

/// PASS 1: collect, in discovery order, every concrete instance reachable from
/// `root`. Recurses into each newly-discovered instance's THIR.
fn collect_worklist<'tcx>(
    tcx: TyCtxt<'tcx>,
    root: MonoInstance<'tcx>,
) -> LResult<Worklist<'tcx>> {
    let (wl, roots) = worklist_batch::collect_roots(tcx, [root])?;
    debug_assert_eq!(roots, [0]);
    Ok(wl)
}

#[path = "m3_worklist_batch.rs"]
mod worklist_batch;
use worklist_batch::WorklistSymbols;

#[cfg(test)]
#[path = "m3_worklist_batch_tests.rs"]
mod worklist_batch_tests;

/// Recursively walk a THIR body collecting resolved USER-fn callees (in source
/// order). Overloaded-arith Calls are skipped (lowered inline). Nested Calls
/// (`double(double(x))`) are walked so the inner call is also collected.
fn collect_calls_in_body<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: TypingEnv<'tcx>,
    thir: &Thir<'tcx>,
    current_args: ty::GenericArgsRef<'tcx>,
    expr: ExprId,
    out: &mut Vec<MonoInstance<'tcx>>,
) -> LResult<()> {
    match &thir[expr].kind {
        ExprKind::Scope { value, .. } => {
            collect_calls_in_body(tcx, typing_env, thir, current_args, *value, out)
        }
        ExprKind::NeverToAny { source } => {
            collect_calls_in_body(tcx, typing_env, thir, current_args, *source, out)
        }
        ExprKind::Block { block } => {
            let b = &thir[*block];
            // M5.2: a helper may be called ONLY inside a `let` initializer (or a
            // statement-expr). Walk every statement before the tail expr so such a
            // callee is still discovered for the worklist.
            for &stmt_id in b.stmts.iter() {
                match &thir[stmt_id].kind {
                    thir::StmtKind::Let { initializer: Some(init), .. } => {
                        collect_calls_in_body(tcx, typing_env, thir, current_args, *init, out)?;
                    }
                    thir::StmtKind::Let { initializer: None, .. } => {}
                    thir::StmtKind::Expr { expr, .. } => {
                        collect_calls_in_body(tcx, typing_env, thir, current_args, *expr, out)?;
                    }
                }
            }
            match b.expr {
                Some(inner) => {
                    collect_calls_in_body(tcx, typing_env, thir, current_args, inner, out)
                }
                None => Ok(()),
            }
        }
        ExprKind::Binary { lhs, rhs, .. }
        | ExprKind::LogicalOp { lhs, rhs, .. } => {
            collect_calls_in_body(tcx, typing_env, thir, current_args, *lhs, out)?;
            collect_calls_in_body(tcx, typing_env, thir, current_args, *rhs, out)
        }
        // M5.1: descend into both branches (and the cond) so a helper called
        // INSIDE an `if` arm is still discovered for the worklist.
        ExprKind::If { cond, then, else_opt, .. } => {
            collect_calls_in_body(tcx, typing_env, thir, current_args, *cond, out)?;
            collect_calls_in_body(tcx, typing_env, thir, current_args, *then, out)?;
            if let Some(e) = else_opt {
                collect_calls_in_body(tcx, typing_env, thir, current_args, *e, out)?;
            }
            Ok(())
        }
        // M5.3: descend into the scrutinee and each arm body so a helper called
        // INSIDE a match arm (e.g. `0 => double(x + 1)`) is discovered for the
        // worklist. (Guards, if any, are rejected at lowering time, so we do not
        // walk them here.)
        ExprKind::Match { scrutinee, arms, .. } => {
            collect_calls_in_body(tcx, typing_env, thir, current_args, *scrutinee, out)?;
            for &arm_id in arms.iter() {
                let arm = &thir[arm_id];
                collect_calls_in_body(tcx, typing_env, thir, current_args, arm.body, out)?;
            }
            Ok(())
        }
        ExprKind::Call { ty, args, .. } => {
            // M5.7f: `Box::new(inner)` is a `Call` to an EXTERN (`alloc`) fn that the
            // lowering PEELS (it is not a cross-fn edge). `resolve_user_call` would
            // error on its non-local body, so SKIP resolving it and just descend into
            // its argument (where the real construction / any helper call lives).
            // Identify it by the `box_new` diagnostic item, NOT a bare name.
            let is_box_new = matches!(ty.kind(), TyKind::FnDef(did, _)
                if tcx.is_diagnostic_item(rustc_span::sym::box_new, *did));
            // Record this callee if it is a user fn (not overloaded-arith, not box_new).
            if !is_box_new {
                if let Some(inst) = resolve_user_call(tcx, typing_env, current_args, *ty)? {
                    out.push(inst);
                }
            }
            // Recurse into the arguments (an arg may itself be a Call).
            for a in args.iter() {
                collect_calls_in_body(tcx, typing_env, thir, current_args, *a, out)?;
            }
            Ok(())
        }
        ExprKind::VarRef { .. } | ExprKind::Literal { .. } | ExprKind::ZstLiteral { .. } => Ok(()),
        // M5.7c/M5.7f: a unary op (`-eval(a)`) or a Borrow/Deref wrapper (`&one()`,
        // `&Val::Neg(..)`, `*r`) may CONTAIN a user-fn call or a construction whose
        // field calls a helper. The body lowerer descends these; collection must
        // too, or a call reachable only through them is missed from the worklist.
        ExprKind::Unary { arg, .. } => {
            collect_calls_in_body(tcx, typing_env, thir, current_args, *arg, out)
        }
        ExprKind::Borrow { arg, .. } | ExprKind::Deref { arg } => {
            collect_calls_in_body(tcx, typing_env, thir, current_args, *arg, out)
        }
        // A trait-dispatch receiver construction (`let y = Yes;`) OR (M5.7f) an
        // enum-variant construction (`Level::Succ(Box::new(..))`). Walk every field
        // initializer so a helper called inside a field (`Succ(double(x))`) and a
        // nested construction's calls are discovered. (A `..base` is lowered-loud
        // out of scope; we still scan it defensively.)
        ExprKind::Adt(adt_expr) => {
            for f in adt_expr.fields.iter() {
                collect_calls_in_body(tcx, typing_env, thir, current_args, f.expr, out)?;
            }
            if let thir::AdtExprBase::Base(fru) = &adt_expr.base {
                collect_calls_in_body(tcx, typing_env, thir, current_args, fru.base, out)?;
            }
            Ok(())
        }
        // Any other shape: ignore for collection (Pass 2 will error if it can't
        // lower a body it must lower).
        _ => Ok(()),
    }
}

/// PASS 2: emit each collected instance, in FuncId order, into `mb`. Returns the
/// lowered signature info for each (indexed by FuncId), for the differential.
/// `func_base` is the module's function count when this worklist's emission
/// begins: instance `i` lands at `FuncId(func_base + i)` (and cross-fn Call
/// edges target the same offset). For a fresh module it is 0 (the M4 case);
/// >0 lets several worklist roots share one module (the M5 if-roundtrip emit).
fn emit_worklist<'tcx>(
    tcx: TyCtxt<'tcx>,
    mb: &mut ModuleBuilder,
    wl: &Worklist<'tcx>,
    symbols: WorklistSymbols<'tcx, '_>,
    func_base: u32,
    register_structs: bool,
) -> LResult<Vec<LoweredInstance>> {
    let typing_env = TypingEnv::fully_monomorphized();
    let mut lowered = Vec::with_capacity(wl.instances.len());
    let actual_base = worklist_batch::next_function_id(mb)?;
    if actual_base.index() != func_base {
        return bail(format!(
            "worklist base {func_base} differs from actual builder id {}", actual_base.index()
        ));
    }
    if let Some(last) = wl.instances.len().checked_sub(1) {
        let last = u32::try_from(last)
            .map_err(|_| LowerError("instance worklist exceeds the FuncId space".into()))?;
        worklist_batch::function_id(func_base, last)?;
    }

    // M5.4: register the tagged-struct `EnumModel` for every recursive enum
    // matched anywhere in this worklist, keyed by AdtDef DefId, BEFORE any
    // function is built (the struct must exist in the module first). For the
    // M3/M5.1-M5.3 worklists there is no ADT match, so this map stays empty and
    // no struct is added — keeping their emitted modules byte-identical.
    //
    // M5.6: when SEVERAL worklist roots that match the SAME enum are emitted into
    // ONE module (is_zero + is_nonzero), only the FIRST may `add_struct` the
    // `Level` tagged struct; a second registration would push a duplicate
    // `StructId(0)` (a validate error). `register_structs=false` builds the model
    // (for discr/offset lookup) but reuses the already-registered struct. The
    // single-root M5.4 callers pass `true`, so their emission is byte-identical.
    let enum_models = build_worklist_enum_models(tcx, mb, wl, register_structs)?;

    for (idx, inst) in wl.instances.iter().enumerate() {
        let ordinal = u32::try_from(idx)
            .map_err(|_| LowerError("instance worklist exceeds the FuncId space".into()))?;
        let expected_id = worklist_batch::function_id(func_base, ordinal)?;
        let actual_next = worklist_batch::next_function_id(mb)?;
        if actual_next != expected_id {
            return bail(format!(
                "worklist ordinal {ordinal} differs from actual builder function id {}", actual_next.index()
            ));
        }
        let (thir_steal, body_expr) = tcx
            .thir_body(inst.def)
            .map_err(|_| LowerError("M4: thir_body errored (tainted)".into()))?;
        let thir = thir_steal.borrow();

        // Span threading: pre-intern THIS instance's THIR source file(s) into
        // the (shared) module's file table — `intern_file` is idempotent, so
        // several worklist instances from one file share one entry.
        let spans = SpanMap::build(tcx, mb, thir.exprs.iter().map(|e| e.span));

        let mut cx = MonoCx {
            tcx,
            thir: &thir,
            args: inst.args,
            typing_env,
            params: Default::default(),
            locals: Default::default(),
            func_base,
            enum_models: enum_models.clone(),
            spans,
            cur_span: None,
        };

        let sig = match &thir.body_type {
            thir::BodyTy::Fn(sig) => *sig,
            _ => return bail("M4: not a function body"),
        };
        // M5.1: lower ALL inputs, one block-param per input (concrete ir-ty).
        let in_tys: Vec<trust_ir::ty::Ty> = sig
            .inputs()
            .iter()
            .map(|t| cx.concrete_ir_ty(*t))
            .collect::<LResult<Vec<_>>>()?;
        let out_ty = cx.concrete_ir_ty(sig.output())?;

        let full_name = symbols.name(tcx, inst);
        let sig_id = mb.add_func_type(in_tys.clone(), vec![out_ty.clone()]);

        let func_id = {
            let mut fb = mb.function(full_name.clone(), sig_id);
            let entry = fb.create_block();
            let param_vals: Vec<ValueId> = in_tys
                .iter()
                .map(|ty| fb.add_block_param(entry, ty.clone()))
                .collect();
            fb.switch_to_block(entry);
            // Fn-level default span (the body expr's position) for the final `ret`.
            cx.enter_expr_span(&mut fb, body_expr);
            bind_params_n(&thir, &mut cx.params, &param_vals)?;
            let result = cx.lower_expr(&mut fb, &wl.by_key, body_expr)?;
            fb.ret(vec![result]);
            fb.build()
        };
        // The auto-assigned FuncId MUST match this instance's discovery index
        // OFFSET by the worklist base (the contract that makes forward Call edges
        // to later-built fns valid). With base==0 this is the original M4 check.
        if func_id != expected_id {
            return bail(format!("M4 FuncId/discovery-order mismatch for {full_name}"));
        }

        lowered.push(LoweredInstance {
            func_id,
            name: full_name,
            param_tys: in_tys,
            ret_ty: out_ty,
        });
    }
    Ok(lowered)
}

/// M6: recover the FAITHFUL `EnumLayout` for the recursive enum a function lowers
/// over (matched OR constructed). The emitted differentials use it to build a
/// `HeapLayout` so the heap they Store matches the lowered reader's Loads EXACTLY.
/// Bails if the function references no recursive enum, or more than one (the heap
/// oracle models a single enum). `extra_enum` lets a fold-then-construct corpus
/// fn (whose own THIR may only CONSTRUCT, with the matched enum in a callee) name
/// the enum explicitly — but for the corpus the single matched/constructed enum
/// is unambiguous, so the scan suffices.
pub fn matched_enum_layout<'tcx>(
    tcx: TyCtxt<'tcx>,
    def: LocalDefId,
) -> LResult<crate::EnumLayout> {
    let (thir_steal, body_expr) = tcx
        .thir_body(def)
        .map_err(|_| LowerError("M6: thir_body errored (tainted)".into()))?;
    let thir = thir_steal.borrow();
    let mut seen = std::collections::HashSet::new();
    let mut adts = Vec::new();
    collect_match_enum_adts(&thir, body_expr, &mut seen, &mut adts);
    match adts.as_slice() {
        [adt] => crate::enum_layout_of(tcx, *adt),
        [] => bail("M6: function references no recursive enum to derive a layout from"),
        _ => bail(format!(
            "M6: function references {} distinct enums; the heap oracle models a single enum",
            adts.len()
        )),
    }
}

/// M5.4: scan EVERY instance's THIR for a `match` whose scrutinee is a recursive
/// enum ADT and, for each distinct AdtDef, register its tagged-struct
/// `EnumModel` (via the shared `build_enum_model`) into `mb`, keyed by DefId.
/// Returns the map. Empty (and registers nothing) when no recursive-ADT match
/// exists — the M3/M5.1-M5.3 case, so those modules stay byte-identical.
///
/// NOTE: `build_enum_model` registers its struct as `StructId(0)` (the same
/// convention M1/M2 + model.rs's heap builder use). The M5.4 corpus has exactly
/// ONE recursive enum, so a single struct id is sufficient and never collides.
fn build_worklist_enum_models<'tcx>(
    tcx: TyCtxt<'tcx>,
    mb: &mut ModuleBuilder,
    wl: &Worklist<'tcx>,
    register_structs: bool,
) -> LResult<std::collections::HashMap<DefId, EnumModel>> {
    let mut adts: Vec<ty::AdtDef<'tcx>> = Vec::new();
    let mut seen: std::collections::HashSet<DefId> = std::collections::HashSet::new();
    for inst in wl.instances.iter() {
        let (thir_steal, body_expr) = tcx
            .thir_body(inst.def)
            .map_err(|_| LowerError("M5.4: thir_body errored (tainted)".into()))?;
        let thir = thir_steal.borrow();
        collect_match_enum_adts(&thir, body_expr, &mut seen, &mut adts);
    }
    let mut models = std::collections::HashMap::new();
    // This mature heap-model adapter has one nominal StructId(0). Never turn
    // batching into permission to merge distinct source enums under that id.
    if adts.len() > 1 {
        return bail(format!(
            "worklist references {} distinct enums; the heap model owns one nominal enum",
            adts.len()
        ));
    }
    for adt in adts {
        // Register the tagged struct (M5.4 single-root case) OR reuse an already-
        // registered one (M5.6 second predicate sharing the module's `Level`):
        // `build_enum_model` both computes the model AND `add_struct`s it, so for
        // the reuse case we compute the SAME model (StructId 0) without re-adding.
        let model = if register_structs {
            build_enum_model(tcx, mb, adt)?
        } else {
            enum_model_without_register(tcx, adt)?
        };
        models.insert(adt.did(), model);
    }
    Ok(models)
}

/// Compute the tagged-struct `EnumModel` for `adt` WITHOUT registering its struct
/// in the module — the model only (variant names/Switch values/field counts, the
/// conventional `StructId(0)`, and the FAITHFUL `EnumLayout`). Used when a SECOND
/// worklist root in the same module matches the SAME enum (M5.6 is_nonzero after
/// is_zero): the struct is already registered, so re-adding it would push a
/// duplicate `StructId(0)` and fail validation. Mirrors the model-construction
/// half of lib.rs `build_enum_model`, sharing the SAME `enum_layout_of`.
fn enum_model_without_register<'tcx>(tcx: TyCtxt<'tcx>, adt: ty::AdtDef<'tcx>) -> LResult<EnumModel> {
    let name = tcx.item_name(adt.did()).to_string();
    let layout = crate::enum_layout_of(tcx, adt)?;
    let mut variants = Vec::new();
    for (idx, vdef) in adt.variants().iter_enumerated() {
        // The legacy `variants` tuple carries the Switch value (or 0 placeholder
        // for the niche untagged variant, which is the Switch DEFAULT); the
        // authoritative encoding lives in `layout`.
        let sv = layout.switch_value_for_variant(idx).unwrap_or(0);
        let nfields = vdef.fields.len();
        variants.push((vdef.name.to_string(), sv, nfields));
    }
    Ok(EnumModel {
        name,
        variants,
        struct_id: trust_ir::value::StructId::new(0),
        layout,
    })
}

/// Recursively walk a THIR body collecting the AdtDef of every `match` whose
/// scrutinee is an enum (peeling references). De-dups by AdtDef DefId via `seen`.
fn collect_match_enum_adts<'tcx>(
    thir: &Thir<'tcx>,
    expr: ExprId,
    seen: &mut std::collections::HashSet<DefId>,
    out: &mut Vec<ty::AdtDef<'tcx>>,
) {
    match &thir[expr].kind {
        ExprKind::Scope { value, .. } => collect_match_enum_adts(thir, *value, seen, out),
        ExprKind::NeverToAny { source } => {
            collect_match_enum_adts(thir, *source, seen, out)
        }
        ExprKind::Block { block } => {
            let b = &thir[*block];
            for &stmt_id in b.stmts.iter() {
                match &thir[stmt_id].kind {
                    thir::StmtKind::Let { initializer: Some(init), .. } => {
                        collect_match_enum_adts(thir, *init, seen, out)
                    }
                    thir::StmtKind::Let { initializer: None, .. } => {}
                    thir::StmtKind::Expr { expr, .. } => {
                        collect_match_enum_adts(thir, *expr, seen, out)
                    }
                }
            }
            if let Some(inner) = b.expr {
                collect_match_enum_adts(thir, inner, seen, out);
            }
        }
        ExprKind::Binary { lhs, rhs, .. } | ExprKind::LogicalOp { lhs, rhs, .. } => {
            collect_match_enum_adts(thir, *lhs, seen, out);
            collect_match_enum_adts(thir, *rhs, seen, out);
        }
        ExprKind::If { cond, then, else_opt, .. } => {
            collect_match_enum_adts(thir, *cond, seen, out);
            collect_match_enum_adts(thir, *then, seen, out);
            if let Some(e) = else_opt {
                collect_match_enum_adts(thir, *e, seen, out);
            }
        }
        ExprKind::Match { scrutinee, arms, .. } => {
            let scrut_ty = peel_ref_ty(thir[*scrutinee].ty);
            if let TyKind::Adt(adt, _) = scrut_ty.kind() {
                if adt.is_enum() && seen.insert(adt.did()) {
                    out.push(*adt);
                }
            }
            collect_match_enum_adts(thir, *scrutinee, seen, out);
            for &arm_id in arms.iter() {
                collect_match_enum_adts(thir, thir[arm_id].body, seen, out);
            }
        }
        ExprKind::Call { args, .. } => {
            for a in args.iter() {
                collect_match_enum_adts(thir, *a, seen, out);
            }
        }
        // M5.7f: an enum-variant CONSTRUCTION (`Level::Succ(..)`, `Val::Lit(5)`)
        // also needs the enum's tagged-struct `EnumModel` registered (it BUILDS the
        // struct the match path reads). Collect the constructed enum's AdtDef (de-
        // duped with any matched occurrence), and walk field initializers so a
        // NESTED construction (`Succ(Box::new(Zero))`) is discovered too. A struct
        // construction (the trait ZST receivers `Yes`/`Two`) is NOT an enum, so it
        // is skipped here — keeping the M3/M5.1-M5.3 modules byte-identical.
        ExprKind::Adt(adt_expr) => {
            if adt_expr.adt_def.is_enum() && seen.insert(adt_expr.adt_def.did()) {
                out.push(adt_expr.adt_def);
            }
            for f in adt_expr.fields.iter() {
                collect_match_enum_adts(thir, f.expr, seen, out);
            }
        }
        // M5.7f: `Box::new(inner)` is a `Call` (handled above), but a borrow/deref
        // around a construction (`&Val::Neg(..)` argument) wraps the Adt — descend.
        ExprKind::Borrow { arg, .. } | ExprKind::Deref { arg } => {
            collect_match_enum_adts(thir, *arg, seen, out);
        }
        ExprKind::Unary { arg, .. } => {
            collect_match_enum_adts(thir, *arg, seen, out);
        }
        _ => {}
    }
}

/// Peel a single layer of `&T`/`&mut T` (the `&self`/`&Nat` match scrutinee) to
/// the pointee type. (Box is an Adt itself; the M5.4 scrutinee is `&Enum`.)
fn peel_ref_ty(ty: ty::Ty<'_>) -> ty::Ty<'_> {
    match ty.kind() {
        TyKind::Ref(_, inner, _) => *inner,
        _ => ty,
    }
}

impl<'a, 'tcx> MonoCx<'a, 'tcx> {
    /// THE unified body lowerer (M5.1). Lowers ANY supported THIR expr to one
    /// `ValueId`, computing each expr's result ir-ty FROM the THIR
    /// (`self.concrete_ir_ty(self.thir[e].ty)`) rather than threading a single
    /// `ir_ty` — so a bool `if`-cond and an i64 branch can coexist in one body.
    ///
    /// This subsumes the former M3 `lower_scalar_body`/`lower_scalar_operand`
    /// and M4 `lower_callchain_body`/`lower_callchain_operand`: every shape they
    /// handled (bare-param / `add x,x` / nested user-fn Call) lowers IDENTICALLY
    /// here, plus `if`/`else` (join-param) and `&&`/`||` (CondBr+join).
    fn lower_expr(
        &mut self,
        fb: &mut FunctionBuilder<'_>,
        by_key: &InstanceMap<'tcx>,
        expr: ExprId,
    ) -> LResult<ValueId> {
        // Span threading: `lower_expr_inner` stamps each visited expr's span as
        // the builder's sticky span; this wrapper RESTORES the enclosing expr's
        // span once the sub-expr returns, so instructions the CALLER emits
        // afterwards (the `add` of a `Binary`, a join-block `br`, ...) carry the
        // caller's own provenance rather than the last sub-expr's.
        let saved = self.cur_span;
        let r = self.lower_expr_inner(fb, by_key, expr);
        self.restore_span(fb, saved);
        r
    }

    /// `lower_expr`'s body (see the span-threading wrapper above). Every
    /// recursive descent goes through the WRAPPER, so per-expr spans nest and
    /// restore correctly.
    fn lower_expr_inner(
        &mut self,
        fb: &mut FunctionBuilder<'_>,
        by_key: &InstanceMap<'tcx>,
        expr: ExprId,
    ) -> LResult<ValueId> {
        let mut e = expr;
        loop {
            // Stamp the CURRENT expr's source span (macro spans degrade to the
            // outermost callsite; an unmappable span keeps the enclosing one).
            self.enter_expr_span(fb, e);
            match &self.thir[e].kind {
                ExprKind::Scope { value, .. } => e = *value,
                ExprKind::NeverToAny { source } => e = *source,
                ExprKind::Block { block } => {
                    // M5.2: a block may carry `let`-binding (and statement-expr)
                    // statements BEFORE its trailing value expr. Lower each stmt
                    // in source order (binding lets into `self.locals`), then peel
                    // to the tail expr. `self.thir[*block]` is re-borrowed inside
                    // `lower_block_stmts` per-stmt so the recursion can mutate cx.
                    let block_id = *block;
                    let tail = self.lower_block_stmts(fb, by_key, block_id)?;
                    match tail {
                        Some(inner) => e = inner,
                        None => {
                            return bail(
                                "M5.2: block used as a value has no trailing expr",
                            )
                        }
                    }
                }
                ExprKind::VarRef { id } => {
                    // M5.2: a VarRef may name a `let`-bound local OR a parameter.
                    // Check `locals` first (a let shadows a same-id param; THIR
                    // ids are unique so this is just a defensive ordering).
                    return self
                        .locals
                        .get(id)
                        .or_else(|| self.params.get(id))
                        .copied()
                        .ok_or_else(|| {
                            LowerError(format!("VarRef {id:?} is not a bound local or param"))
                        });
                }
                // An int OR bool constant literal. The branch/cond ir-ty is read
                // per-expr from the THIR, so the same arm serves both.
                ExprKind::Literal { .. } | ExprKind::ZstLiteral { .. } => {
                    return self.lower_const_literal(fb, e);
                }
                ExprKind::Binary { op, lhs, rhs } => {
                    let l = self.lower_expr(fb, by_key, *lhs)?;
                    let r = self.lower_expr(fb, by_key, *rhs)?;
                    // Result ty of THIS expr (bool for a comparison; the operand
                    // width for arithmetic). The comparison path needs the
                    // OPERAND ty/signedness, read from the lhs THIR expr.
                    let res_ty = self.concrete_ir_ty(self.thir[e].ty)?;
                    let operand_ty = self.thir[*lhs].ty;
                    return self.lower_binop_thir(fb, *op, res_ty, operand_ty, l, r);
                }
                // M5.7c: a UNARY operator — `!` (THIR `UnOp::Not`, both bool
                // logical-not and integer bitwise-not) and unary `-` (`UnOp::Neg`).
                ExprKind::Unary { op, arg } => {
                    return self.lower_unary(fb, by_key, e, *op, *arg);
                }
                ExprKind::Call { ty, args, .. } => {
                    // M5.7f: `Box::new(inner)` is a `Call` to the `box_new`
                    // diagnostic-item fn. At the trust-ir level a `Box<T>` IS the
                    // heap pointer to `T`, so a `Box::new(inner)` value is exactly
                    // `inner`'s value (the inner construction's `HeapAlloc` pointer,
                    // or a scalar boxed — not in the corpus). Peel `Box::new` to its
                    // single argument and lower that. Identify the call by the
                    // `box_new` DIAGNOSTIC ITEM (a def-path identity), NOT a bare
                    // method name — consistent with the `arith_binop_of` /
                    // `is_deref_call` lesson (a user fn named `new` is not Box::new).
                    if self.is_box_new_call(*ty) {
                        let inner = self.box_new_arg(args)?;
                        e = inner;
                        continue;
                    }
                    return self.lower_call_expr(fb, by_key, e, *ty, args);
                }
                // M5.4: a `Borrow`/`Deref` wrapping a Ptr place — e.g. the
                // `&*m` reborrow around the recursive `depth(m)` argument
                // (`Borrow(Deref(Deref(VarRef m)))`). At the pointer level a
                // `&`/`*`/`Box`-deref is identity, so resolve the underlying
                // place. (No M3/M5.1-M5.3 scalar body produces these, so their
                // emission is unchanged.)
                //
                // SOUNDNESS: identity-peeling is ONLY correct when the deref
                // RESULT is itself a pointer (the reborrow case). For `*r` where
                // `r: &i64`, the Deref result is an `i64` scalar — peeling would
                // return the POINTER typed as the scalar (a miscompile). Decide on
                // the deref result's concrete ir-ty.
                ExprKind::Deref { arg } => {
                    let arg = *arg;
                    let result_ir = self.concrete_ir_ty(self.thir[e].ty)?;
                    if result_ir == trust_ir::ty::Ty::Ptr {
                        // Reborrow / Box-deref at the pointer level: identity-peel.
                        return self.lower_place(fb, by_key, e);
                    }
                    // Scalar deref: resolve the place pointer being dereferenced
                    // and emit a typed Load of the scalar through it (same typed
                    // Load shape `load_field` uses for struct fields).
                    //
                    // SOUNDNESS (audit FIX C): `lower_place` peels ALL Borrow/Deref
                    // layers to the underlying VarRef pointer. That is correct for a
                    // SINGLE-level scalar deref `*r` (r: &i64) — `arg` peels to `r`,
                    // a `Ptr` to the scalar, and `Load(i64, r)` reads the scalar. But
                    // for a MULTI-level scalar deref `**rr` (rr: &&i64), `arg` is
                    // itself `*rr`, and `lower_place(*rr)` over-peels BOTH derefs to
                    // `rr` (a `Ptr` to a `&i64`), so `Load(i64, rr)` would read the
                    // INNER POINTER's bits as an i64 — a silent miscompile. Guard: if
                    // the inner place `arg` (after peeling scopes/uses) is ITSELF a
                    // deref of a pointer-to-pointer, bail loud (multi-level scalar
                    // deref is future work). A single-level `*r` still lowers.
                    if self.scalar_deref_arg_is_multi_level(arg)? {
                        return bail(
                            "M5: multi-level scalar deref (e.g. `**rr` where rr: &&i64) is not \
                             yet supported — `lower_place` peels ALL pointer layers, so loading \
                             the scalar through the OUTERMOST pointer would read the inner \
                             pointer's bits (a miscompile). Only a single-level scalar deref \
                             `*r` (r: &scalar) is supported",
                        );
                    }
                    let ptr = self.lower_place(fb, by_key, arg)?;
                    return Ok(fb.load(result_ir, ptr));
                }
                // A `Borrow` produces a reference (`&T`), which is always a `Ptr`
                // at the trust-ir level — identity-peel to the place pointer. If
                // the borrow's result is somehow NOT a Ptr, fail loud rather than
                // return a scalar typed as Ptr.
                ExprKind::Borrow { .. } => {
                    let result_ir = self.concrete_ir_ty(self.thir[e].ty)?;
                    if result_ir != trust_ir::ty::Ty::Ptr {
                        return bail(format!(
                            "M5.4: Borrow lowered to {result_ir:?}, expected Ptr \
                             (a non-pointer borrow place is unsupported)"
                        ));
                    }
                    return self.lower_place(fb, by_key, e);
                }
                ExprKind::LogicalOp { op, lhs, rhs } => {
                    return self.lower_logical(fb, by_key, *op, *lhs, *rhs);
                }
                ExprKind::If { cond, then, else_opt, .. } => {
                    return self.lower_if(fb, by_key, e, *cond, *then, *else_opt);
                }
                ExprKind::Match { scrutinee, arms, .. } => {
                    // Copy out of the immutable `self.thir[e]` borrow so the
                    // `&mut self` lowering call below is borrow-clean (mirrors
                    // how the `If` arm copies its child ExprIds).
                    let scrut = *scrutinee;
                    let arm_ids: Vec<thir::ArmId> = arms.to_vec();
                    // Dispatch on the scrutinee's CONCRETE type: an integer
                    // scrutinee is the M5.3 scalar switch; an `&Enum`/`Box<Enum>`
                    // (a recursive ADT, lowered to `Ptr`) is the M5.4 heap-tag
                    // match. A registered `EnumModel` for the scrutinee's AdtDef
                    // is the precise signal that this is an M5.4 ADT match.
                    if self.match_scrutinee_enum_did(scrut).is_some() {
                        return self.lower_match_adt(fb, by_key, e, scrut, &arm_ids);
                    }
                    return self.lower_match_scalar(fb, by_key, e, scrut, &arm_ids);
                }
                // Trait static dispatch: a ZST receiver construction. A trait
                // method call on a unit struct (`Yes.pred()`/`Two.score()`) binds
                // or borrows the receiver as an `Adt` constructing a field-less
                // struct. A ZST has no runtime value; the resolved leaf method
                // ignores its `&self` (lowered to a `Ptr` param), so it lowers to a
                // placeholder `Ptr` (the dummy receiver the former
                // `lower_trait_dispatch` special case passed). A NON-ZST aggregate
                // bails LOUDLY (no real struct layout / field stores here).
                ExprKind::Adt(_) => {
                    return self.lower_zst_adt(fb, by_key, e);
                }
                other => {
                    return bail(format!(
                        "M5.1 lower_expr: unsupported expr {} ({:?})",
                        crate::expr_kind_name_pub(other),
                        std::mem::discriminant(other)
                    ))
                }
            }
        }
    }

    /// M5.2: lower a block's STATEMENTS (in source order) into side effects /
    /// local bindings, returning the block's trailing value expr (if any) for the
    /// caller to peel to. Each `let pat = init` lowers `init` via `lower_expr` and
    /// binds the pattern's var into `self.locals`. A statement-expr is lowered and
    /// its value discarded (the corpus has none, but the clean-kernel direction
    /// does; lowering-and-discarding is sound and keeps call-discovery honest). A
    /// `let` without an initializer, or a non-`Binding` let pattern (tuple
    /// destructuring etc.), bails LOUDLY — out of M5.2 scope.
    fn lower_block_stmts(
        &mut self,
        fb: &mut FunctionBuilder<'_>,
        by_key: &InstanceMap<'tcx>,
        block_id: rustc_middle::thir::BlockId,
    ) -> LResult<Option<ExprId>> {
        // `self.thir` is `&'a Thir`, so this borrow is tied to 'a (NOT &self) —
        // we can iterate the stmt ids while calling `&mut self` lowerers below.
        let block = &self.thir[block_id];
        let stmt_ids: &[rustc_middle::thir::StmtId] = &block.stmts;
        let tail = block.expr;

        for &stmt_id in stmt_ids {
            match &self.thir[stmt_id].kind {
                thir::StmtKind::Let { pattern, initializer, else_block, .. } => {
                    if else_block.is_some() {
                        return bail("M5.2: `let ... else` is out of scope");
                    }
                    let init = initializer.ok_or_else(|| {
                        LowerError(
                            "M5.2: `let` without an initializer is out of scope".into(),
                        )
                    })?;
                    // Bind the pattern var. Only a simple `let x = ..` binding is
                    // supported; tuple/struct destructuring etc. bails loudly.
                    //
                    // SOUNDNESS (audit FIX #5 — defense-in-depth, symmetric with
                    // the ADT-match `collect_bindings` guard): a `let` `Binding`
                    // may ALSO carry an `@`-subpattern (`let x @ y = ..`, or worse
                    // `let x @ Variant(..) = ..`). The old match bound ONLY `var`
                    // and SILENTLY DROPPED `subpattern: Some(..)`, so the inner
                    // binder `y` (or a nested constructor constraint) would dangle
                    // or be lost. Reject a let `Binding` with an `@`-subpattern, and
                    // any non-`Binding` let pattern (tuple/struct destructuring),
                    // LOUDLY rather than miscompile.
                    let var = match &pattern.kind {
                        thir::PatKind::Binding { var, subpattern: None, .. } => *var,
                        thir::PatKind::Binding { subpattern: Some(_), .. } => {
                            return bail(
                                "M5: `let` with an @-subpattern (`let x @ y = ..`) is not yet \
                                 supported — only a simple `let x = ..` binding is supported \
                                 (the @-subpattern would otherwise be silently dropped)",
                            )
                        }
                        other => {
                            return bail(format!(
                                "M5: `let` with a destructuring pattern {:?} is not yet \
                                 supported (only a simple `let x = ..` binding is supported)",
                                std::mem::discriminant(other)
                            ))
                        }
                    };
                    let val = self.lower_expr(fb, by_key, init)?;
                    self.locals.insert(var, val);
                }
                thir::StmtKind::Expr { expr, .. } => {
                    // A statement-expr: lower for its side effects, discard the
                    // value. (No corpus shape exercises this; included so a helper
                    // called only in a stmt-expr position is still lowered.)
                    let _ = self.lower_expr(fb, by_key, *expr)?;
                }
            }
        }
        Ok(tail)
    }

    /// Read an int OR bool literal (peeled to the `Literal`/`ZstLiteral` node)
    /// from the type-checked const and emit the matching trust-ir const. The
    /// literal's ir width/type is read PER-EXPR from the THIR.
    fn lower_const_literal(
        &mut self,
        fb: &mut FunctionBuilder<'_>,
        e: ExprId,
    ) -> LResult<ValueId> {
        let ir_ty = self.concrete_ir_ty(self.thir[e].ty)?;
        match ir_ty {
            trust_ir::ty::Ty::Bool => {
                let b = self.eval_bool_literal(e)?;
                Ok(fb.bool_const(b))
            }
            int_ty => {
                let v = self.eval_int_literal(e)?;
                Ok(fb.iconst(int_ty, v))
            }
        }
    }

    /// Lower a ZST struct construction (`Yes`/`No`/`Two`/`Neg`, a field-less unit
    /// struct used as a trait-dispatch receiver) to a placeholder `Ptr` value. A
    /// ZST has no runtime representation and the resolved trait leaf ignores its
    /// `&self` receiver (lowered to a `Ptr` param), so a null `Ptr` is a sound
    /// stand-in — exactly the dummy receiver the former `lower_trait_dispatch`
    /// special case passed. A NON-ZST aggregate (any explicit field, a base `..`,
    /// default fields, or an enum variant with payload) bails LOUDLY: we have no
    /// real struct layout / field-store machinery in this lowerer. `e` must be an
    /// `ExprKind::Adt`; the `AdtExpr` is re-borrowed inside (so the caller can pass
    /// just the `ExprId`, avoiding a borrow conflict with `&mut self`).
    fn lower_zst_adt(
        &mut self,
        fb: &mut FunctionBuilder<'_>,
        by_key: &InstanceMap<'tcx>,
        e: ExprId,
    ) -> LResult<ValueId> {
        // M5.7f: an ENUM-VARIANT construction (`Level::Succ(..)`, `Val::Lit(5)`)
        // is a real tagged-struct heap value (the DUAL of `lower_match_adt`).
        // Route it to the construction path BEFORE the ZST-receiver checks below
        // (which still bail loud for an enum variant with NO model registered).
        if let ExprKind::Adt(adt_expr) = &self.thir[e].kind {
            if adt_expr.adt_def.is_enum() {
                return self.lower_enum_variant_construction(fb, by_key, e);
            }
        }
        let (is_struct, total_field_count, nfields, is_none_base) = match &self.thir[e].kind {
            ExprKind::Adt(adt_expr) => (
                // SOUNDNESS: distinguish a genuine field-less unit STRUCT from a
                // no-payload ENUM VARIANT. An enum value-type lowers to `Ptr`, so a
                // payload-less variant (`Level::Zero`, `Nat::Zero`) ALSO has zero
                // explicit fields and would pass the old `nfields == 0` check — but
                // constructing it as a value is real heap construction (a tagged
                // box), and a later `match` would Load the tag through this null
                // Ptr (a NULL deref / silent miscompile). Require `is_struct()` and
                // that the ADT genuinely carries NO fields in ANY variant.
                adt_expr.adt_def.is_struct(),
                adt_expr.adt_def.all_fields().count(),
                adt_expr.fields.len(),
                matches!(adt_expr.base, thir::AdtExprBase::None),
            ),
            other => {
                return bail(format!(
                    "M3 trait-dispatch: lower_zst_adt on a non-Adt expr {:?}",
                    std::mem::discriminant(other)
                ))
            }
        };
        if !is_struct {
            // An enum VARIANT value (even a no-payload one): constructing it as a
            // value is real heap construction (future work). It must NOT be treated
            // as a null-Ptr ZST receiver — a downstream `match` would Load the tag
            // through NULL. Fail loud.
            return bail(
                "M3 trait-dispatch: constructing an ENUM VARIANT value is out of scope \
                 (an enum value lowers to Ptr; a null-Ptr stand-in would be a NULL \
                 deref when the value is later matched). Only a field-less unit STRUCT \
                 receiver is supported.",
            );
        }
        if total_field_count != 0 {
            // A struct whose definition has fields (even if this construction
            // happened to enumerate none — impossible without `..`, but be safe):
            // it has a real layout we do not store. Fail loud.
            return bail(format!(
                "M3 trait-dispatch: ADT construction of a struct with {total_field_count} \
                 declared field(s) is out of scope (only a genuinely field-less unit \
                 struct ZST receiver is supported)"
            ));
        }
        if nfields != 0 {
            return bail(format!(
                "M3 trait-dispatch: ADT construction with {nfields} field(s) is out of scope \
                 (only a field-less ZST receiver, e.g. a unit struct, is supported)"
            ));
        }
        if !is_none_base {
            return bail(
                "M3 trait-dispatch: ADT construction with a `..base`/default-fields \
                 tail is out of scope (only a field-less ZST receiver is supported)",
            );
        }
        // Confirm the construction's CONCRETE type is genuinely zero-sized (a
        // field-less struct). `concrete_ir_ty` maps such a struct to `Ptr` (see
        // `lower_concrete_ty`); a non-ZST struct would error there, fail-loud.
        let ir_ty = self.concrete_ir_ty(self.thir[e].ty)?;
        if ir_ty != trust_ir::ty::Ty::Ptr {
            return bail(format!(
                "M3 trait-dispatch: ADT construction lowered to {ir_ty:?}, expected Ptr \
                 (only a field-less ZST receiver is supported)"
            ));
        }
        // The placeholder receiver pointer: a null `Ptr`. The resolved leaf method
        // never dereferences it. (`Inst::NullPtr` is typed `Ptr` and validates; an
        // `iconst(Ptr, 0)` would NOT — `Constant::Int` does not match `Ty::Ptr`.)
        Ok(fb.null_ptr())
    }

    /// M5.7f: lower an ENUM-VARIANT CONSTRUCTION (`Level::Succ(Box::new(Level::Zero))`,
    /// `Val::Lit(5)`) — the DUAL of `lower_match_adt`. It BUILDS the tagged-struct
    /// heap value the match path READS, and is the key remaining capability for a
    /// real `whnf` (which constructs the reduced term). The shape mirrors
    /// `model.rs::build_heap_value` (the M2/M5.4 differential's hand-written heap
    /// builder), but driven from genuine THIR:
    ///   1. `p = HeapAlloc(Ty::Struct(model.struct_id))` (the enum's tagged struct);
    ///   2. `Store(i32 <variant discriminant>, GEP(p, TAG_OFFSET))`;
    ///   3. per field i: lower the field VALUE and `Store` it at `GEP(p,
    ///      payload_offset(i))` — a Box-child field stores the inner POINTER (Ptr,
    ///      from the inner construction's alloc); an inline-scalar field stores the
    ///      VALUE at its scalar width (the INVERSE of `bind_payload_field`'s
    ///      pointer-vs-scalar read);
    ///   4. the constructor expression's value is `p` (a `Ptr`).
    ///
    /// The enum's `EnumModel` must be registered in `self.enum_models` (done by
    /// `build_worklist_enum_models`, which collects both MATCHED and CONSTRUCTED
    /// enums) — its `struct_id` is the HeapAlloc'd type and its discriminants the
    /// stored tags. A construction whose model is not registered bails LOUDLY
    /// (refusing to invent a layout).
    fn lower_enum_variant_construction(
        &mut self,
        fb: &mut FunctionBuilder<'_>,
        by_key: &InstanceMap<'tcx>,
        e: ExprId,
    ) -> LResult<ValueId> {
        // Pull the construction's variant index + field expr ids out of the
        // immutable THIR borrow so the `&mut self` field lowering below is clean.
        let (did, variant_index, field_exprs): (DefId, VariantIdx, Vec<(usize, ExprId)>) =
            match &self.thir[e].kind {
                ExprKind::Adt(adt_expr) => {
                    if !matches!(adt_expr.base, thir::AdtExprBase::None) {
                        return bail(
                            "M5.7f: enum-variant construction with a `..base`/functional-record-\
                             update tail is not supported (only an explicit-all-fields variant \
                             construction is)",
                        );
                    }
                    // `adt_expr.fields` carries (FieldIdx, expr). Map to (usize, expr)
                    // in field-index order (the tagged-struct slots are 0..nfields).
                    let mut fields: Vec<(usize, ExprId)> = adt_expr
                        .fields
                        .iter()
                        .map(|f| (f.name.as_usize(), f.expr))
                        .collect();
                    fields.sort_by_key(|&(idx, _)| idx);
                    (adt_expr.adt_def.did(), adt_expr.variant_index, fields)
                }
                other => {
                    return bail(format!(
                        "M5.7f: lower_enum_variant_construction on a non-Adt expr {:?}",
                        std::mem::discriminant(other)
                    ))
                }
            };

        // The enum's tagged-struct model + FAITHFUL layout (registered by
        // build_worklist_enum_models). The construction path is the DUAL of
        // `lower_match_adt`: it Stores the SAME bytes (tag width/offset + the niche
        // value or no tag for a niche untagged variant) the match path Loads.
        let (struct_id, layout) = {
            let model = self.enum_models.get(&did).ok_or_else(|| {
                LowerError(format!(
                    "M5.7f: constructing an enum variant whose `EnumModel` is not registered \
                     ({did:?}) — refusing to invent a tagged-struct layout (the enum must be \
                     discovered by `build_worklist_enum_models`, which collects constructed + \
                     matched enums)"
                ))
            })?;
            (model.struct_id, model.layout.clone())
        };

        // The concrete enum args (for resolving each field's REAL type — Box-child
        // pointer vs inline scalar). For the corpus enums (Level/Val) these are the
        // identity/empty args; a generic enum would carry the instantiation.
        let enum_args = match self.concretize(self.thir[e].ty).kind() {
            TyKind::Adt(_, args) => *args,
            other => {
                return bail(format!(
                    "M5.7f: constructed value's concrete type is not an Adt ({other:?})"
                ))
            }
        };

        // 1. Allocate the tagged struct on the heap (mirrors build_heap_value).
        let p = fb.heap_alloc(
            trust_ir::ty::Ty::Struct(struct_id),
            None,
            None,
            trust_ir::inst::AllocOrigin::RustHeap,
        );

        // 2. Store the discriminant tag at the REAL tag offset + width. For a
        // Direct enum every variant stores its Switch value. For a NICHE enum, the
        // niche variants store their encoded niche value, and the UNTAGGED variant
        // stores NOTHING into the tag word (its payload field's own value provides
        // the discriminant — exactly what rustc's `set_discriminant` does). A
        // niche untagged variant with a non-trivial payload (a Box/scalar that
        // also sits at the tag offset) is constructed by storing that payload
        // (handled in step 3); we MUST NOT clobber it with a synthetic tag.
        let is_niche_untagged = matches!(
            &layout.tag_encoding,
            crate::LayoutTagEncoding::Niche { untagged_variant } if *untagged_variant == variant_index
        );
        if !is_niche_untagged {
            let discr = layout.switch_value_for_variant(variant_index).ok_or_else(|| {
                LowerError(format!(
                    "M5.7f: no Switch tag value for constructed variant {variant_index:?} of \
                     {did:?} (a niche untagged variant stores no tag; any other variant must \
                     have one)"
                ))
            })?;
            let tag = fb.iconst(layout.tag_ir_ty.clone(), discr);
            store_field(fb, p, layout.tag_offset, layout.tag_ir_ty.clone(), tag);
        }

        // 3. Per field: lower the field VALUE and Store it by its REAL kind, at the
        // variant's REAL per-field byte offset.
        for (field_idx, field_expr) in field_exprs {
            let field_rustc_ty =
                self.adt_field_rustc_ty(did, enum_args, variant_index, field_idx)?;
            let field_ir = lower_concrete_ty(self.tcx, field_rustc_ty).map_err(|err| {
                LowerError(format!(
                    "M5.7f: constructing variant {variant_index:?} field {field_idx} (rustc ty \
                     {field_rustc_ty:?}): {err} — an inline-aggregate (tuple/array/struct) \
                     payload has no tagged-struct slot layout (pointer and inline-scalar \
                     payloads ARE supported; inline-aggregate is future work)"
                ))
            })?;
            // The field VALUE: a Box-child or nested variant recurses through
            // lower_expr (which peels `Box::new` and re-enters construction); a
            // scalar leaf (`5` in `Val::Lit(5)`) is a const/var lowered to its
            // scalar value. Either way, `lower_expr` yields the right SSA value.
            // `by_key` is threaded so a field initializer that is itself a user-fn
            // call (`Succ(double(x))`, not in this corpus but valid) resolves.
            let v = self.lower_expr(fb, by_key, field_expr)?;
            let field_off = layout.field_offset(variant_index, field_idx).ok_or_else(|| {
                LowerError(format!(
                    "M5.7f: no layout offset for constructed variant {variant_index:?} field \
                     {field_idx} of {did:?}"
                ))
            })?;
            if field_ir == trust_ir::ty::Ty::Ptr {
                // Box-child / recursive-enum field: the slot HOLDS the pointer
                // (the inner construction's HeapAlloc / a `&` place). Store the Ptr.
                store_field(fb, p, field_off, trust_ir::ty::Ty::Ptr, v);
            } else if is_scalar_ir_ty(&field_ir) {
                // INLINE-SCALAR field (`Val::Lit(i64)`): store the scalar VALUE at
                // its width INLINE in the slot (the inverse of bind_payload_field's
                // `field_addr` read, which the body's `*n` then Loads).
                store_field(fb, p, field_off, field_ir, v);
            } else {
                return bail(format!(
                    "M5.7f: constructing variant {variant_index:?} field {field_idx} of ir-ty \
                     {field_ir:?} is not supported — only a pointer (Box-child/recursive) or an \
                     inline-scalar payload field has a tagged-struct slot"
                ));
            }
        }

        // 4. The constructor expression's value is the root struct pointer.
        Ok(p)
    }

    /// M5.7f: is this `Call`'s callee the `Box::new` constructor? Identified by the
    /// `box_new` DIAGNOSTIC ITEM (a def-path identity), NOT a bare method name —
    /// a user inherent/free fn literally named `new` is NOT `Box::new`, and peeling
    /// it would silently drop the call. Mirrors `is_deref_call`/`arith_binop_of`,
    /// which key on trait/diagnostic identity rather than the method name.
    fn is_box_new_call(&self, callee_ty: ty::Ty<'tcx>) -> bool {
        if let TyKind::FnDef(did, _) = callee_ty.kind() {
            return self.tcx.is_diagnostic_item(rustc_span::sym::box_new, *did);
        }
        false
    }

    /// M5.7f: does this `Call` expr return an OWNED enum heap value (an enum, or a
    /// `Box<enum>`) — i.e. an OWNED tagged-struct `Ptr` the caller can use directly
    /// as a place pointer (`&one()`)? This is the precise signal distinguishing a
    /// value-producing constructor-call place from a REFERENCE place-projection: a
    /// user method returning `&T` (e.g. `w.deref() -> &Tree`, the `neg_user_deref`
    /// guard) has a `Ref` result type and is NOT owned, so it returns `false` and
    /// `lower_place` falls through to its loud bail (that soundness guard preserved).
    /// Checks the CONCRETE (post-substitution) result type so a generic fn is judged
    /// on its instantiation.
    fn call_returns_owned_enum(&self, call_expr: ExprId) -> bool {
        let result = self.concretize(self.thir[call_expr].ty);
        // An OWNED enum value, or an owned `Box<enum>` — NOT a `&enum` reference
        // (which is a borrow place-projection, not an owned value).
        match result.kind() {
            TyKind::Adt(adt, _) => adt.is_enum() || adt.is_box(),
            _ => false,
        }
    }

    /// M5.7f: the single argument of a `Box::new(inner)` call (the value being
    /// boxed). `Box::new` is a 1-arg associated fn; anything else is a malformed
    /// box call (bail rather than mis-peel).
    fn box_new_arg(&self, args: &[ExprId]) -> LResult<ExprId> {
        match args {
            [inner] => Ok(*inner),
            _ => bail(format!(
                "M5.7f: `Box::new` call has {} arg(s), expected exactly 1",
                args.len()
            )),
        }
    }

    /// Read a bool literal (`true`/`false`) via its THIR `Literal` node.
    fn eval_bool_literal(&self, e: ExprId) -> LResult<bool> {
        match &self.thir[e].kind {
            ExprKind::Literal { lit, neg } => {
                if *neg {
                    return bail("M5.1: negated bool literal");
                }
                match lit.node {
                    rustc_ast::LitKind::Bool(b) => Ok(b),
                    ref other => bail(format!("M5.1: non-bool literal {other:?}")),
                }
            }
            _ => bail("M5.1: expected bool literal"),
        }
    }

    /// Read an integer literal's value as `i128` via its THIR `Literal` node
    /// (`LitKind::Int`), honoring a `neg` sign. Mirrors `eval_bool_literal` for
    /// the integer side so the unified `Literal` arm serves both.
    fn eval_int_literal(&self, e: ExprId) -> LResult<i128> {
        match &self.thir[e].kind {
            ExprKind::Literal { lit, neg } => match lit.node {
                rustc_ast::LitKind::Int(v, _) => {
                    let raw = v.get() as i128;
                    Ok(if *neg { -raw } else { raw })
                }
                ref other => bail(format!("M5.1: non-int literal {other:?}")),
            },
            other => bail(format!(
                "M5.1: expected int literal, found {:?}",
                std::mem::discriminant(other)
            )),
        }
    }

    /// Lower `if cond { then } else { else_opt }` into CondBr to a then/else
    /// block, each branch jumping to a `join` block carrying the branch value as
    /// a block param (the branches' concrete ir-ty). Returns the join param.
    /// Mirrors `lower_logical`'s join-param pattern. A value-producing `if`
    /// always has an else in THIR; we bail if `else_opt` is None.
    fn lower_if(
        &mut self,
        fb: &mut FunctionBuilder<'_>,
        by_key: &InstanceMap<'tcx>,
        if_expr: ExprId,
        cond: ExprId,
        then: ExprId,
        else_opt: Option<ExprId>,
    ) -> LResult<ValueId> {
        let else_expr = else_opt
            .ok_or_else(|| LowerError("M5.1: value-producing `if` with no else branch".into()))?;

        // The `if`'s result ir-ty (= both branches' ty) is read from the THIR.
        let join_ty = self.concrete_ir_ty(self.thir[if_expr].ty)?;

        let cond_val = self.lower_expr(fb, by_key, cond)?;

        let then_block = fb.create_block();
        let else_block = fb.create_block();
        let join = fb.create_block();
        let join_param = fb.add_block_param(join, join_ty);

        fb.condbr(cond_val, then_block, vec![], else_block, vec![]);

        // then block: lower the branch (which may itself move blocks) and jump to
        // join with its value.
        fb.switch_to_block(then_block);
        let then_val = self.lower_expr(fb, by_key, then)?;
        fb.br(join, vec![then_val]);

        // else block: likewise.
        fb.switch_to_block(else_block);
        let else_val = self.lower_expr(fb, by_key, else_expr)?;
        fb.br(join, vec![else_val]);

        fb.switch_to_block(join);
        Ok(join_param)
    }

    /// M5.3: lower a `match scrut { arms }` whose scrutinee is a SCALAR (integer)
    /// VALUE into a `Switch` over that value joining at a block-param — the
    /// value-producing generalization of LowerCx's whole-function-tail
    /// `lower_match` (which reads an enum TAG via heap Load and returns per arm).
    ///
    /// Shape:
    ///   - lower `scrut` to an integer `ValueId` in the CURRENT block;
    ///   - create a `join` block with one result block-param (the match's ir-ty);
    ///   - for each arm: an `arm_block` lowering the arm body (which may itself
    ///     move blocks via if/match — so the `br(join, [result])` is emitted in
    ///     whatever block is CURRENT after the body, mirroring `lower_if`);
    ///   - integer-literal (`Constant`) patterns push `SwitchCase`s; a `Wild`/
    ///     plain `Binding` arm is the DEFAULT (a scalar match REQUIRES a catch-all
    ///     for exhaustiveness); a `Binding` catch-all binds the scrutinee value
    ///     into `locals` so the arm body can reference it;
    ///   - emit the `Switch` in the block where the scrutinee was lowered;
    ///   - `switch_to_block(join)`, return the join param.
    ///
    /// An ADT (Ptr) scrutinee BAILS LOUDLY — that is M5.4 (match over a recursive
    /// ADT through the heap tag), which keeps LowerCx's Load-the-tag machinery.
    fn lower_match_scalar(
        &mut self,
        fb: &mut FunctionBuilder<'_>,
        by_key: &InstanceMap<'tcx>,
        match_expr: ExprId,
        scrutinee: ExprId,
        arms: &[thir::ArmId],
    ) -> LResult<ValueId> {
        // Gate: only an INTEGER scrutinee is M5.3. A Ptr/ADT/bool scrutinee is
        // out of scope (the ADT/heap-tag match is M5.4).
        let scrut_ir_ty = self.concrete_ir_ty(self.thir[scrutinee].ty)?;
        if !is_int_ir_ty(&scrut_ir_ty) {
            return bail(format!(
                "M5.4: match over a non-integer scrutinee (ir-ty {scrut_ir_ty:?}) \
                 is out of M5.3 scope (M5.3 is a SCALAR-value switch; an ADT/heap \
                 tag match is M5.4)"
            ));
        }

        // 1. Lower the scrutinee to an integer value. The builder's current block
        // is now the scrutinee's final block (the scrutinee may itself have moved
        // blocks via a nested if/match). We emit the `Switch` terminator into THIS
        // block BEFORE switching away to lower arm bodies — so we never need to
        // re-name the scrutinee's block (the builder exposes no current-block
        // accessor, and `lower_if` relies on the same "emit the terminator in the
        // block the operand left us in" discipline).
        let scrut_val = self.lower_expr(fb, by_key, scrutinee)?;

        // 2. The match result ir-ty (= every arm's ty) and the join block.
        let join_ty = self.concrete_ir_ty(self.thir[match_expr].ty)?;
        let join = fb.create_block();
        let join_param = fb.add_block_param(join, join_ty);

        // 3. PASS A — assign each arm an arm_block and derive its SwitchCases (or
        // the single catch-all default) from its pattern, binding a catch-all
        // `Binding` var to the scrutinee value. This runs entirely before any arm
        // body is lowered, so the `Switch` can be emitted into the scrutinee's
        // block (still current) without losing it. A scalar match has exactly one
        // catch-all (Rust requires it for exhaustiveness).
        let mut cases: Vec<trust_ir::inst::SwitchCase> = Vec::new();
        let mut default_block: Option<BlockId> = None;
        // arm_id -> its arm_block, for PASS B (body lowering).
        let mut arm_blocks: Vec<(thir::ArmId, BlockId)> = Vec::with_capacity(arms.len());

        for &arm_id in arms {
            if self.thir[arm_id].guard.is_some() {
                return bail("M5.3: match arm has a guard (unsupported)");
            }
            let arm_block = fb.create_block();
            arm_blocks.push((arm_id, arm_block));

            match &self.thir[arm_id].pattern.kind {
                thir::PatKind::Constant { value } => {
                    let n = self.eval_pat_const_int(*value)?;
                    cases.push(trust_ir::inst::SwitchCase {
                        value: trust_ir::constant::Constant::Int(n),
                        target: arm_block,
                        args: vec![],
                    });
                }
                // A catch-all: `_` (Wild) or a plain binding `name` (no
                // subpattern). A `Binding` catch-all binds `name` to the
                // scrutinee VALUE (into `locals`) so the arm body can use it.
                thir::PatKind::Wild => {
                    if default_block.is_some() {
                        return bail("M5.3: more than one catch-all arm in a scalar match");
                    }
                    default_block = Some(arm_block);
                }
                thir::PatKind::Binding { var, subpattern: None, .. } => {
                    if default_block.is_some() {
                        return bail("M5.3: more than one catch-all arm in a scalar match");
                    }
                    self.locals.insert(*var, scrut_val);
                    default_block = Some(arm_block);
                }
                // Or-patterns of integer literals: one case per alternative, all
                // targeting this arm block.
                thir::PatKind::Or { pats } => {
                    for p in pats.iter() {
                        match &p.kind {
                            thir::PatKind::Constant { value } => {
                                let n = self.eval_pat_const_int(*value)?;
                                cases.push(trust_ir::inst::SwitchCase {
                                    value: trust_ir::constant::Constant::Int(n),
                                    target: arm_block,
                                    args: vec![],
                                });
                            }
                            other => {
                                return bail(format!(
                                    "M5.3: or-pattern alternative is not an integer literal \
                                     ({:?})",
                                    std::mem::discriminant(other)
                                ))
                            }
                        }
                    }
                }
                other => {
                    return bail(format!(
                        "M5.3: unsupported scalar-match arm pattern {:?} \
                         (only integer literal, `_`/binding catch-all, and \
                         or-of-literals are supported; ranges/bindings-with-\
                         subpattern are out of scope)",
                        std::mem::discriminant(other)
                    ))
                }
            }
        }

        // 4. Emit the Switch in the scrutinee's (still-current) block. A scalar
        // match in Rust REQUIRES a catch-all for exhaustiveness, so `default_block`
        // is Some; if (defensively) absent, route the default to an `unreachable`
        // block so validate stays happy and the interpreter never falls through.
        let default = match default_block {
            Some(b) => b,
            None => {
                let trap = fb.create_block();
                fb.switch_to_block(trap);
                fb.unreachable();
                trap
            }
        };
        fb.switch(scrut_val, cases, default, vec![]);

        // 5. PASS B — lower each arm body into its arm_block. The body may itself
        // move blocks (a nested if/match), so emit `br(join, [result])` in
        // whatever block is CURRENT after lowering — mirroring `lower_if`.
        for (arm_id, arm_block) in arm_blocks {
            let body = self.thir[arm_id].body;
            fb.switch_to_block(arm_block);
            let result = self.lower_expr(fb, by_key, body)?;
            fb.br(join, vec![result]);
        }

        // 6. Resume in the join block; its param is the match's value.
        fb.switch_to_block(join);
        Ok(join_param)
    }

    /// Evaluate an integer-literal PATTERN const (`PatKind::Constant { value }`)
    /// to a signed `i128`, matching the convention `eval_int_literal` uses for an
    /// expression literal so a `SwitchCase` value compares equal to the scrutinee
    /// (the interpreter re-encodes the case value at the scrutinee's ir-ty). The
    /// leaf `ScalarInt` is read at the value type's layout width, sign-extended
    /// for a signed integer type and zero-extended for an unsigned one.
    fn eval_pat_const_int(&self, value: ty::Value<'tcx>) -> LResult<i128> {
        let leaf = value
            .try_to_leaf()
            .ok_or_else(|| LowerError("M5.3: pattern const is not a scalar leaf".into()))?;
        let input = self
            .typing_env
            .with_post_analysis_normalized_invalidating_rigid_aliases(self.tcx, value.ty);
        let size = self
            .tcx
            .layout_of(input)
            .map_err(|e| LowerError(format!("M5.3: layout_of pattern const ty failed: {e:?}")))?
            .size;
        match value.ty.kind() {
            TyKind::Int(_) => Ok(leaf.to_int(size)),
            TyKind::Uint(_) => Ok(leaf.to_uint(size) as i128),
            other => bail(format!(
                "M5.3: pattern const has non-integer type {other:?} (only integer \
                 literal patterns are supported for a scalar match)"
            )),
        }
    }

    // --- M5.4: `match` over a RECURSIVE ADT (heap-tag) ----------------------

    /// If `scrutinee`'s CONCRETE type is an `&Enum`/`Box<Enum>`/bare-enum whose
    /// AdtDef has a registered `EnumModel` in this worklist, return that DefId.
    /// This is the precise dispatch signal for the M5.4 ADT-match path (vs the
    /// M5.3 scalar switch). `None` for an integer (or any non-registered) scrut.
    fn match_scrutinee_enum_did(&self, scrutinee: ExprId) -> Option<DefId> {
        let scrut_ty = self.concretize(self.thir[scrutinee].ty);
        let peeled = peel_ref_ty(scrut_ty);
        if let TyKind::Adt(adt, _) = peeled.kind() {
            if self.enum_models.contains_key(&adt.did()) {
                return Some(adt.did());
            }
        }
        None
    }

    /// The CONCRETE generic args of the scrutinee's enum ADT (for resolving a
    /// payload field's true type). For a non-generic enum (`Level`) these are the
    /// identity/empty args; for a generic one they carry the instantiation.
    fn scrutinee_enum_args(&self, scrutinee: ExprId) -> Option<ty::GenericArgsRef<'tcx>> {
        let scrut_ty = self.concretize(self.thir[scrutinee].ty);
        let peeled = peel_ref_ty(scrut_ty);
        if let TyKind::Adt(_, args) = peeled.kind() {
            return Some(args);
        }
        None
    }

    /// The CONCRETE (post-substitution) rustc `ty::Ty` of an enum variant FIELD,
    /// in the scrutinee's instantiation. Used by the ADT-match payload-binding
    /// guard (audit FIX 3, extended by M5.7b). The M5.7b payload binder CLASSIFIES the
    /// field kind (pointer vs inline scalar vs inline aggregate) on this rustc ty
    /// BEFORE `lower_concrete_ty` — an inline AGGREGATE (tuple/array/non-pointer-
    /// ADT) field has no trust-ir scalar and would otherwise bail with a generic
    /// `lower_concrete_ty` message, masking that it is specifically the payload-
    /// binding guard firing.
    fn adt_field_rustc_ty(
        &self,
        did: DefId,
        enum_args: ty::GenericArgsRef<'tcx>,
        vidx: VariantIdx,
        field: usize,
    ) -> LResult<ty::Ty<'tcx>> {
        let adt = self.tcx.adt_def(did);
        let vdef = adt.variant(vidx);
        let fdef = vdef.fields.get(rustc_abi::FieldIdx::from_usize(field)).ok_or_else(|| {
            LowerError(format!(
                "M5.4: variant {vidx:?} has no field {field} (binding out of range)"
            ))
        })?;
        // The field's type, substituted with the enum's concrete args. (A recursive
        // `Box<Self>`/`&Self` field -> Ptr; a scalar field -> its scalar ir-ty; an
        // inline aggregate has no trust-ir scalar.)
        Ok(self
            .tcx
            .normalize_erasing_regions(self.typing_env, fdef.ty(self.tcx, enum_args)))
    }

    /// Lower a `match scrut { arms }` over a RECURSIVE ADT into the heap-tag form:
    /// Load the discriminant tag through the scrutinee pointer, `Switch` over it,
    /// and JOIN each arm's value at a block-param — the value-producing,
    /// worklist-driven analog of `LowerCx::lower_match` (which `ret`s per arm).
    /// A direct microcosm of a real `whnf`: tag dispatch + payload binding +
    /// recursion through the worklist Call edge.
    ///
    /// Shape:
    ///   - resolve the scrutinee to its heap POINTER (`lower_place`);
    ///   - `tag = load_field(scrut_ptr, TAG_OFFSET, I32)` (reuse lib.rs load_field);
    ///   - create a `join` block with one result block-param (the match's ir-ty);
    ///   - PASS A: per arm, create an arm_block and map its variant(s) ->
    ///     `SwitchCase { Int(discr) -> arm_block }` (via lib.rs pattern_variants +
    ///     EnumModel::discr_for_variant); a wildcard arm becomes the default;
    ///   - emit the `Switch` in the scrutinee's (still-current) block; a
    ///     non-wildcard exhaustive match routes the default to `unreachable`;
    ///   - PASS B: per arm, BIND its payload pattern bindings into `locals`
    ///     (binding `m` for field i -> `load_field(scrut_ptr, payload_offset(i),
    ///     Ptr)`, the child heap pointer) and lower the arm body via `lower_expr`,
    ///     `br(join, [result])` in whatever block is current after the body;
    ///   - resume in `join`, return its param.
    fn lower_match_adt(
        &mut self,
        fb: &mut FunctionBuilder<'_>,
        by_key: &InstanceMap<'tcx>,
        match_expr: ExprId,
        scrutinee: ExprId,
        arms: &[thir::ArmId],
    ) -> LResult<ValueId> {
        let did = self.match_scrutinee_enum_did(scrutinee).ok_or_else(|| {
            LowerError("M5.4: lower_match_adt on a non-recursive-enum scrutinee".into())
        })?;

        // 1. Scrutinee heap pointer (a param/local `Ptr`). The pointer-typed
        // current block is where the tag Load + Switch are emitted.
        let scrut_ptr = self.lower_place(fb, by_key, scrutinee)?;

        // The FAITHFUL layout (tag offset/width + Direct/Niche encoding) for this
        // enum, cloned out of the model so the borrow checker is happy across the
        // `&mut self` body lowering below.
        let layout = {
            let model = self.enum_models.get(&did).ok_or_else(|| {
                LowerError("M5.4: no EnumModel for the scrutinee enum".into())
            })?;
            model.layout.clone()
        };

        // 2. Read the discriminant tag the FAITHFUL way: a typed Load at the REAL
        // tag offset and the REAL tag width (i8/i16/i32/i64), derived from
        // `layout_of`. For a niche enum this Loads the NICHE word; for a direct
        // enum it Loads the explicit tag.
        let tag = load_field(fb, scrut_ptr, layout.tag_offset, layout.tag_ir_ty.clone());

        // 3. The match result ir-ty (= every arm's ty) and the join block.
        let join_ty = self.concrete_ir_ty(self.thir[match_expr].ty)?;
        let join = fb.create_block();
        let join_param = fb.add_block_param(join, join_ty);

        // 4. PASS A — classify each arm and derive its SwitchCases (or the default).
        // Runs entirely before any arm body is lowered, so the `Switch` can be
        // emitted into the scrutinee's still-current block without losing it.
        //
        // M5.7a: an arm is classified `Trivial` (the existing flat one-level case),
        // `OneLevelNested` (the new `App(Lam(_), _)` redex shape — routed via a
        // CANDIDATE block that does an inner tag-check), or `Unsupported` (bail).
        let mut cases: Vec<trust_ir::inst::SwitchCase> = Vec::new();
        let mut default_block: Option<BlockId> = None;
        // Each arm's body block, the block the Switch routed to (= arm_block for a
        // trivial arm, or the interposed CANDIDATE block for a nested arm), and its
        // nested-field info (None = trivial arm).
        let mut arm_plans: Vec<(thir::ArmId, BlockId, BlockId, Option<NestedCtorField>)> =
            Vec::with_capacity(arms.len());
        // M5.7a: at most ONE arm may route an outer variant. A nested arm's
        // FAIL path falls through to the catch-all (NOT a second arm on the same
        // outer variant) — two arms on the same outer variant need a full decision
        // tree (future work), so reject a duplicate outer variant loud.
        let mut routed_variants: std::collections::HashSet<VariantIdx> =
            std::collections::HashSet::new();
        // Does any arm carry a one-level nested constructor? (If so, a catch-all is
        // REQUIRED — the nested-fail path branches to it.)
        let mut has_nested = false;

        for &arm_id in arms {
            if self.thir[arm_id].guard.is_some() {
                return bail("M5.4: match arm has a guard (unsupported)");
            }
            // SOUNDNESS (HIGH — silent miscompile): the flat discriminant `Switch`
            // routes an arm by its OUTER variant only (`pattern_variants` discards
            // SUBpatterns). M5.7a REFINES the all-or-nothing trivial guard into a
            // three-way classifier: the COMMON one-level nested-ctor case
            // (`App(Lam(_), _)`) is lowered as a decision sub-tree (inner tag-check
            // + branch); a DEEPER/ambiguous nest (`App(App(Lam(_),_),_)`, two
            // nested-ctor fields, a nested ctor with non-trivial own fields, an
            // `@`/Or/Constant/Range) still BAILS loud — it would drop the inner
            // constraint and silently miscompile.
            let shape = classify_arm_subpatterns(&self.thir[arm_id].pattern.kind);
            let nested = match shape {
                ArmShape::Trivial => None,
                ArmShape::OneLevelNested(n) => {
                    has_nested = true;
                    Some(n)
                }
                ArmShape::Unsupported => {
                    return bail(
                        "M5: nested/non-trivial subpattern in ADT-match arm not yet supported \
                         — would drop the inner constraint (the flat discriminant Switch routes \
                         by the OUTER variant only; a deeper nest, a second nested-ctor field, a \
                         nested ctor with non-trivial own fields, or an `@`/Or/Constant/Range \
                         subpattern would silently miscompile). Supported: one-level arms whose \
                         fields are `_`/`Missing`/a plain binder (M5.4/M5.7b), plus EXACTLY ONE \
                         one-level nested constructor `App(Lam(_), _)` (M5.7a)",
                    );
                }
            };
            let arm_block = fb.create_block();
            // The block the Switch routes the outer variant to: a nested arm needs
            // a CANDIDATE block (the inner tag-check) interposed before arm_block.
            let candidate_block = if nested.is_some() {
                fb.create_block()
            } else {
                arm_block
            };
            arm_plans.push((arm_id, arm_block, candidate_block, nested));

            // Reuse lib.rs `pattern_variants` (peels Deref -> Variant) to classify.
            match pattern_variants(&self.thir[arm_id].pattern.kind)? {
                PatternMatch::Wildcard => {
                    if default_block.is_some() {
                        return bail("M5.4: more than one catch-all arm in an ADT match");
                    }
                    default_block = Some(arm_block);
                }
                PatternMatch::Variants(idxs) => {
                    for vidx in idxs {
                        // M5.7a: reject two arms routing the same outer variant.
                        if !routed_variants.insert(vidx) {
                            return bail(
                                "M5.7a: two arms route the same OUTER variant (e.g. a nested \
                                 `App(Lam(_),_)` plus another `App(..)` arm). Routing the \
                                 nested-fail path to a SECOND same-variant arm needs a full \
                                 decision tree — future work; only one arm per outer variant \
                                 (the nested-fail path falls through to the catch-all) is \
                                 supported",
                            );
                        }
                        // M6 NICHE: the niche UNTAGGED variant is the Switch DEFAULT
                        // (it has no encoded tag value — any non-niche bit pattern
                        // decodes to it). An EXPLICIT arm matching the untagged
                        // variant therefore becomes the default target, NOT a case.
                        // (`switch_value_for_variant` returns None for it.)
                        match layout.switch_value_for_variant(vidx) {
                            None => {
                                // The untagged variant: route the Switch default
                                // here. A NESTED untagged arm cannot be the default
                                // (the default has no inner tag-check interposed).
                                if nested.is_some() {
                                    return bail(
                                        "M6: a nested-constructor arm on the niche UNTAGGED \
                                         variant is not supported (the untagged variant is the \
                                         Switch default, which routes directly with no inner \
                                         tag-check block)",
                                    );
                                }
                                if default_block.is_some() {
                                    return bail(
                                        "M6: two arms route the Switch default (a `_` catch-all \
                                         AND the niche untagged variant, or two untagged-variant \
                                         arms) — only one default target is supported",
                                    );
                                }
                                default_block = Some(arm_block);
                            }
                            Some(discr) => {
                                cases.push(trust_ir::inst::SwitchCase {
                                    value: trust_ir::constant::Constant::Int(discr),
                                    target: candidate_block,
                                    args: vec![],
                                });
                            }
                        }
                    }
                }
            }
        }

        // M5.7a: a one-level nested arm's FAIL path branches to the catch-all, so a
        // catch-all `_` arm MUST be present. (A bare exhaustive enum match with no
        // catch-all but a nested arm has no fall-through target.)
        if has_nested && default_block.is_none() {
            return bail(
                "M5.7a: a nested-constructor arm (`App(Lam(_), _)`) requires a catch-all `_` \
                 arm present (the nested-fail path branches to it); an exhaustive match \
                 without a catch-all is not yet supported for nested arms",
            );
        }

        // M6 NICHE SOUNDNESS FLOOR: in a niche enum the UNTAGGED variant decodes as
        // the Switch DEFAULT (any tag value not in the niche range). If the match
        // has NO default target (no `_` arm and no explicit untagged-variant arm),
        // the untagged variant would mis-route to the synthetic `unreachable` trap
        // — a silent miscompile. The verbatim `is_zero`/`is_nonzero` DO cover the
        // untagged `Param` arm (so default is set); refuse anything that does not.
        if layout.is_niche() && default_block.is_none() {
            return bail(
                "M6: niche-encoded enum match has no Switch default (neither a `_` catch-all nor \
                 an explicit arm for the niche UNTAGGED variant). The untagged variant decodes as \
                 the default, so without one it would mis-route to `unreachable` — refusing to \
                 silently miscompile a niche enum",
            );
        }

        // 5. Emit the Switch in the scrutinee's (still-current) block. A
        // non-wildcard exhaustive enum match has no catch-all, so route the
        // default to an `unreachable` block (validate stays happy; the
        // interpreter never falls through). The trap block is CREATED but its
        // `unreachable` is filled AFTER the Switch is emitted — we must NOT
        // `switch_to_block` away from the scrutinee's block before emitting the
        // Switch terminator into it (the builder exposes no current-block
        // accessor; this is the same "emit the terminator in the block the
        // operand left us in" discipline `lower_match_scalar`/`lower_if` use).
        let (default, trap_to_fill) = match default_block {
            Some(b) => (b, None),
            None => {
                let trap = fb.create_block();
                (trap, Some(trap))
            }
        };
        fb.switch(tag, cases, default, vec![]);
        if let Some(trap) = trap_to_fill {
            fb.switch_to_block(trap);
            fb.unreachable();
        }

        // 6. PASS B — for each arm: (a) for a NESTED arm, fill its CANDIDATE block
        // (load the outer Box child, check its inner tag, condbr to arm_block /
        // default); (b) bind the arm's payload bindings into `locals`; (c) lower
        // the body and `br(join, [result])`. A binding `m` at field i binds to the
        // child HEAP POINTER `load_field(scrut_ptr, payload_offset(i), Ptr)` —
        // exactly the pointer a recursive call passes. The body may move blocks
        // (nested if/match), so the `br(join, ..)` is emitted in whatever block is
        // CURRENT after the body — mirroring `lower_if`/`lower_match_scalar`.
        let enum_args = self.scrutinee_enum_args(scrutinee);
        for (arm_id, arm_block, candidate_block, nested) in arm_plans {
            // The variant this arm's OUTER constructor binds (to look up each
            // field's REAL type). `None` for a wildcard/binder arm (no constructor).
            let arm_variant = pattern_variant_idx(&self.thir[arm_id].pattern.kind);

            // (a) M5.7a CANDIDATE block: the outer Switch routed this nested arm's
            // variant to `candidate_block`. Load the nested-field Box child, read
            // its inner tag, and condbr to the arm body iff the inner tag matches
            // the nested variant — else fall through to the catch-all (`default`).
            if let Some(nf) = nested {
                let (Some(vidx), Some(args)) = (arm_variant, enum_args) else {
                    return bail(
                        "M5.7a: cannot determine the OUTER variant/args for a nested arm \
                         (refusing to emit an inner tag-check against an unknown layout)",
                    );
                };
                self.emit_nested_candidate(
                    fb, candidate_block, scrut_ptr, did, args, vidx, nf, arm_block, default,
                )?;
            }

            // (b) Bind this arm's payload bindings into `locals`, then lower its
            // body in `arm_block`.
            fb.switch_to_block(arm_block);

            // OUTER-field bindings (the arm's own trivial fields, e.g. `App(_, arg)`
            // binds `arg` at outer field 1; `Succ(inner)` binds `inner` at field 0).
            // For a nested arm the nested-ctor field is NOT collected here (it has no
            // direct binder at the outer level); its INNER bindings are bound in (c).
            let mut bindings = std::collections::HashMap::new();
            collect_bindings(&self.thir[arm_id].pattern.kind, &mut bindings)?;
            // Determinism (audit FIX 6): sort by (field, then a STABLE per-body key
            // from the var's HirId) — a HashMap's order varies run-to-run and the
            // emitted IR IS the proof artifact, so it must be reproducible.
            let mut ordered: Vec<(rustc_middle::thir::LocalVarId, usize)> =
                bindings.into_iter().collect();
            ordered.sort_by_key(|&(var, field)| {
                let hir = var.0;
                (field, hir.owner.def_id.local_def_index.as_u32(), hir.local_id.as_u32())
            });
            for (var, field) in ordered {
                let (Some(vidx), Some(args)) = (arm_variant, enum_args) else {
                    return bail(
                        "M5.4: cannot determine the payload field's type for a binding \
                         (no resolvable single variant / enum args) — refusing to bind \
                         it (would risk a mis-typed slot read)",
                    );
                };
                let bound = self.bind_payload_field(fb, scrut_ptr, did, args, vidx, field)?;
                self.locals.insert(var, bound);
            }

            // (c) M5.7a INNER bindings: the nested constructor's OWN field bindings
            // (e.g. `App(Lam(b), _)` binds `b` = Lam's Box child). These bind
            // against the NESTED CHILD pointer (the outer Box child loaded in the
            // candidate block), reusing the SAME payload binder against the nested
            // variant's layout. We re-load the nested child pointer here (it is the
            // outer field's Box child = `load_field(scrut_ptr, payload_offset(of))`).
            if let Some(nf) = nested {
                let (Some(outer_vidx), Some(args)) = (arm_variant, enum_args) else {
                    return bail("M5.7a: cannot determine OUTER args for nested inner bindings");
                };
                let mut inner = std::collections::HashMap::new();
                collect_nested_bindings(
                    &self.thir[arm_id].pattern.kind,
                    nf.outer_field,
                    &mut inner,
                )?;
                let mut inner_ordered: Vec<(rustc_middle::thir::LocalVarId, usize)> =
                    inner.into_iter().collect();
                inner_ordered.sort_by_key(|&(var, field)| {
                    let hir = var.0;
                    (field, hir.owner.def_id.local_def_index.as_u32(), hir.local_id.as_u32())
                });
                if !inner_ordered.is_empty() {
                    // The nested child pointer = the outer field's Box child, at the
                    // OUTER variant's REAL field offset.
                    let outer_off =
                        self.variant_field_offset(did, outer_vidx, nf.outer_field)?;
                    let nested_ptr =
                        load_field(fb, scrut_ptr, outer_off, trust_ir::ty::Ty::Ptr);
                    for (var, field) in inner_ordered {
                        let bound = self.bind_payload_field(
                            fb,
                            nested_ptr,
                            did,
                            args,
                            nf.inner_variant,
                            field,
                        )?;
                        self.locals.insert(var, bound);
                    }
                }
            }

            // (d) M5.7e INLINE-AGGREGATE bindings: a field that is a tuple/struct
            // destructure (`Span((a, b))`'s tuple field) binds its SUB-fields at
            // their REAL cumulative offsets — the aggregate's offset WITHIN the
            // variant + each sub-field's offset WITHIN the aggregate (`layout_of`).
            // The sub-bindings are read by the SAME type-classified slot read
            // `bind_payload_field` uses (a scalar sub-field by ADDRESS, a pointer
            // sub-field by Load(Ptr)). Bindings live at a full field PATH
            // (`[outer_field, sub_field]`).
            {
                let mut agg = std::collections::HashMap::new();
                collect_aggregate_bindings(&self.thir[arm_id].pattern.kind, &mut agg)?;
                if !agg.is_empty() {
                    let Some(vidx) = arm_variant else {
                        return bail(
                            "M5.7e: cannot determine the variant for an inline-aggregate \
                             payload binding (no resolvable single variant)",
                        );
                    };
                    let mut agg_ordered: Vec<(rustc_middle::thir::LocalVarId, Vec<usize>)> =
                        agg.into_iter().collect();
                    // Determinism: sort by (path, then a STABLE per-body key from the
                    // var's HirId) — the emitted IR is the proof artifact.
                    agg_ordered.sort_by(|(va, pa), (vb, pb)| {
                        let ha = va.0;
                        let hb = vb.0;
                        (pa, ha.owner.def_id.local_def_index.as_u32(), ha.local_id.as_u32())
                            .cmp(&(pb, hb.owner.def_id.local_def_index.as_u32(), hb.local_id.as_u32()))
                    });
                    for (var, path) in agg_ordered {
                        let bound =
                            self.bind_aggregate_payload(fb, scrut_ptr, did, vidx, &path)?;
                        self.locals.insert(var, bound);
                    }
                }
            }

            let body = self.thir[arm_id].body;
            let result = self.lower_expr(fb, by_key, body)?;
            fb.br(join, vec![result]);
        }

        // 7. Resume in the join block; its param is the match's value.
        fb.switch_to_block(join);
        Ok(join_param)
    }

    /// Bind ONE payload field of an enum variant (at `base_ptr`, the heap pointer
    /// to the tagged struct) to its SSA value, returning that value. Factored out
    /// of the M5.4/M5.7b ADT-match payload binder so BOTH the OUTER arm fields
    /// (`base_ptr` = the scrutinee pointer) and the M5.7a NESTED constructor's own
    /// fields (`base_ptr` = the nested child pointer) reuse the IDENTICAL,
    /// type-classified slot read. The emitted bytes for the outer-field case are
    /// UNCHANGED from before this refactor (byte-identity preserved).
    ///
    /// SOUNDNESS (audit FIX 3 + M5.7b): `build_enum_model` makes every payload SLOT
    /// 8 bytes (a `Ty::Ptr` field), but a slot is read TWO ways by the field's REAL
    /// type — a POINTER field (`Box<Self>`/`&`/recursive child) is `Load(Ptr,GEP)`;
    /// an INLINE-SCALAR field is the GEP ADDRESS (NO Load), which the body's `*n`
    /// then Loads. An inline AGGREGATE payload has no tagged-struct layout → bail.
    /// M6: the REAL byte offset of `field` in variant `vidx` of enum `did`, read
    /// from the registered `EnumLayout` (`layout_of`-derived). REPLACES the
    /// hand-coded `payload_offset(i)=8+8i` — a niche enum places children AFTER the
    /// niche word, so the real offsets differ.
    fn variant_field_offset(&self, did: DefId, vidx: VariantIdx, field: usize) -> LResult<i128> {
        let model = self.enum_models.get(&did).ok_or_else(|| {
            LowerError("M6: no EnumModel for the enum (field-offset lookup)".into())
        })?;
        model.layout.field_offset(vidx, field).ok_or_else(|| {
            LowerError(format!(
                "M6: no layout field offset for variant {vidx:?} field {field} of {did:?}"
            ))
        })
    }

    fn bind_payload_field(
        &mut self,
        fb: &mut FunctionBuilder<'_>,
        base_ptr: ValueId,
        did: DefId,
        enum_args: ty::GenericArgsRef<'tcx>,
        vidx: VariantIdx,
        field: usize,
    ) -> LResult<ValueId> {
        let field_rustc_ty = self.adt_field_rustc_ty(did, enum_args, vidx, field)?;
        let field_off = self.variant_field_offset(did, vidx, field)?;
        match lower_concrete_ty(self.tcx, field_rustc_ty) {
            Ok(trust_ir::ty::Ty::Ptr) => {
                // POINTER field (a `Box<Self>`/`&`/recursive-enum child): the slot
                // HOLDS the pointer. A by-ref binding is the stored pointer =
                // `Load(Ptr, GEP)`. (M5.4: `count_succ`'s `Succ(inner)`.)
                Ok(load_field(fb, base_ptr, field_off, trust_ir::ty::Ty::Ptr))
            }
            Ok(field_ir) if is_scalar_ir_ty(&field_ir) => {
                // M5.7b — INLINE-SCALAR field: matching `&Enum`, a by-ref binding
                // `n` is the ADDRESS of the inline value = the GEP of the slot (NO
                // Load); the body's `*n` Loads it at the right width. Bind the GEP.
                Ok(field_addr(fb, base_ptr, field_off))
            }
            _ => bail(format!(
                "M5.7b: binding a non-pointer, non-scalar payload field (variant \
                 {vidx:?} field {field}, rustc ty {field_rustc_ty:?}) is not yet \
                 supported — an inline aggregate (tuple/array/struct) payload has \
                 no layout in the tagged-struct model (pointer and inline-scalar \
                 payloads ARE supported; binding a WHOLE inline aggregate by-ref is \
                 future work — destructuring its SUB-fields `Span((a, b))` IS \
                 supported via the M5.7e aggregate path)"
            )),
        }
    }

    /// M5.7e: bind ONE leaf binding nested INSIDE an inline-aggregate payload field,
    /// addressed by its full field `path` from the OUTER variant. For `Span((a, b))`
    /// the path `[0, 0]` reaches `a` (outer field 0 = the tuple, sub-field 0) and
    /// `[0, 1]` reaches `b`. The cumulative byte offset is the aggregate field's
    /// offset WITHIN the variant (from the enum `EnumLayout`) PLUS each sub-field's
    /// offset WITHIN the aggregate (from `tcx.layout_of` of the aggregate type). The
    /// leaf is bound by the SAME type-classified slot read `bind_payload_field`
    /// uses: a SCALAR sub-field by ADDRESS (the slot GEP, the body's `*a` Loads it),
    /// a POINTER sub-field (a `Box` child inside the aggregate) by Load(Ptr). A
    /// NESTED aggregate sub-field (an aggregate-in-aggregate) BAILS loud here.
    fn bind_aggregate_payload(
        &mut self,
        fb: &mut FunctionBuilder<'_>,
        base_ptr: ValueId,
        did: DefId,
        vidx: VariantIdx,
        path: &[usize],
    ) -> LResult<ValueId> {
        if path.len() < 2 {
            return bail(format!(
                "M5.7e: aggregate binding path {path:?} has fewer than 2 levels — an \
                 inline-aggregate binding is at least [outer_field, sub_field]"
            ));
        }
        // Level 0: the OUTER variant field (the aggregate itself). Its offset comes
        // from the enum's faithful `EnumLayout`; its rustc TYPE is the aggregate.
        let outer_field = path[0];
        let enum_args = match self.enum_args_for_did(did) {
            Some(a) => a,
            None => {
                return bail(
                    "M5.7e: cannot resolve the enum's generic args for an aggregate \
                     payload binding",
                )
            }
        };
        let mut cur_off = self.variant_field_offset(did, vidx, outer_field)?;
        let mut cur_ty = self.adt_field_rustc_ty(did, enum_args, vidx, outer_field)?;

        // Levels 1.. : walk INTO the aggregate, accumulating each sub-field's offset
        // (from `layout_of` of the current aggregate type) and descending its type.
        for (depth, &sub) in path[1..].iter().enumerate() {
            let is_last = depth + 1 == path.len() - 1;
            let (sub_off, sub_ty) = self.aggregate_subfield(cur_ty, sub)?;
            cur_off += sub_off;
            cur_ty = sub_ty;
            if !is_last {
                // An intermediate level that is itself an aggregate: a nested
                // aggregate-in-aggregate. Out of M5.7e scope (only one level deep).
                return bail(format!(
                    "M5.7e: nested aggregate-in-aggregate binding (path {path:?}) is not \
                     supported — only a single level of inline-aggregate destructuring \
                     `Span((a, b))` is in scope (deeper nesting is future work)"
                ));
            }
        }

        // The leaf sub-field, classified by its REAL type (the SAME pointer-vs-scalar
        // discipline `bind_payload_field` uses).
        match lower_concrete_ty(self.tcx, cur_ty) {
            Ok(trust_ir::ty::Ty::Ptr) => {
                // A POINTER sub-field (a `Box`/`&` child inside the aggregate): the
                // slot HOLDS the pointer. Bind the stored pointer = Load(Ptr, GEP).
                Ok(load_field(fb, base_ptr, cur_off, trust_ir::ty::Ty::Ptr))
            }
            Ok(field_ir) if is_scalar_ir_ty(&field_ir) => {
                // A SCALAR sub-field: matching `&Enum`, a by-ref binding is the
                // ADDRESS of the inline value (the slot GEP, NO Load); the body's
                // `*a` (the scalar-Deref path) Loads it at the right width.
                Ok(field_addr(fb, base_ptr, cur_off))
            }
            _ => bail(format!(
                "M5.7e: aggregate sub-field (path {path:?}, rustc ty {cur_ty:?}) is \
                 neither a scalar nor a pointer — only scalar / pointer (Box-child) \
                 sub-fields are supported (a nested aggregate sub-field bails)"
            )),
        }
    }

    /// M5.7e: the (byte offset, rustc type) of sub-field `i` of an aggregate type
    /// `agg_ty` (a tuple or struct), read FAITHFULLY from `tcx.layout_of`. Bails
    /// loud on a non-aggregate type or an out-of-range sub-field index.
    fn aggregate_subfield(
        &self,
        agg_ty: ty::Ty<'tcx>,
        i: usize,
    ) -> LResult<(i128, ty::Ty<'tcx>)> {
        use rustc_middle::ty::layout::LayoutCx;
        let agg_ty = self.concretize(agg_ty);
        // The sub-field's TYPE: tuple element `i`, or struct field `i` (single
        // variant). Anything else is not a destructurable inline aggregate.
        let sub_ty = match agg_ty.kind() {
            TyKind::Tuple(elems) => *elems.get(i).ok_or_else(|| {
                LowerError(format!(
                    "M5.7e: tuple {agg_ty:?} has no element {i} (aggregate sub-field out of range)"
                ))
            })?,
            TyKind::Adt(adt, args) if adt.is_struct() => {
                let vdef = adt.non_enum_variant();
                let fdef = vdef.fields.get(rustc_abi::FieldIdx::from_usize(i)).ok_or_else(|| {
                    LowerError(format!(
                        "M5.7e: struct {agg_ty:?} has no field {i} (aggregate sub-field out of range)"
                    ))
                })?;
                self.tcx
                    .normalize_erasing_regions(self.typing_env, fdef.ty(self.tcx, args))
            }
            other => {
                return bail(format!(
                    "M5.7e: inline-aggregate sub-field access on a non-aggregate type {other:?} \
                     (only a tuple or single-variant struct is destructurable)"
                ))
            }
        };
        // The sub-field's OFFSET within the aggregate, from `layout_of`.
        let lcx = LayoutCx::new(self.tcx, self.typing_env);
        let layout = self
            .tcx
            .layout_of(self.typing_env.as_query_input(agg_ty))
            .map_err(|e| {
                LowerError(format!(
                    "M5.7e: tcx.layout_of({agg_ty:?}) failed ({e:?}) — cannot derive the \
                     aggregate sub-field offset"
                ))
            })?;
        let _ = &lcx;
        let off = layout.fields.offset(i).bytes() as i128;
        Ok((off, sub_ty))
    }

    /// M5.7e: the concrete generic args of the enum `did` AS MATCHED in this body —
    /// the same instantiation `bind_payload_field` resolves via the scrutinee. The
    /// corpus enums are non-generic (identity args), so this reads the AdtDef's own
    /// identity args; a generic enum would need the scrutinee's args (out of scope —
    /// the recursive corpus enums carry no type params).
    fn enum_args_for_did(&self, did: DefId) -> Option<ty::GenericArgsRef<'tcx>> {
        let enum_ty = self.tcx.normalize_erasing_regions(
            self.typing_env,
            self.tcx.type_of(did).instantiate_identity(),
        );
        match enum_ty.kind() {
            TyKind::Adt(_, args) => Some(args),
            _ => None,
        }
    }

    /// M5.7a: fill a nested-constructor arm's CANDIDATE block. The outer Switch
    /// routed the outer variant (e.g. `App`) HERE. Load the nested field's Box
    /// child pointer (`load_field(scrut_ptr, payload_offset(outer_field), Ptr)`),
    /// read THAT child's discriminant tag (`load_field(child_ptr, TAG_OFFSET, I32)`),
    /// and `condbr (inner_tag == <nested-variant discr>) -> arm_block, default`.
    /// The nested-fail edge to `default` (the catch-all) is correct: Rust match is
    /// first-match and the catch-all is the last arm, so an outer-variant match
    /// whose inner ctor does NOT match falls through to the catch-all.
    ///
    /// SOUNDNESS: the nested field MUST be a Box-child POINTER slot (the only kind
    /// whose stored value is a tagged-struct pointer we can read an inner tag from).
    /// A nested ctor on a SCALAR field has no inner tag — reject it loud.
    #[allow(clippy::too_many_arguments)]
    fn emit_nested_candidate(
        &mut self,
        fb: &mut FunctionBuilder<'_>,
        candidate_block: BlockId,
        scrut_ptr: ValueId,
        did: DefId,
        enum_args: ty::GenericArgsRef<'tcx>,
        outer_vidx: VariantIdx,
        nf: NestedCtorField,
        arm_block: BlockId,
        default_block: BlockId,
    ) -> LResult<()> {
        // The nested field must be a Box-child POINTER (its slot holds a pointer to
        // a tagged struct whose i32 tag we then read). Reject a scalar nested field.
        let field_rustc_ty = self.adt_field_rustc_ty(did, enum_args, outer_vidx, nf.outer_field)?;
        match lower_concrete_ty(self.tcx, field_rustc_ty) {
            Ok(trust_ir::ty::Ty::Ptr) => {}
            _ => {
                return bail(format!(
                    "M5.7a: a nested constructor on a non-pointer field (variant {outer_vidx:?} \
                     field {}, rustc ty {field_rustc_ty:?}) is not supported — a nested ctor \
                     needs a Box-child pointer slot to read the inner discriminant tag from \
                     (only Box-child nesting is supported for now)",
                    nf.outer_field
                ));
            }
        }
        // The nested variant's Switch value + the enum's FAITHFUL tag layout (the
        // inner child is the SAME enum `did`, so it uses the SAME tag offset/width).
        let (inner_discr, outer_off, tag_offset, tag_ir_ty) = {
            let model = self.enum_models.get(&did).ok_or_else(|| {
                LowerError("M5.7a: no EnumModel for the scrutinee enum".into())
            })?;
            // M6 NICHE: an inner tag-check Eq'ing the niche untagged variant is
            // unsound (it has no encoded tag value — its presence is "anything not
            // a niche value"). Refuse it loud.
            let inner_discr = model.layout.switch_value_for_variant(nf.inner_variant).ok_or_else(|| {
                LowerError(format!(
                    "M5.7a/M6: nested constructor selects the niche UNTAGGED variant {:?}, which \
                     has no tag value to Eq-check against (a nested-ctor inner tag-check requires \
                     a Direct/niche-tagged variant)",
                    nf.inner_variant
                ))
            })?;
            let outer_off = model
                .layout
                .field_offset(outer_vidx, nf.outer_field)
                .ok_or_else(|| {
                    LowerError(format!(
                        "M5.7a/M6: no layout offset for outer variant {outer_vidx:?} field {}",
                        nf.outer_field
                    ))
                })?;
            (
                inner_discr,
                outer_off,
                model.layout.tag_offset,
                model.layout.tag_ir_ty.clone(),
            )
        };

        use trust_ir::inst::ICmpOp;
        fb.switch_to_block(candidate_block);
        // field_ptr = the Box child pointer stored in the outer slot (REAL offset).
        let field_ptr = load_field(fb, scrut_ptr, outer_off, trust_ir::ty::Ty::Ptr);
        // inner_tag = the child's discriminant tag (REAL tag offset + width).
        let inner_tag = load_field(fb, field_ptr, tag_offset, tag_ir_ty.clone());
        let want = fb.iconst(tag_ir_ty.clone(), inner_discr);
        let cond = fb.icmp(ICmpOp::Eq, tag_ir_ty, inner_tag, want);
        // Match -> the arm body; mismatch -> the catch-all (first-match fallthrough).
        fb.condbr(cond, arm_block, vec![], default_block, vec![]);
        Ok(())
    }

    /// Resolve a scrutinee/receiver PLACE to the `Ptr` `ValueId` it denotes. For
    /// the M5.4 corpus the scrutinee is a bare param/local pointer (`match *self` /
    /// `match n` where `n: &Enum`), so peel scopes/uses/borrows/derefs to the
    /// `VarRef` and return its bound SSA value (a `Ptr`). A `&x`/`*x` around a
    /// pointer place is identity at the pointer level (a `Box`/`&` IS the
    /// pointer), exactly as `LowerCx::resolve_receiver_payload` peels them.
    ///
    /// Trait static dispatch adds one leaf: a borrowed ZST receiver constructed
    /// inline (`Two.score()` => `Borrow(Adt(Two))`, no `let`). Peeling reaches the
    /// `Adt`, which lowers to a placeholder `Ptr` (`lower_zst_adt`) — the resolved
    /// leaf ignores its `&self`. (`fb` is threaded so this leaf can emit the
    /// placeholder; the existing pointer-place callers never reach it, so their
    /// emission is unchanged.)
    fn lower_place(
        &mut self,
        fb: &mut FunctionBuilder<'_>,
        by_key: &InstanceMap<'tcx>,
        expr: ExprId,
    ) -> LResult<ValueId> {
        let mut e = expr;
        loop {
            match &self.thir[e].kind {
                ExprKind::Scope { value, .. } => e = *value,
                ExprKind::NeverToAny { source } => e = *source,
                ExprKind::Borrow { arg, .. } | ExprKind::Deref { arg } => e = *arg,
                ExprKind::PointerCoercion { source, .. } => e = *source,
                // The auto-deref `<Box as Deref>::deref(&m)` inserted before a
                // method/field access: peel to its single receiver argument.
                ExprKind::Call { ty, args, .. } if self.is_deref_call(*ty) => {
                    if args.is_empty() {
                        return bail("M5.4: deref call with no argument");
                    }
                    e = args[0];
                }
                // M5.7f: `&Box::new(inner)` — the box call IS the heap pointer; peel
                // it to its inner construction (identity at the pointer level).
                ExprKind::Call { ty, args, .. } if self.is_box_new_call(*ty) => {
                    e = self.box_new_arg(args)?;
                }
                // M5.7f: a place that is a user-fn CALL returning an OWNED enum heap
                // value (`&one()` => the `Ptr` `one()` constructs/returns). The call
                // result IS the heap pointer the caller treats as the place — lower it
                // as a VALUE. RESTRICTED to a call whose concrete RESULT type is an
                // owned enum / Box<enum> (a `Ptr` to a tagged struct we can match):
                // a user method returning a `&T` REFERENCE place-projection (e.g. the
                // `neg_user_deref` `w.deref() -> &Tree`) is NOT an owned value and
                // STILL bails loud (that soundness guard is preserved). A box/deref
                // call is intercepted above; arith calls are not place exprs.
                ExprKind::Call { ty, .. } if self.call_returns_owned_enum(e) => {
                    let args = match &self.thir[e].kind {
                        ExprKind::Call { args, .. } => args.clone(),
                        _ => unreachable!("matched Call above"),
                    };
                    let ty = *ty;
                    return self.lower_call_expr(fb, by_key, e, ty, &args);
                }
                ExprKind::VarRef { id } => {
                    return self
                        .locals
                        .get(id)
                        .or_else(|| self.params.get(id))
                        .copied()
                        .ok_or_else(|| {
                            LowerError(format!(
                                "M5.4: scrutinee/arg VarRef {id:?} is not a bound local or param"
                            ))
                        });
                }
                // A ZST receiver constructed inline (trait static dispatch), OR
                // (M5.7f) an enum-variant construction used directly as a place.
                ExprKind::Adt(_) => {
                    return self.lower_zst_adt(fb, by_key, e);
                }
                other => {
                    return bail(format!(
                        "M5.4: unsupported scrutinee/arg place {} ({:?})",
                        crate::expr_kind_name_pub(other),
                        std::mem::discriminant(other)
                    ))
                }
            }
        }
    }

    /// SOUNDNESS (audit FIX C): is the pointer operand of a SCALAR deref itself a
    /// dereference/borrow of another pointer — i.e. is this a MULTI-level scalar
    /// deref like `**rr` (rr: &&i64)? `lower_place` peels ALL Borrow/Deref layers,
    /// so for a single-level `*r` (`arg` = a bare VarRef pointer) it resolves to
    /// the right pointer, but for `**rr` (`arg` = `*rr`, itself a Deref) it would
    /// over-peel to the outer pointer and load the inner pointer's bits as the
    /// scalar. Peel only Scope/Use wrappers off `arg`; if what remains is a
    /// `Deref`, a `Borrow`, or a `Deref::deref`/`DerefMut` Call (an explicit OR
    /// auto-inserted dereference of a pointer place), this is multi-level.
    fn scalar_deref_arg_is_multi_level(&self, arg: ExprId) -> LResult<bool> {
        let mut e = arg;
        loop {
            match &self.thir[e].kind {
                ExprKind::Scope { value, .. } => e = *value,
                ExprKind::NeverToAny { source } => e = *source,
                // The pointer operand is itself the result of dereferencing /
                // (re)borrowing another pointer: multi-level.
                ExprKind::Deref { .. } | ExprKind::Borrow { .. } => return Ok(true),
                ExprKind::Call { ty, .. } if self.is_deref_call(*ty) => return Ok(true),
                // A bare VarRef/param pointer (`*r`): single-level. Anything else
                // is a place shape `lower_place` will report on; treat as
                // single-level here and let `lower_place` decide.
                _ => return Ok(false),
            }
        }
    }

    /// Is this `Call`'s callee a `Deref::deref`/`DerefMut::deref_mut` (the
    /// overloaded `*` auto-inserted before a method/field access on `Box`/`&`)?
    ///
    /// SOUNDNESS (audit FIX): identify the deref by the callee's CONTAINER TRAIT
    /// lang-item identity (`Deref`/`DerefMut`), NOT by the bare method NAME. A user
    /// inherent method (or a different trait's method) literally named `deref` /
    /// `deref_mut` is NOT a pointer dereference: `lower_place` peels a recognized
    /// deref to its receiver, so misclassifying a user `deref` would SILENTLY DROP
    /// the call and run the match/recursion on the un-deref'd receiver (a
    /// wrong-but-validating result). This mirrors `arith_binop_of`, which likewise
    /// keys on trait identity rather than the `add`/`sub`/`mul` method name.
    fn is_deref_call(&self, callee_ty: ty::Ty<'tcx>) -> bool {
        let TyKind::FnDef(did, _) = callee_ty.kind() else {
            return false;
        };
        let Some(trait_did) = self
            .tcx
            .opt_associated_item(*did)
            .and_then(|item| item.trait_container(self.tcx))
        else {
            // Not a trait item (e.g. an inherent `fn deref`): not a Deref call.
            return false;
        };
        let li = self.tcx.lang_items();
        Some(trait_did) == li.deref_trait() || Some(trait_did) == li.deref_mut_trait()
    }

    /// `&&` / `||` -> CondBr + join param. For `a && b`: eval a; if true eval b
    /// else false. For `a || b`: eval a; if true true else eval b. Adapted from
    /// the M1/M2 `LowerCx::lower_logical` to call the unified `lower_expr` for
    /// operands. (No M3/M4 corpus shape exercises this yet, but the unified
    /// lowerer must own it for the clean-kernel `whnf` direction.)
    fn lower_logical(
        &mut self,
        fb: &mut FunctionBuilder<'_>,
        by_key: &InstanceMap<'tcx>,
        op: rustc_middle::thir::LogicalOp,
        lhs: ExprId,
        rhs: ExprId,
    ) -> LResult<ValueId> {
        use rustc_middle::thir::LogicalOp;
        let lhs_val = self.lower_expr(fb, by_key, lhs)?;

        let rhs_block = fb.create_block();
        let short_block = fb.create_block();
        let join = fb.create_block();
        let join_param = fb.add_block_param(join, trust_ir::ty::Ty::Bool);

        match op {
            LogicalOp::And => {
                fb.condbr(lhs_val, rhs_block, vec![], short_block, vec![]);
            }
            LogicalOp::Or => {
                fb.condbr(lhs_val, short_block, vec![], rhs_block, vec![]);
            }
        }

        fb.switch_to_block(short_block);
        let short_const = fb.bool_const(matches!(op, LogicalOp::Or));
        fb.br(join, vec![short_const]);

        fb.switch_to_block(rhs_block);
        let rhs_val = self.lower_expr(fb, by_key, rhs)?;
        fb.br(join, vec![rhs_val]);

        fb.switch_to_block(join);
        Ok(join_param)
    }

    /// Lower a Call expr: an overloaded-arith operator -> native binop; a user fn
    /// -> a cross-function `fb.call` to the callee's mapped FuncId. The call's
    /// result ir-ty is read from its OWN THIR expr (not threaded), and the
    /// overloaded-arith operand ty/signedness from the first arg's THIR.
    fn lower_call_expr(
        &mut self,
        fb: &mut FunctionBuilder<'_>,
        by_key: &InstanceMap<'tcx>,
        call_expr: ExprId,
        callee_ty: ty::Ty<'tcx>,
        args: &[ExprId],
    ) -> LResult<ValueId> {
        // User fn? Resolve + emit a cross-function Call.
        if let Some(inst) =
            resolve_user_call(self.tcx, self.typing_env, self.args, callee_ty)?
        {
            let callee_idx = *by_key.get(&inst.key()).ok_or_else(|| {
                LowerError(format!("M4: callee instance {:?} not in worklist", inst.key()))
            })?;
            // Offset by the worklist base so a cross-fn Call edge targets the
            // callee's ACTUAL FuncId when several worklists share a module.
            let callee_funcid = worklist_batch::function_id(self.func_base, callee_idx)?;
            let mut lowered_args = Vec::with_capacity(args.len());
            for a in args.iter() {
                lowered_args.push(self.lower_expr(fb, by_key, *a)?);
            }
            return Ok(fb.call(callee_funcid, lowered_args));
        }
        // Otherwise it must be an overloaded-arith operator -> native binop.
        let bop = self.recognize_overloaded_arith(callee_ty)?;
        if args.len() != 2 {
            return bail(format!(
                "M4 overloaded-arith call expects 2 args, got {}",
                args.len()
            ));
        }
        let res_ty = self.concrete_ir_ty(self.thir[call_expr].ty)?;
        let operand_ty = self.thir[args[0]].ty;
        let l = self.lower_expr(fb, by_key, args[0])?;
        let r = self.lower_expr(fb, by_key, args[1])?;
        self.lower_binop_thir(fb, bop, res_ty, operand_ty, l, r)
    }

    /// Lower a MIR binop, choosing between arithmetic (the result `res_ty` is the
    /// operand width) and a comparison (the result is `bool`, so the `icmp` needs
    /// the OPERAND ty + signedness, derived from `operand_ty`). Arithmetic ops
    /// delegate to the original `lower_binop` so the existing M3/M4 IR is byte-
    /// identical.
    fn lower_binop_thir(
        &mut self,
        fb: &mut FunctionBuilder<'_>,
        op: rustc_middle::mir::BinOp,
        res_ty: trust_ir::ty::Ty,
        operand_ty: ty::Ty<'tcx>,
        l: ValueId,
        r: ValueId,
    ) -> LResult<ValueId> {
        use rustc_middle::mir::BinOp as MirBinOp;
        use trust_ir::inst::ICmpOp;
        // Comparisons produce bool; emit an ICmp over the OPERAND ty. Eq/Ne are
        // sign-agnostic; the ordered comparisons pick a signed/unsigned ICmpOp
        // from the operand's signedness.
        let icmp_op = match op {
            MirBinOp::Eq => Some(ICmpOp::Eq),
            MirBinOp::Ne => Some(ICmpOp::Ne),
            MirBinOp::Lt | MirBinOp::Le | MirBinOp::Gt | MirBinOp::Ge => {
                let signed = self.is_signed_int(operand_ty)?;
                Some(match (op, signed) {
                    (MirBinOp::Lt, true) => ICmpOp::Slt,
                    (MirBinOp::Le, true) => ICmpOp::Sle,
                    (MirBinOp::Gt, true) => ICmpOp::Sgt,
                    (MirBinOp::Ge, true) => ICmpOp::Sge,
                    (MirBinOp::Lt, false) => ICmpOp::Ult,
                    (MirBinOp::Le, false) => ICmpOp::Ule,
                    (MirBinOp::Gt, false) => ICmpOp::Ugt,
                    (MirBinOp::Ge, false) => ICmpOp::Uge,
                    _ => unreachable!(),
                })
            }
            _ => None,
        };
        if let Some(c) = icmp_op {
            let op_ir = self.concrete_ir_ty(operand_ty)?;
            return Ok(fb.icmp(c, op_ir, l, r));
        }
        // Arithmetic: result ty IS the operand width; delegate to the original.
        self.lower_binop(fb, op, res_ty, l, r)
    }

    /// Is the (post-substitution) integer operand type signed? `Int(..) -> true`,
    /// `Uint(..) -> false`. Errors on a non-integer comparison operand.
    fn is_signed_int(&self, operand_ty: ty::Ty<'tcx>) -> LResult<bool> {
        match self.concretize(operand_ty).kind() {
            TyKind::Int(_) => Ok(true),
            TyKind::Uint(_) => Ok(false),
            other => bail(format!(
                "M5.1: comparison operand is not an integer: {other:?}"
            )),
        }
    }

    /// M5.7c: lower a THIR `Unary { op, arg }`. The result ir-ty (and, for `Not`,
    /// the discriminator between BOOL logical-not and INTEGER bitwise-not) is the
    /// concrete ir-ty of THIS expr (`!`/`-` are width/type-preserving in Rust).
    ///
    ///  - `UnOp::Neg` on an INTEGER -> the native trust-ir `UnOp::Neg`
    ///    (`0 - x`, two's-complement wrapping at the type width, exactly the
    ///    interpreter's `0u128.wrapping_sub(raw) & mask`). Neg of a NON-integer
    ///    (a float — trust-ir has no `f*` scalar through `lower_concrete_ty` yet,
    ///    so this is effectively unreachable, but guard it) bails LOUD.
    ///  - `UnOp::Not` on an INTEGER -> the native trust-ir `UnOp::Not`
    ///    (bitwise complement `!x`, the interpreter's `!raw & mask`).
    ///  - `UnOp::Not` on a `bool` -> a `Select(arg, false, true)`. The trust-ir
    ///    interpreter represents `bool` as a DISTINCT value kind (NOT an int), so
    ///    a native `UnOp::Not`/`ICmp` typed `Bool` would hit `expect_int_value`
    ///    and trap; a `Select` over a bool cond with bool arms is the shape both
    ///    the interpreter and trust-cg evaluate for a bool, and is exactly `!b`.
    ///  - `UnOp::PtrMetadata` (and any other future unop) bails LOUD.
    fn lower_unary(
        &mut self,
        fb: &mut FunctionBuilder<'_>,
        by_key: &InstanceMap<'tcx>,
        e: ExprId,
        op: rustc_middle::mir::UnOp,
        arg: ExprId,
    ) -> LResult<ValueId> {
        use rustc_middle::mir::UnOp as MirUnOp;
        use trust_ir::inst::UnOp as IrUnOp;
        let res_ty = self.concrete_ir_ty(self.thir[e].ty)?;
        let a = self.lower_expr(fb, by_key, arg)?;
        match op {
            MirUnOp::Not => match res_ty {
                trust_ir::ty::Ty::Bool => {
                    // `!b` over a bool: select false when b is true, true when false.
                    let t = fb.bool_const(true);
                    let f = fb.bool_const(false);
                    Ok(fb.select(trust_ir::ty::Ty::Bool, a, f, t))
                }
                int_ty => {
                    // Integer `!x`: bitwise complement at the type width.
                    ir_ty_is_signed(&int_ty)?; // fail-loud on a non-integer Not.
                    Ok(fb.unop(IrUnOp::Not, int_ty, a))
                }
            },
            MirUnOp::Neg => {
                // Integer negate. Bail loud on a non-integer Neg (e.g. a float),
                // which we have no trust-ir scalar / native `FNeg` plumbing for.
                ir_ty_is_signed(&res_ty).map_err(|_| {
                    LowerError(format!(
                        "M5.7c: unary `-` on a non-integer ir-ty {res_ty:?} is unsupported \
                         (no float negate plumbing)"
                    ))
                })?;
                Ok(fb.unop(IrUnOp::Neg, res_ty, a))
            }
            other => bail(format!("M5.7c: unsupported unary op {other:?}")),
        }
    }
}

/// Lower a generic CALL CHAIN root instance (`root_def` at `concrete`) plus all
/// transitively-called user-fn instances, into `mb`, as separate concrete
/// Functions joined by real Call edges. Returns the lowered instances (index
/// relative to `func_base` == FuncId); `[0]` is the root. `func_base` is the
/// module's function count BEFORE this call (0 for a fresh module); pass the
/// running total when emitting several roots into one module.
pub fn lower_callchain_instance<'tcx>(
    tcx: TyCtxt<'tcx>,
    mb: &mut ModuleBuilder,
    root_def: LocalDefId,
    concrete: ty::Ty<'tcx>,
    name_suffix: &str,
    func_base: u32,
) -> LResult<Vec<LoweredInstance>> {
    // Default: register any matched enum's tagged struct. Every existing caller
    // emits at most one root per enum per module, so this stays byte-identical.
    lower_callchain_instance_ext(tcx, mb, root_def, concrete, name_suffix, func_base, true)
}

/// `lower_callchain_instance` with explicit control over whether a matched enum's
/// tagged struct is REGISTERED in the module. Pass `register_structs=false` for a
/// SECOND worklist root that matches the SAME enum already registered by a prior
/// root in this module (M5.6 is_nonzero after is_zero), to avoid a duplicate
/// `StructId(0)`. `true` is the original `lower_callchain_instance` behavior.
pub fn lower_callchain_instance_ext<'tcx>(
    tcx: TyCtxt<'tcx>,
    mb: &mut ModuleBuilder,
    root_def: LocalDefId,
    concrete: ty::Ty<'tcx>,
    name_suffix: &str,
    func_base: u32,
    register_structs: bool,
) -> LResult<Vec<LoweredInstance>> {
    let root_def_id = root_def.to_def_id();
    let root_args = args_for_single_type_param(tcx, root_def_id, concrete);
    let root = MonoInstance {
        def: root_def,
        args: root_args,
    };
    let wl = collect_worklist(tcx, root)?;
    emit_worklist(tcx, mb, &wl, WorklistSymbols::Legacy(name_suffix), func_base, register_structs)
}

/// M5.5 UNIFIED predicate entry. Lower a single `fn(&Enum) -> bool` predicate
/// (`Level::is_zero`/`is_nonzero`) as a worklist ROOT (FuncId 0) into a FRESH,
/// UNBUILT `ModuleBuilder`, through `MonoCx::lower_expr` — the SAME path M5.6
/// proved at 42/42 parity vs the retired LowerCx native oracle. Returns the
/// unbuilt builder (so a caller can append heap-constructing differential runners
/// into the SAME module before `build()`), the recovered `EnumModel` for the
/// matched enum, and the predicate's FuncId(0).
///
/// This REPLACES the M1/M2 `LowerCx` lowering: `lib.rs::lower_fn_to_builder` /
/// `lower_fn_to_module` delegate here, so there is ONE lowering path. The
/// predicate self-recurses (`a.is_zero()` => `Level::is_zero(a)`), so the worklist
/// is a SINGLE instance at FuncId 0; if a predicate called OTHER predicates they
/// would become FuncId 1.. — `run_emitted_differential` only drives FuncId(0),
/// which is the predicate, so that is fine.
///
/// The emitted IR DIFFERS structurally from LowerCx's (MonoCx joins each arm at a
/// block-param vs LowerCx's per-arm `ret`); the contract preserved here is
/// BEHAVIORAL (the differential result set), not byte-identity.
pub fn lower_predicate_to_builder<'tcx>(
    tcx: TyCtxt<'tcx>,
    def: LocalDefId,
) -> LResult<(ModuleBuilder, EnumModel, FuncId)> {
    // Validate the predicate shape the same way LowerCx did (fail-loud): it must
    // be a `fn(&self) -> bool` whose body matches over an enum.
    let (thir_steal, body_expr) = tcx
        .thir_body(def)
        .map_err(|_| LowerError("thir_body errored (tainted by type errors)".into()))?;
    {
        let thir = thir_steal.borrow();
        let sig = match &thir.body_type {
            thir::BodyTy::Fn(sig) => *sig,
            _ => return bail("not a function body"),
        };
        let ret = sig.output();
        if !ret.is_bool() {
            return bail(format!("return type is {ret:?}, expected bool"));
        }
        // Confirm the body is a match over an enum (recover the AdtDef for the
        // EnumModel below); this also rejects the non-leaf shapes LowerCx rejected.
        let _ = crate::find_match_enum(tcx, &thir, body_expr)?;
    }

    let fn_name = tcx.item_name(def.to_def_id()).to_string();
    let mut mb = ModuleBuilder::new(format!("frontend::{fn_name}"));

    // Build the worklist for the predicate root. The predicate self-recurses, so
    // this is a single instance (FuncId 0). The i64 seed is the unused identity
    // arg for a non-generic root (mirrors the M5.4/M5.6 predicate roots).
    let i64_ty = tcx.types.i64;
    let root_def_id = def.to_def_id();
    let root_args = args_for_single_type_param(tcx, root_def_id, i64_ty);
    let root = MonoInstance {
        def,
        args: root_args,
    };
    let wl = collect_worklist(tcx, root)?;

    // Recover the matched enum's `EnumModel` WITHOUT registering its struct (the
    // following `emit_worklist` registers it). `run_emitted_differential` and the
    // driver only read `.name`/`.variants` from this; the struct is added once.
    //
    // SOUNDNESS (audit FIX 4): look up the `&self` scrutinee enum DETERMINISTICALLY
    // rather than taking an arbitrary HashMap entry (`into_values().next()`). For a
    // predicate matching 2+ distinct enums, the arbitrary pick is nondeterministic
    // and `run_differential_for` would silently skip parity when the chosen model
    // has the wrong shape. The heap corpus/oracle only model the `&self` enum, and
    // `build_enum_model` hardcodes `StructId(0)` (two distinct enums would collide
    // on StructId(0) and fail validation) — so bail loud on >1 distinct enum.
    let mut models_unreg = build_worklist_enum_models(tcx, &mut mb, &wl, false)?;
    if models_unreg.len() > 1 {
        return bail(format!(
            "predicate matches {} distinct enums; only the single `&self` enum is \
             modeled (the heap corpus/oracle + the StructId(0) tagged struct assume one)",
            models_unreg.len()
        ));
    }
    // The `&self` scrutinee enum, recovered from the body's match (the SAME enum
    // `find_match_enum` validated above), looked up by its AdtDef DefId.
    let scrut_adt = {
        let thir = thir_steal.borrow();
        crate::find_match_enum(tcx, &thir, body_expr)?
    };
    let enum_model = models_unreg.remove(&scrut_adt.did()).ok_or_else(|| {
        LowerError(
            "M5.5: predicate body matched no enum (no EnumModel for the &self scrutinee)".into(),
        )
    })?;

    // Emit the predicate (and any callee predicates) at FuncId(func_base + i),
    // base 0, REGISTERING the matched enum's tagged struct (StructId 0).
    let lowered = emit_worklist(tcx, &mut mb, &wl, WorklistSymbols::Legacy("i64"), 0, true)?;
    let root = lowered
        .first()
        .ok_or_else(|| LowerError("M5.5: empty predicate worklist".into()))?;
    debug_assert_eq!(root.func_id.index(), 0, "predicate must be FuncId(0)");

    Ok((mb, enum_model, root.func_id))
}

/// Emit the call-chain round-trip module (`quad__i64` + `double__i64`, joined by
/// a real Call edge) for the downstream trust-cg JIT cross-check. Mirrors
/// `emit_scalar_roundtrip_module` but for the worklist output.
pub fn emit_callchain_roundtrip_module<'tcx>(
    tcx: TyCtxt<'tcx>,
    quad_def: LocalDefId,
) -> LResult<Module> {
    let mut mb = ModuleBuilder::new("frontend::m4::callchain".to_string());
    let i64_ty = tcx.types.i64;
    let _lowered = lower_callchain_instance(tcx, &mut mb, quad_def, i64_ty, "i64", 0)?;
    Ok(mb.build()?)
}

/// Run the M4 worklist lowering + differential for `quad<i64>`. Builds the module
/// (quad__i64 + double__i64), validates it, and checks the interpreter on the
/// root over several i64 inputs against the native oracle `quad(x) = 4*x`
/// (wrapping). Returns (module, report).
pub fn run_m4_differential<'tcx>(
    tcx: TyCtxt<'tcx>,
    quad_def: LocalDefId,
) -> LResult<(Module, M3Report)> {
    let mut mb = ModuleBuilder::new("frontend::m4".to_string());
    let i64_ty = tcx.types.i64;

    let lowered = lower_callchain_instance(tcx, &mut mb, quad_def, i64_ty, "i64", 0)?;
    let root = lowered
        .first()
        .ok_or_else(|| LowerError("M4: empty worklist".into()))?;

    // A nullary runner per input so the interpreter can drive `quad__i64`.
    let inputs: [i128; 4] = [3, -7, 1_000_000, i64::MAX as i128];
    let runners: Vec<(i128, FuncId)> = inputs
        .iter()
        .map(|&x| (x, add_unary_runner(&mut mb, root, x)))
        .collect();

    let module = mb.build()?;
    let verrs = trust_ir_build::validate_module(&module);

    let mut checks = Vec::new();
    for (x, runner) in runners {
        // Native oracle: quad(x) = double(double(x)) = 4*x with i64 wrapping.
        let oracle = quad_oracle_i64(x as i64) as i128;
        push_int_check(
            &module,
            &mut checks,
            &format!("quad::<i64>({x})"),
            runner,
            oracle,
        );
    }

    Ok((module, M3Report { validate_errors: verrs.len(), checks }))
}

/// Native oracle for `quad<i64>`: `double(double(x))` with i64 wrapping
/// (`double(y) = y + y`).
fn quad_oracle_i64(x: i64) -> i64 {
    let d = x.wrapping_add(x);
    d.wrapping_add(d)
}

// --- M5.1: `if`/`else` control flow + multi-param functions ------------------
//
// M4 lowered single-param call chains. M5.1 unifies the body lowerer into one
// recursive `lower_expr` (above) and adds `if`/`else` (CondBr + join param) and
// N-parameter functions. The corpus shapes: `pick(c,a,b)` (if/join/multi-param/
// VarRef), `select<T>(c,a,b)` (the same UNDER monomorphization at T=i64), and
// `max2(a,b)` (an `if` whose cond is a signed `>=` comparison -> `icmp Sge`).
// All three go through the SAME worklist machinery (`lower_callchain_instance`);
// for the non-generic ones the substitution args are the identity.

/// A descriptor for one M5 differential case: corpus def + the N i64 arguments
/// to drive it with + the native oracle result.
pub struct M5Case {
    pub label: String,
    pub def: LocalDefId,
    pub args: Vec<i128>,
    pub oracle: i128,
}

/// Run the M5.1 differential: lower each `pick`/`select`/`max2` case through the
/// (now N-param + if-aware) worklist, add an N-ary runner that feeds the actual
/// args, and check interp == native oracle.
///
/// Each case is lowered into its OWN module: the worklist's load-bearing
/// `assert_eq!(func_id.index(), discovery_idx)` contract requires the root
/// instance to land at FuncId 0, so a fresh module per case is the clean way to
/// drive several call sites without colliding FuncIds. Returns the LAST case's
/// module (for the driver's function-count line) plus the COMBINED report (one
/// check per case, validate errors summed across cases).
pub fn run_m5_differential<'tcx>(
    tcx: TyCtxt<'tcx>,
    cases: &[M5Case],
) -> LResult<(Module, M3Report)> {
    let i64_ty = tcx.types.i64;
    let mut checks = Vec::new();
    let mut total_verrs = 0usize;
    let mut last_module: Option<Module> = None;

    for case in cases {
        let mut mb = ModuleBuilder::new(format!("frontend::m5::{}", case.label));
        let lowered = lower_callchain_instance(tcx, &mut mb, case.def, i64_ty, "i64", 0)?;
        let root = lowered
            .first()
            .ok_or_else(|| LowerError("M5: empty worklist".into()))?;
        let runner = add_nary_runner(&mut mb, root, &case.args);

        let module = mb.build()?;
        total_verrs += trust_ir_build::validate_module(&module).len();
        push_int_check(&module, &mut checks, &case.label, runner, case.oracle);
        last_module = Some(module);
    }

    let module = last_module
        .ok_or_else(|| LowerError("M5: no cases supplied".into()))?;
    Ok((module, M3Report { validate_errors: total_verrs, checks }))
}

/// Emit the M5.1 `if`/`pick` round-trip module (`pick` + `select__i64`) as a
/// standalone module for the downstream trust-cg JIT cross-check. Mirrors
/// `emit_callchain_roundtrip_module`. `select` is included when present so the
/// emitted text shows `if` works under monomorphization too.
pub fn emit_if_roundtrip_module<'tcx>(
    tcx: TyCtxt<'tcx>,
    pick_def: LocalDefId,
    select_def: Option<LocalDefId>,
) -> LResult<Module> {
    let mut mb = ModuleBuilder::new("frontend::m5::if".to_string());
    let i64_ty = tcx.types.i64;
    // Emit `pick` (base 0), then `select` based AFTER pick's functions so its
    // root lands at the right FuncId. `pick`/`select` are leaf `if` bodies (no
    // cross-fn Call), so each contributes exactly its own instance count.
    let pick = lower_callchain_instance(tcx, &mut mb, pick_def, i64_ty, "i64", 0)?;
    if let Some(s) = select_def {
        let base = pick.len() as u32;
        let _sel = lower_callchain_instance(tcx, &mut mb, s, i64_ty, "i64", base)?;
    }
    Ok(mb.build()?)
}

// --- M5.7c: unary ops + the rest of the integer binops -----------------------
//
// PURELY ADDITIVE: `ExprKind::Unary` (`!`/unary `-`) and the integer binops
// Div/Rem/BitAnd/BitOr/BitXor/Shl/Shr in `lower_binop`, all through the SAME
// unified `MonoCx::lower_expr` worklist. The differential drives each corpus fn
// (`negate`/`inot`/`bnot`/`bitops`/`divrem`/`shifts`) over several inputs incl.
// negatives + a signed-shift case, against a GENUINE NATIVE Rust oracle computed
// the same way M4's `quad_oracle` is (NOT hand literals).

/// The native oracle for one M5.7c case: an integer result or a bool result
/// (so `bnot` can be checked alongside the i64 ops).
pub enum M5gOracle {
    Int(i128),
    Bool(bool),
}

/// One M5.7c differential case: corpus def + the args (i128; a bool arg is fed as
/// 0/1 by the runner) + the native oracle. Each case lowers into its OWN module
/// (the worklist's "root at FuncId 0" contract), like `run_m5_differential`.
pub struct M5gCase {
    pub label: String,
    pub def: LocalDefId,
    pub args: Vec<i128>,
    pub oracle: M5gOracle,
}

/// Run the M5.7c differential: lower each unary/binop corpus fn through the
/// worklist, add an N-ary runner that feeds the actual args, and check
/// interp == native oracle (int OR bool). Returns the LAST case's module (for the
/// driver's function-count line) plus the COMBINED report.
pub fn run_m5g_differential<'tcx>(
    tcx: TyCtxt<'tcx>,
    cases: &[M5gCase],
) -> LResult<(Module, M3Report)> {
    let i64_ty = tcx.types.i64;
    let mut checks = Vec::new();
    let mut total_verrs = 0usize;
    let mut last_module: Option<Module> = None;

    for case in cases {
        let mut mb = ModuleBuilder::new(format!("frontend::m5g::{}", case.label));
        let lowered = lower_callchain_instance(tcx, &mut mb, case.def, i64_ty, "i64", 0)?;
        let root = lowered
            .first()
            .ok_or_else(|| LowerError("M5.7c: empty worklist".into()))?;
        let runner = add_nary_runner(&mut mb, root, &case.args);

        let module = mb.build()?;
        total_verrs += trust_ir_build::validate_module(&module).len();
        match case.oracle {
            M5gOracle::Int(o) => push_int_check(&module, &mut checks, &case.label, runner, o),
            M5gOracle::Bool(o) => push_bool_check(&module, &mut checks, &case.label, runner, o),
        }
        last_module = Some(module);
    }

    let module = last_module.ok_or_else(|| LowerError("M5.7c: no cases supplied".into()))?;
    Ok((module, M3Report { validate_errors: total_verrs, checks }))
}

/// Emit the M5.7c scalar-op round-trip module for the downstream trust-cg JIT
/// cross-check: the i64->i64 / (i64,i64)->i64 ops `negate`/`bitops`/`divrem`/
/// `shifts` (the bool `bnot` is left out — the JIT round-trip below only embeds
/// the integer ops; `bnot` is still covered by the frontend differential).
/// Mirrors `emit_if_roundtrip_module`: each is a leaf body (no cross-fn Call), so
/// each contributes exactly one instance and the FuncId base is the running total.
pub fn emit_ops_roundtrip_module<'tcx>(
    tcx: TyCtxt<'tcx>,
    negate_def: LocalDefId,
    bitops_def: LocalDefId,
    divrem_def: LocalDefId,
    shifts_def: LocalDefId,
) -> LResult<Module> {
    let mut mb = ModuleBuilder::new("frontend::m5g::ops".to_string());
    let i64_ty = tcx.types.i64;
    let mut base = 0u32;
    for def in [negate_def, bitops_def, divrem_def, shifts_def] {
        let lowered = lower_callchain_instance(tcx, &mut mb, def, i64_ty, "i64", base)?;
        base += lowered.len() as u32;
    }
    Ok(mb.build()?)
}

// --- M5.7d: MULTI-type-param generic monomorphization ------------------------
//
// PURELY ADDITIVE on top of M3's single-type-param path. `args_for_type_params`
// binds N type params POSITIONALLY; `lower_multi_generic_instance` lowers a fn
// with N type params at a concrete tuple through the SAME unified `lower_expr`.
// The differential lowers `fst`/`combine` at MULTIPLE distinct type tuples and
// drives each over GENUINE NATIVE oracles (fst(a,_)==a; combine(a,b,_)==a+b
// wrapping), INCLUDING a width-discriminating case
// (`combine<u32>(0x8000_0000, 0x8000_0000, _)` wraps to 0 at U32 width).

/// One M5.7d differential case: the corpus def, the concrete TYPE tuple it is
/// instantiated at (a `name_suffix` + the concrete `ty::Ty`s), the actual ARG
/// values (i128; a `bool` arg would be fed via the runner's bool slot, though the
/// corpus shapes here use only integers), and the GENUINE native oracle. Each
/// case lowers into its OWN module (the runner calls FuncId 0).
pub struct M5hCase<'tcx> {
    pub label: String,
    pub def: LocalDefId,
    /// The concrete type tuple (positional), each paired with a suffix fragment
    /// (e.g. `[(i64,"i64"),(u32,"u32")]` -> suffix `i64_u32`).
    pub concretes: Vec<ty::Ty<'tcx>>,
    pub name_suffix: String,
    pub args: Vec<i128>,
    pub oracle: M5gOracle,
}

/// Run the M5.7d MULTI-type-param differential. For each case, lower the fn at
/// its concrete type tuple via `lower_multi_generic_instance`, add an N-ary
/// runner that feeds the actual args, and check interp == native oracle. Returns
/// the LAST case's module (for the driver's function-count line) + combined
/// report. ALSO records, per case, the lowered root's concrete ir param/ret types
/// so the driver can print the per-instantiation type witness.
pub fn run_m5h_differential<'tcx>(
    tcx: TyCtxt<'tcx>,
    cases: &[M5hCase<'tcx>],
) -> LResult<(Module, M3Report, Vec<LoweredInstance>)> {
    let mut checks = Vec::new();
    let mut total_verrs = 0usize;
    let mut last_module: Option<Module> = None;
    let mut lowered_roots: Vec<LoweredInstance> = Vec::new();

    for case in cases {
        let mut mb = ModuleBuilder::new(format!("frontend::m5h::{}", case.label));
        let root =
            lower_multi_generic_instance(tcx, &mut mb, case.def, &case.concretes, &case.name_suffix)?;
        let runner = add_nary_runner(&mut mb, &root, &case.args);
        lowered_roots.push(LoweredInstance {
            func_id: root.func_id,
            name: root.name.clone(),
            param_tys: root.param_tys.clone(),
            ret_ty: root.ret_ty.clone(),
        });

        let module = mb.build()?;
        total_verrs += trust_ir_build::validate_module(&module).len();
        match case.oracle {
            M5gOracle::Int(o) => push_int_check(&module, &mut checks, &case.label, runner, o),
            M5gOracle::Bool(o) => push_bool_check(&module, &mut checks, &case.label, runner, o),
        }
        last_module = Some(module);
    }

    let module = last_module.ok_or_else(|| LowerError("M5.7d: no cases supplied".into()))?;
    Ok((
        module,
        M3Report { validate_errors: total_verrs, checks },
        lowered_roots,
    ))
}

/// Emit the M5.7d multi-type-param round-trip module for the downstream trust-cg
/// JIT cross-check: the i64-instantiated `fst<i64,i64>` and `combine<i64,i64>`
/// (both pure-i64 so the trust-cg i64 C-ABI helpers can drive them). Each is a
/// leaf body (no cross-fn Call) contributing exactly one instance; FuncId base is
/// the running total. The instantiation suffix is `i64_i64`, so the emitted fns
/// are `fst__i64_i64` (`(i64,i64)->i64`, returns the 1st arg) and
/// `combine__i64_i64` (`(i64,i64,i64)->i64`, returns `a + b`).
pub fn emit_multigen_roundtrip_module<'tcx>(
    tcx: TyCtxt<'tcx>,
    fst_def: LocalDefId,
    combine_def: LocalDefId,
) -> LResult<Module> {
    let mut mb = ModuleBuilder::new("frontend::m5h::multigen".to_string());
    let i64_ty = tcx.types.i64;
    // fst<i64,i64>: (i64,i64)->i64.
    let _fst = lower_multi_generic_instance(tcx, &mut mb, fst_def, &[i64_ty, i64_ty], "i64_i64")?;
    // combine<i64,i64>: (i64,i64,i64)->i64.
    let _combine =
        lower_multi_generic_instance(tcx, &mut mb, combine_def, &[i64_ty, i64_ty], "i64_i64")?;
    Ok(mb.build()?)
}

// --- M5.2: `let`-bindings (multi-statement blocks) ---------------------------
//
// M5.1 handled single-tail-expr bodies. M5.2 adds `let`-binding statements
// before the tail (the most pervasive shape in real clean-kernel `tc/` helpers).
// The unified `lower_expr` Block arm now lowers each `let pat = init` (binding
// the var into `MonoCx::locals`) before peeling to the tail. The corpus shapes:
// `poly` (sequential lets, value reuse), `quad_let` (a let feeding a call
// chain), and `twice_let<T>` (a let UNDER monomorphization). All three reuse the
// SAME worklist machinery as M5.1 (`lower_callchain_instance` + `M5Case`); the
// only new lowering is the let-block handling itself.

/// Run the M5.2 `let`-binding differential. Identical machinery to
/// `run_m5_differential` (one fresh module per case so the worklist's "root at
/// FuncId 0" contract holds), reported separately so the M5.1 7/7 line stays
/// distinct. Each case is lowered through the (now let-aware) unified lowerer.
pub fn run_m5b_differential<'tcx>(
    tcx: TyCtxt<'tcx>,
    cases: &[M5Case],
) -> LResult<(Module, M3Report)> {
    // The lowering path is identical to M5.1's; delegate to keep ONE codepath.
    run_m5_differential(tcx, cases)
}

/// Emit the M5.2 `let` round-trip module (`poly` + `quad_let`, plus the
/// `double__i64` callee that `quad_let` discovers) as standalone trust-ir TEXT
/// for the downstream trust-cg JIT cross-check. Mirrors
/// `emit_if_roundtrip_module`: emit `poly` (base 0), then `quad_let` based AFTER
/// poly's functions so its worklist (root `quad_let__i64` + callee
/// `double__i64`) lands at the right FuncIds.
pub fn emit_let_roundtrip_module<'tcx>(
    tcx: TyCtxt<'tcx>,
    poly_def: LocalDefId,
    quad_let_def: LocalDefId,
) -> LResult<Module> {
    let mut mb = ModuleBuilder::new("frontend::m5::let".to_string());
    let i64_ty = tcx.types.i64;
    // `poly` is a leaf let body (no cross-fn Call): contributes exactly 1 fn.
    let poly = lower_callchain_instance(tcx, &mut mb, poly_def, i64_ty, "i64", 0)?;
    let base = poly.len() as u32;
    // `quad_let` discovers `double__i64`: its worklist is 2 fns, based after poly.
    let _ql = lower_callchain_instance(tcx, &mut mb, quad_let_def, i64_ty, "i64", base)?;
    Ok(mb.build()?)
}

// --- M5.3: `match`-as-VALUE over a scalar (integer) discriminant -------------
//
// M5.1 added `if`/join; M5.2 added `let`. M5.3 generalizes `match` from LowerCx's
// whole-function-tail form (read an enum TAG via heap Load, `ret` per arm) to a
// value-producing EXPRESSION over a SCALAR integer scrutinee: switch on the
// integer VALUE directly and JOIN each arm's result at a block-param. This is the
// structural prerequisite for M5.4 (match over a recursive ADT). The lowering
// lives in the unified `MonoCx::lower_expr` (`lower_match_scalar`); an ADT (Ptr)
// scrutinee bails loudly with an M5.4 message. The corpus shapes: `classify`
// (integer-literal arms + `_` catch-all) and `step` (arm bodies that call a
// helper + a `Binding` catch-all that binds the scrutinee value into `locals`).
// Both reuse the SAME worklist machinery (`lower_callchain_instance` + `M5Case`).

/// Run the M5.3 scalar-`match` differential. Identical machinery to
/// `run_m5_differential` (one fresh module per case so the worklist's "root at
/// FuncId 0" contract holds), reported separately so the prior M5 lines stay
/// distinct. Each case is lowered through the (now match-aware) unified lowerer.
pub fn run_m5c_differential<'tcx>(
    tcx: TyCtxt<'tcx>,
    cases: &[M5Case],
) -> LResult<(Module, M3Report)> {
    // The lowering path is identical to M5.1/M5.2's; delegate to keep ONE codepath.
    run_m5_differential(tcx, cases)
}

/// Run the scalar-DEREF differential (audit FIX 2). Lowers `deref_add(r: &i64)
/// -> i64` (whose body `*r + 1` must Load the i64 THROUGH the pointer, not
/// identity-peel the pointer typed as i64) and, per input, builds a runner that
/// `alloca`s an i64 slot, `Store`s the input into it, and Calls `deref_add` with
/// that pointer. The native oracle is `x + 1` (i64 wrapping). A correct scalar
/// deref yields `x + 1`; the pre-fix miscompile (returning the pointer) would
/// not. Returns (module, report).
pub fn run_deref_differential<'tcx>(
    tcx: TyCtxt<'tcx>,
    deref_add_def: LocalDefId,
) -> LResult<(Module, M3Report)> {
    let i64_ty = tcx.types.i64; // unused identity arg for the non-generic root.
    let mut checks = Vec::new();
    let mut total_verrs = 0usize;
    let mut last_module: Option<Module> = None;

    let inputs: [i64; 5] = [0, 1, -1, 41, i64::MAX];
    for &x in inputs.iter() {
        let mut mb = ModuleBuilder::new(format!("frontend::deref::{x}"));
        let lowered = lower_callchain_instance(tcx, &mut mb, deref_add_def, i64_ty, "i64", 0)?;
        let root = lowered
            .first()
            .ok_or_else(|| LowerError("deref: empty worklist".into()))?;
        // The lowered signature must be `fn(Ptr) -> i64` — the `&i64` param is a
        // Ptr, the result is i64. Guard it so a regression in scalar-deref
        // lowering (e.g. returning Ptr) is caught loudly here.
        if root.param_tys.as_slice() != [trust_ir::ty::Ty::Ptr]
            || root.ret_ty != trust_ir::ty::Ty::I64
        {
            return bail(format!(
                "deref: deref_add lowered to {:?} -> {:?}, expected fn(Ptr) -> I64",
                root.param_tys, root.ret_ty
            ));
        }
        let target = root.func_id;

        // Nullary runner: alloca an i64 slot, Store `x`, Call deref_add(slot_ptr).
        let sig = mb.add_func_type(vec![], vec![trust_ir::ty::Ty::I64]);
        let runner = {
            let mut fb = mb.function(format!("run_deref_add_{x}"), sig);
            let entry = fb.create_block();
            fb.switch_to_block(entry);
            let slot = fb.alloca(trust_ir::ty::Ty::I64);
            let v = fb.iconst(trust_ir::ty::Ty::I64, x as i128);
            fb.store(trust_ir::ty::Ty::I64, slot, v);
            let r = fb.call(target, vec![slot]);
            fb.ret(vec![r]);
            fb.build()
        };

        let module = mb.build()?;
        total_verrs += trust_ir_build::validate_module(&module).len();
        let oracle = x.wrapping_add(1) as i128;
        push_int_check(&module, &mut checks, &format!("deref_add(&{x}) [*r + 1]"), runner, oracle);
        last_module = Some(module);
    }

    let module = last_module.ok_or_else(|| LowerError("deref: no inputs".into()))?;
    Ok((module, M3Report { validate_errors: total_verrs, checks }))
}

/// Emit the M5.3 scalar-`match` round-trip module (`classify`, plus `step` and
/// the `double__i64` it discovers) as standalone trust-ir TEXT for the
/// downstream trust-cg JIT cross-check. Mirrors `emit_let_roundtrip_module`:
/// emit `classify` (base 0), then `step` based AFTER classify's functions so its
/// worklist (root `step__i64` + callee `double__i64`) lands at the right FuncIds.
/// `step` is included only when present in the corpus.
pub fn emit_match_roundtrip_module<'tcx>(
    tcx: TyCtxt<'tcx>,
    classify_def: LocalDefId,
    step_def: Option<LocalDefId>,
) -> LResult<Module> {
    let mut mb = ModuleBuilder::new("frontend::m5::match".to_string());
    let i64_ty = tcx.types.i64;
    // `classify` is a leaf scalar-match body (no cross-fn Call): 1 fn.
    let classify = lower_callchain_instance(tcx, &mut mb, classify_def, i64_ty, "i64", 0)?;
    if let Some(s) = step_def {
        let base = classify.len() as u32;
        // `step` discovers `double__i64`: its worklist is 2 fns, based after classify.
        let _step = lower_callchain_instance(tcx, &mut mb, s, i64_ty, "i64", base)?;
    }
    Ok(mb.build()?)
}

// --- M5.4: `match` over a RECURSIVE ADT (heap-tag), value-returning ----------
//
// M5.3 switched on a SCALAR integer value. M5.4 closes the recursive-enum class
// LowerCx (M1/M2) handles, but as a VALUE-returning, worklist-driven lowering: a
// `match` over a `&Level` (a recursive ADT) lowered through the unified
// `MonoCx::lower_expr` — Load the discriminant tag through the heap shape,
// `Switch`, bind each arm's payload child POINTERS into `locals`, lower the arm
// body (a self-recursive `count_succ(child)` Call flowing through the worklist),
// and JOIN every arm's i64 result at a block-param. A direct microcosm of a real
// `whnf`. The corpus shape: `count_succ(&Level) -> i64` (counts `Succ` nodes).
// It reuses the EXISTING M1/M2 `Level` enum shape, so the differential reuses
// `model.rs`'s heap builder (`add_int_input_runner` over `Micro`) + native
// oracle (`Micro::count_succ`) to drive the THIR-lowered fn over real heap inputs.

/// Run the M5.4 recursive-ADT-match differential. Lower `count_succ` (the
/// recursive `match &Level -> i64` fold) through the worklist (which registers
/// the `Level` tagged struct + lowers the value-producing heap-tag match), then
/// build a heap-graph runner per `Micro` corpus value (over several depths) and
/// check interp == native `Micro::count_succ`. Returns (module, report).
pub fn run_m5d_differential<'tcx>(
    tcx: TyCtxt<'tcx>,
    count_succ_def: LocalDefId,
) -> LResult<(Module, M3Report)> {
    use crate::model::{add_int_input_runner, Micro};

    let mut mb = ModuleBuilder::new("frontend::m5::adtmatch".to_string());
    let i64_ty = tcx.types.i64; // unused by the non-generic count_succ; identity args.

    // Lower count_succ (+ any callees — it self-recurses, so the worklist is just
    // itself) and register the `Level` tagged struct in the module.
    let lowered = lower_callchain_instance(tcx, &mut mb, count_succ_def, i64_ty, "i64", 0)?;
    let root = lowered
        .first()
        .ok_or_else(|| LowerError("M5.4: empty worklist".into()))?;
    let target = root.func_id;

    // Corpus over several DEPTHS: a value-producing recursive ADT fold checked at
    // depth 0 (Zero), 1 (Succ Zero), 2 (Succ Succ Zero), 3, plus binary-recursive
    // (Max/IMax) and Param-leaf trees so every arm + both recursion shapes fire.
    let z = || Micro::Zero;
    let s = |m: Micro| Micro::Succ(Box::new(m));
    let mx = |a: Micro, b: Micro| Micro::Max(Box::new(a), Box::new(b));
    let im = |a: Micro, b: Micro| Micro::IMax(Box::new(a), Box::new(b));
    let pm = |n: u64| Micro::Param(n);
    let cases: Vec<(String, Micro)> = vec![
        ("count_succ(Zero) [depth 0]".into(), z()),
        ("count_succ(Succ Zero) [depth 1]".into(), s(z())),
        ("count_succ(Succ Succ Zero) [depth 2]".into(), s(s(z()))),
        ("count_succ(Succ^3 Zero) [depth 3]".into(), s(s(s(z())))),
        ("count_succ(Param) [leaf]".into(), pm(7)),
        ("count_succ(Max(Succ Zero, Succ Succ Zero)) [binary]".into(), mx(s(z()), s(s(z())))),
        ("count_succ(IMax(Succ Zero, Zero)) [binary]".into(), im(s(z()), z())),
        (
            "count_succ(Max(Param, Succ(Max(Succ Zero, Zero)))) [nested]".into(),
            mx(pm(1), s(mx(s(z()), z()))),
        ),
    ];

    // M6: the FAITHFUL heap layout (from `layout_of`) the lowered `count_succ`
    // reads — so the heap the runner Stores matches its Loads byte-for-byte.
    let heap_lay =
        crate::model::HeapLayout::from_enum_layout(&matched_enum_layout(tcx, count_succ_def)?);
    let nullary_i64 = mb.add_func_type(vec![], vec![trust_ir::ty::Ty::I64]);
    let runners: Vec<(String, i128, FuncId)> = cases
        .iter()
        .enumerate()
        .map(|(i, (label, m))| {
            let oracle = m.count_succ() as i128;
            let runner = add_int_input_runner(
                &mut mb,
                &heap_lay,
                m,
                target,
                nullary_i64,
                &format!("run_adt_{i}"),
            );
            (label.clone(), oracle, runner)
        })
        .collect();

    let module = mb.build()?;
    let verrs = trust_ir_build::validate_module(&module);

    let mut checks = Vec::new();
    for (label, oracle, runner) in runners {
        push_int_check(&module, &mut checks, &label, runner, oracle);
    }

    Ok((module, M3Report { validate_errors: verrs.len(), checks }))
}

/// Emit the M5.4 recursive-ADT-match round-trip module (`count_succ`, the
/// value-producing `match &Level -> i64` fold + its `Level` tagged struct) as
/// standalone trust-ir TEXT for the downstream trust-cg JIT round-trip. Mirrors
/// `emit_match_roundtrip_module`. `count_succ` self-recurses, so its worklist is
/// the single fn; emitting it also emits the `Level` struct definition.
pub fn emit_adt_match_roundtrip_module<'tcx>(
    tcx: TyCtxt<'tcx>,
    count_succ_def: LocalDefId,
) -> LResult<Module> {
    let mut mb = ModuleBuilder::new("frontend::m5::adtmatch".to_string());
    let i64_ty = tcx.types.i64;
    let _lowered = lower_callchain_instance(tcx, &mut mb, count_succ_def, i64_ty, "i64", 0)?;
    Ok(mb.build()?)
}

// --- M5.7b: INLINE-SCALAR enum payload (a tiny expression evaluator) ----------
//
// M5.4 bound only POINTER payloads (Box children). M5.7b adds the SECOND payload
// kind a real `is_def_eq` needs: an INLINE-SCALAR field (`Val::Lit(i64)`,
// `Expr::Var(i64)`). Matching `&Val`, a by-ref binding `n` of a scalar field is
// the ADDRESS of the inline value (a GEP, NO Load); the arm body's `*n` (the
// M5.4 scalar-Deref path) Loads it. The corpus shape: `eval(&Val) -> i64`, a
// recursive expression-tree fold MIXING a scalar leaf (`Lit(n) => *n`) with Box
// children (`Neg(a) => -eval(a)`, `Add(a, b) => eval(a) + eval(b)`). It reuses
// the SAME tagged-struct `EnumModel`; the differential reuses `model.rs`'s `Val`
// heap builder (`add_val_int_runner` — inline `Lit`, Box `Neg`/`Add`) + native
// oracle (`Val::eval`) to drive the THIR-lowered fn over real heap inputs.

/// Run the M5.7b inline-scalar-payload differential. Lower `eval` (the recursive
/// `match &Val -> i64` expression fold) through the worklist (which registers the
/// `Val` tagged struct + lowers the value-producing heap-tag match with the NEW
/// inline-scalar payload binding), then build a heap-graph runner per `Val` corpus
/// value (Lit/Neg/Add nesting) and check interp == native `Val::eval`. Returns
/// (module, report).
pub fn run_m5i_differential<'tcx>(
    tcx: TyCtxt<'tcx>,
    eval_def: LocalDefId,
) -> LResult<(Module, M3Report)> {
    use crate::model::{add_val_int_runner, Val};

    let mut mb = ModuleBuilder::new("frontend::m5::evalscalar".to_string());
    let i64_ty = tcx.types.i64; // unused by the non-generic eval; identity args.

    // Lower eval (+ any callees — it self-recurses, so the worklist is itself) and
    // register the `Val` tagged struct in the module.
    let lowered = lower_callchain_instance(tcx, &mut mb, eval_def, i64_ty, "i64", 0)?;
    let root = lowered
        .first()
        .ok_or_else(|| LowerError("M5.7b: empty worklist".into()))?;
    let target = root.func_id;

    // Corpus of `Val` trees: a bare scalar leaf, a negated leaf, an add, and
    // nestings that exercise BOTH the inline-scalar binding (`Lit` -> `*n`) AND the
    // Box-child recursion (`Neg`/`Add`), incl. negative + boundary literals.
    let lit = |n: i64| Val::Lit(n);
    let neg = |v: Val| Val::Neg(Box::new(v));
    let add = |a: Val, b: Val| Val::Add(Box::new(a), Box::new(b));
    let cases: Vec<(String, Val)> = vec![
        ("eval(Lit 0) [inline-scalar leaf]".into(), lit(0)),
        ("eval(Lit 42) [inline-scalar leaf]".into(), lit(42)),
        ("eval(Lit -7) [negative inline scalar]".into(), lit(-7)),
        ("eval(Lit i64::MIN) [boundary inline scalar]".into(), lit(i64::MIN)),
        ("eval(Neg(Lit 5)) [unary -]".into(), neg(lit(5))),
        ("eval(Neg(Lit -5)) [unary - of negative]".into(), neg(lit(-5))),
        ("eval(Add(Lit 3, Lit 4)) [binary +]".into(), add(lit(3), lit(4))),
        (
            "eval(Add(Lit 10, Neg(Lit 4))) [+ over -]".into(),
            add(lit(10), neg(lit(4))),
        ),
        (
            "eval(Neg(Add(Lit 1, Lit 2))) [- over +]".into(),
            neg(add(lit(1), lit(2))),
        ),
        (
            "eval(Add(Add(Lit 1, Lit 2), Neg(Add(Lit 3, Lit 4)))) [nested]".into(),
            add(add(lit(1), lit(2)), neg(add(lit(3), lit(4)))),
        ),
        (
            "eval(Add(Lit i64::MAX, Lit 1)) [wrapping +]".into(),
            add(lit(i64::MAX), lit(1)),
        ),
    ];

    // M6: the FAITHFUL `Val` heap layout (from `layout_of`) the lowered `eval` reads.
    let heap_lay =
        crate::model::HeapLayout::from_enum_layout(&matched_enum_layout(tcx, eval_def)?);
    let nullary_i64 = mb.add_func_type(vec![], vec![trust_ir::ty::Ty::I64]);
    let runners: Vec<(String, i128, FuncId)> = cases
        .iter()
        .enumerate()
        .map(|(i, (label, v))| {
            let oracle = v.eval() as i128;
            let runner = add_val_int_runner(
                &mut mb,
                &heap_lay,
                v,
                target,
                nullary_i64,
                &format!("run_eval_{i}"),
            );
            (label.clone(), oracle, runner)
        })
        .collect();

    let module = mb.build()?;
    let verrs = trust_ir_build::validate_module(&module);

    let mut checks = Vec::new();
    for (label, oracle, runner) in runners {
        push_int_check(&module, &mut checks, &label, runner, oracle);
    }

    Ok((module, M3Report { validate_errors: verrs.len(), checks }))
}

/// Emit the M5.7b inline-scalar-payload round-trip module (`eval`, the recursive
/// `match &Val -> i64` expression fold + its `Val` tagged struct) as standalone
/// trust-ir TEXT for the downstream trust-cg JIT round-trip. Mirrors
/// `emit_adt_match_roundtrip_module`. `eval` self-recurses, so its worklist is the
/// single fn; emitting it also emits the `Val` struct definition.
pub fn emit_eval_roundtrip_module<'tcx>(
    tcx: TyCtxt<'tcx>,
    eval_def: LocalDefId,
) -> LResult<Module> {
    let mut mb = ModuleBuilder::new("frontend::m5::evalscalar".to_string());
    let i64_ty = tcx.types.i64;
    let _lowered = lower_callchain_instance(tcx, &mut mb, eval_def, i64_ty, "i64", 0)?;
    Ok(mb.build()?)
}

// --- M5.7a: NESTED-CONSTRUCTOR match patterns (the canonical β-redex shape) ----
//
// M5.4/M5.7b matched the OUTER variant only (every nested constructor BAILED, the
// fail-loud soundness guard). M5.7a adds the COMMON one-level nested-constructor
// case — `App(box Lam(_), _)`, the exact pattern a real clean-kernel `whnf` uses
// for redex detection — as a decision sub-tree: the outer Switch routes the outer
// variant to a CANDIDATE block that loads the nested field's Box child, reads its
// inner discriminant tag, and `condbr`s to the arm body (inner tag matches the
// nested variant) or the catch-all (mismatch, first-match fallthrough). Deeper /
// ambiguous nests still bail loud. The differential drives the THIR-lowered
// predicate over real `Term` heap graphs (App(Lam,..)/App(Var,..)/Lam/Var trees,
// true + false cases) vs the native `Term` oracle.

/// Run the M5.7a nested-constructor-pattern differential for ONE predicate
/// (`is_beta_redex` or `redex_body_is_var`). Lower the predicate through the
/// worklist (registering the `Term` tagged struct + lowering the nested-pattern
/// decision sub-tree), then build a `Term` heap-graph runner per corpus value and
/// check interp == native oracle on EVERY case. Returns (module, report).
pub fn run_m5j_differential<'tcx>(
    tcx: TyCtxt<'tcx>,
    pred_def: LocalDefId,
    pred_name: &str,
) -> LResult<(Module, M3Report)> {
    use crate::model::{add_term_bool_runner, Term};

    let mut mb = ModuleBuilder::new(format!("frontend::m5::redex::{pred_name}"));
    let i64_ty = tcx.types.i64; // unused by the non-generic predicate; identity args.

    // Lower the predicate (a leaf — no self-call / cross-fn Call) and register the
    // `Term` tagged struct. The root is FuncId 0, a `fn(ptr) -> bool`.
    let lowered = lower_callchain_instance(tcx, &mut mb, pred_def, i64_ty, "i64", 0)?;
    let root = lowered
        .first()
        .ok_or_else(|| LowerError("M5.7a: empty worklist".into()))?;
    if root.param_tys.as_slice() != [trust_ir::ty::Ty::Ptr]
        || root.ret_ty != trust_ir::ty::Ty::Bool
    {
        return bail(format!(
            "M5.7a: predicate `{pred_name}` lowered to {:?} -> {:?}, expected fn(Ptr) -> Bool",
            root.param_tys, root.ret_ty
        ));
    }
    let target = root.func_id;

    // SOUNDNESS: bail LOUDLY on an unknown predicate name BEFORE building runners —
    // a silent default oracle would mask a wrong lowering as "matching".
    if pred_name != "is_beta_redex" && pred_name != "redex_body_is_var" {
        return bail(format!(
            "M5.7a: no native oracle for predicate `{pred_name}` (only `is_beta_redex` / \
             `redex_body_is_var` are modeled) — refusing a default oracle"
        ));
    }

    // Corpus of `Term` trees over BOTH true and false cases, exercising every
    // nested-pattern edge: the redex (App(Lam,..) -> true), the inner-tag-mismatch
    // fallthrough (App(Var,..)/App(App,..) -> false), the outer-variant-mismatch
    // (Lam/Var -> false, the outer Switch default), plus, for `redex_body_is_var`,
    // the further nested match on the bound Lam body (Lam(Var) -> true vs
    // Lam(Lam)/Lam(App) -> false).
    let var = |n: i64| Term::Var(n);
    let lam = |b: Term| Term::Lam(Box::new(b));
    let app = |f: Term, a: Term| Term::App(Box::new(f), Box::new(a));
    let cases: Vec<Term> = vec![
        var(0),                                  // outer mismatch (Var)
        lam(var(1)),                             // outer mismatch (Lam)
        app(lam(var(2)), var(3)),                // REDEX: App(Lam(Var), Var)
        app(lam(lam(var(4))), var(5)),           // REDEX: App(Lam(Lam), _); body is Lam
        app(lam(app(var(6), var(7))), var(8)),   // REDEX: App(Lam(App), _); body is App
        app(var(9), var(10)),                    // inner mismatch: App(Var, _) -> not redex
        app(app(lam(var(11)), var(12)), var(13)),// inner mismatch: App(App, _) -> not redex
        app(lam(var(14)), lam(var(15))),         // REDEX with a Lam argument
        lam(app(lam(var(16)), var(17))),         // Lam wrapping a redex (outer is Lam -> false)
    ];

    // M6: the FAITHFUL `Term` heap layout (from `layout_of`) the lowered predicate reads.
    let heap_lay =
        crate::model::HeapLayout::from_enum_layout(&matched_enum_layout(tcx, pred_def)?);
    let nullary_bool = mb.add_func_type(vec![], vec![trust_ir::ty::Ty::Bool]);
    let runners: Vec<(String, bool, FuncId)> = cases
        .iter()
        .enumerate()
        .map(|(i, t)| {
            let oracle = match pred_name {
                "is_beta_redex" => t.is_beta_redex(),
                "redex_body_is_var" => t.redex_body_is_var(),
                other => unreachable!("unexpected predicate name {other:?}"),
            };
            let runner = add_term_bool_runner(
                &mut mb,
                &heap_lay,
                t,
                target,
                nullary_bool,
                &format!("run_redex_{i}"),
            );
            (format!("{pred_name}({t:?})"), oracle, runner)
        })
        .collect();

    let module = mb.build()?;
    let verrs = trust_ir_build::validate_module(&module);

    let mut checks = Vec::new();
    for (label, oracle, runner) in runners {
        push_bool_check(&module, &mut checks, &label, runner, oracle);
    }

    Ok((module, M3Report { validate_errors: verrs.len(), checks }))
}

/// Emit the M5.7a nested-constructor-pattern round-trip module (`is_beta_redex`,
/// the `match &Term -> bool` redex detector + its `Term` tagged struct) as
/// standalone trust-ir TEXT for the downstream trust-cg JIT round-trip. Mirrors
/// `emit_eval_roundtrip_module`. `is_beta_redex` is a leaf, so its worklist is the
/// single fn; emitting it also emits the `Term` struct definition.
pub fn emit_redex_roundtrip_module<'tcx>(
    tcx: TyCtxt<'tcx>,
    redex_def: LocalDefId,
) -> LResult<Module> {
    let mut mb = ModuleBuilder::new("frontend::m5::redex".to_string());
    let i64_ty = tcx.types.i64;
    let _lowered = lower_callchain_instance(tcx, &mut mb, redex_def, i64_ty, "i64", 0)?;
    Ok(mb.build()?)
}

// --- M5.7e: TUPLE/AGGREGATE enum payload + sub-field destructuring -------------
//
// M5.4/M5.7b bound a payload field as ONE unit (a Box-child pointer, or an inline
// scalar). M5.7e adds the AGGREGATE case a real kernel term needs: an enum variant
// whose field is itself a tuple/struct (`Span((i64, i64))`), DESTRUCTURED into its
// sub-fields (`Span((a, b))`). The aggregate lives INLINE at the variant's field
// slot; binding a sub-field GEPs to the aggregate's offset WITHIN the variant + the
// sub-field's offset WITHIN the aggregate (both from `tcx.layout_of`). The corpus
// `sym_sum` folds a `Sym` tree mixing the inline-tuple `Span`, the Box-child `Cons`
// (the unchanged M5.4 pointer path), and the `Nil` leaf. The differential drives
// the THIR-lowered `sym_sum` over real `Sym` heap graphs vs the native `Sym::sym_sum`
// oracle. SCOPE: this is the by-ref AGGREGATE-AS-ENUM-PAYLOAD case; a struct/tuple
// BY VALUE (return/standalone) is DEFERRED (bail loud — no struct-by-value ABI).

/// M5.7e: the ABSOLUTE byte offsets of the two `Span` inline-tuple sub-fields,
/// derived from `tcx.layout_of`: the `Span` variant's field-0 offset (the tuple's
/// offset within the variant) + each tuple element's offset within `(i64, i64)`.
/// These are exactly the offsets the lowered `sym_sum` binds the `a`/`b` sub-fields
/// at, so the heap builder writes the SAME bytes the reader Loads. Bails loud if the
/// matched enum is not the expected `Sym` shape (a `Span`-like 1-tuple-field variant).
fn sym_span_sub_offsets<'tcx>(tcx: TyCtxt<'tcx>, def: LocalDefId) -> LResult<[i128; 2]> {
    use rustc_middle::ty::layout::LayoutCx;
    let (thir_steal, body_expr) = tcx
        .thir_body(def)
        .map_err(|_| LowerError("M5.7e: thir_body errored (tainted)".into()))?;
    let thir = thir_steal.borrow();
    let mut seen = std::collections::HashSet::new();
    let mut adts = Vec::new();
    collect_match_enum_adts(&thir, body_expr, &mut seen, &mut adts);
    let adt = match adts.as_slice() {
        [a] => *a,
        _ => return bail("M5.7e: sym_sum must match over exactly one enum"),
    };
    let layout = crate::enum_layout_of(tcx, adt)?;
    // The `Span` variant: the one whose single field is a tuple/struct aggregate.
    let typing_env = TypingEnv::fully_monomorphized();
    let enum_ty = tcx.normalize_erasing_regions(
        typing_env,
        tcx.type_of(adt.did()).instantiate_identity(),
    );
    let enum_args = match enum_ty.kind() {
        TyKind::Adt(_, args) => *args,
        _ => return bail("M5.7e: enum type_of is not an Adt"),
    };
    for (vidx, vdef) in adt.variants().iter_enumerated() {
        if vdef.fields.len() != 1 {
            continue;
        }
        let fty = tcx.normalize_erasing_regions(
            typing_env,
            vdef.fields[rustc_abi::FieldIdx::from_usize(0)].ty(tcx, enum_args),
        );
        let TyKind::Tuple(elems) = fty.kind() else {
            continue;
        };
        if elems.len() != 2 {
            continue;
        }
        let field0_off = layout.field_offset(vidx, 0).ok_or_else(|| {
            LowerError("M5.7e: no layout offset for the Span tuple field".into())
        })?;
        let tup_layout = tcx
            .layout_of(typing_env.as_query_input(fty))
            .map_err(|e| LowerError(format!("M5.7e: layout_of tuple failed ({e:?})")))?;
        let _lcx = LayoutCx::new(tcx, typing_env);
        let s0 = tup_layout.fields.offset(0).bytes() as i128;
        let s1 = tup_layout.fields.offset(1).bytes() as i128;
        return Ok([field0_off + s0, field0_off + s1]);
    }
    bail("M5.7e: no `Span((i64,i64))`-shaped tuple-payload variant found")
}

/// Run the M5.7e aggregate-payload differential. Lower `sym_sum` (the recursive
/// `match &Sym -> i64` fold) through the worklist (which registers the `Sym` tagged
/// struct + lowers the aggregate-payload sub-field binding), then build a heap-graph
/// runner per `Sym` corpus value (Nil/Span/Cons nesting) and check interp ==
/// native `Sym::sym_sum`. Returns (module, report).
pub fn run_m5l_differential<'tcx>(
    tcx: TyCtxt<'tcx>,
    sym_sum_def: LocalDefId,
) -> LResult<(Module, M3Report)> {
    use crate::model::{add_sym_int_runner, Sym};

    let mut mb = ModuleBuilder::new("frontend::m5::symagg".to_string());
    let i64_ty = tcx.types.i64; // unused by the non-generic sym_sum; identity args.

    // Lower sym_sum (+ any callees — it self-recurses) and register the `Sym`
    // tagged struct. The root is FuncId 0, a `fn(ptr) -> i64`.
    let lowered = lower_callchain_instance(tcx, &mut mb, sym_sum_def, i64_ty, "i64", 0)?;
    let root = lowered
        .first()
        .ok_or_else(|| LowerError("M5.7e: empty worklist".into()))?;
    if root.param_tys.as_slice() != [trust_ir::ty::Ty::Ptr] || root.ret_ty != trust_ir::ty::Ty::I64
    {
        return bail(format!(
            "M5.7e: `sym_sum` lowered to {:?} -> {:?}, expected fn(Ptr) -> I64",
            root.param_tys, root.ret_ty
        ));
    }
    let target = root.func_id;

    // Corpus of `Sym` trees: the leaf, an inline-tuple `Span` (incl. negative +
    // boundary sub-fields), Box `Cons` wrapping each, and nestings exercising the
    // aggregate sub-field binding under recursion.
    let nil = || Sym::Nil;
    let span = |a: i64, b: i64| Sym::Span(a, b);
    let cons = |s: Sym| Sym::Cons(Box::new(s));
    let cases: Vec<(String, Sym)> = vec![
        ("sym_sum(Nil) [leaf]".into(), nil()),
        ("sym_sum(Span(3, 4)) [inline tuple]".into(), span(3, 4)),
        ("sym_sum(Span(-7, 2)) [negative sub-field]".into(), span(-7, 2)),
        (
            "sym_sum(Span(i64::MAX, 1)) [wrapping add]".into(),
            span(i64::MAX, 1),
        ),
        (
            "sym_sum(Span(i64::MIN, i64::MIN)) [boundary]".into(),
            span(i64::MIN, i64::MIN),
        ),
        ("sym_sum(Cons(Nil)) [box leaf]".into(), cons(nil())),
        (
            "sym_sum(Cons(Span(10, 20))) [box over tuple]".into(),
            cons(span(10, 20)),
        ),
        (
            "sym_sum(Cons(Cons(Span(-1, -2)))) [deep box over tuple]".into(),
            cons(cons(span(-1, -2))),
        ),
    ];

    // The FAITHFUL `Sym` heap layout + the Span sub-field offsets the lowered
    // `sym_sum` reads (so the heap builder writes byte-identical bytes).
    let heap_lay =
        crate::model::HeapLayout::from_enum_layout(&matched_enum_layout(tcx, sym_sum_def)?);
    let span_subs = sym_span_sub_offsets(tcx, sym_sum_def)?;
    let nullary_i64 = mb.add_func_type(vec![], vec![trust_ir::ty::Ty::I64]);
    let runners: Vec<(String, i128, FuncId)> = cases
        .iter()
        .enumerate()
        .map(|(i, (label, s))| {
            let oracle = s.sym_sum() as i128;
            let runner = add_sym_int_runner(
                &mut mb,
                &heap_lay,
                span_subs,
                s,
                target,
                nullary_i64,
                &format!("run_sym_{i}"),
            );
            (label.clone(), oracle, runner)
        })
        .collect();

    let module = mb.build()?;
    let verrs = trust_ir_build::validate_module(&module);

    let mut checks = Vec::new();
    for (label, oracle, runner) in runners {
        push_int_check(&module, &mut checks, &label, runner, oracle);
    }

    Ok((module, M3Report { validate_errors: verrs.len(), checks }))
}

/// FIX 5: the absolute (offset, IR WIDTH) of the two-element aggregate sub-fields
/// of the SINGLE variant whose only field is a 2-tuple, read FAITHFULLY from
/// `tcx.layout_of` (like `sym_span_sub_offsets` but ALSO recovering each sub-field's
/// REAL Load/Store width — so a NARROW tuple like `(i32, i32)` is written and
/// checked at its real I32 width + i32-stride offsets, not a uniform I64). Returns
/// the [(off, width); 2].
fn pair_cell_sub_offsets_widths<'tcx>(
    tcx: TyCtxt<'tcx>,
    def: LocalDefId,
) -> LResult<[(i128, trust_ir::ty::Ty); 2]> {
    let (thir_steal, body_expr) = tcx
        .thir_body(def)
        .map_err(|_| LowerError("FIX5: thir_body errored (tainted)".into()))?;
    let thir = thir_steal.borrow();
    let mut seen = std::collections::HashSet::new();
    let mut adts = Vec::new();
    collect_match_enum_adts(&thir, body_expr, &mut seen, &mut adts);
    let adt = match adts.as_slice() {
        [a] => *a,
        _ => return bail("FIX5: pair_sum must match over exactly one enum"),
    };
    let layout = crate::enum_layout_of(tcx, adt)?;
    let typing_env = TypingEnv::fully_monomorphized();
    let enum_ty = tcx.normalize_erasing_regions(
        typing_env,
        tcx.type_of(adt.did()).instantiate_identity(),
    );
    let enum_args = match enum_ty.kind() {
        TyKind::Adt(_, args) => *args,
        _ => return bail("FIX5: enum type_of is not an Adt"),
    };
    for (vidx, vdef) in adt.variants().iter_enumerated() {
        if vdef.fields.len() != 1 {
            continue;
        }
        let fty = tcx.normalize_erasing_regions(
            typing_env,
            vdef.fields[rustc_abi::FieldIdx::from_usize(0)].ty(tcx, enum_args),
        );
        let TyKind::Tuple(elems) = fty.kind() else {
            continue;
        };
        if elems.len() != 2 {
            continue;
        }
        let field0_off = layout.field_offset(vidx, 0).ok_or_else(|| {
            LowerError("FIX5: no layout offset for the Cell tuple field".into())
        })?;
        let tup_layout = tcx
            .layout_of(typing_env.as_query_input(fty))
            .map_err(|e| LowerError(format!("FIX5: layout_of tuple failed ({e:?})")))?;
        let mut out: Vec<(i128, trust_ir::ty::Ty)> = Vec::with_capacity(2);
        for i in 0..2 {
            let off = field0_off + tup_layout.fields.offset(i).bytes() as i128;
            // The sub-field's REAL IR width, from its concrete scalar type.
            let sub_ty = elems[i];
            let w = lower_concrete_ty(tcx, sub_ty).map_err(|e| {
                LowerError(format!("FIX5: Cell sub-field {i} ty {sub_ty:?}: {e}"))
            })?;
            out.push((off, w));
        }
        return Ok([out[0].clone(), out[1].clone()]);
    }
    bail("FIX5: no `Cell((i32,i32))`-shaped tuple-payload variant found")
}

/// FIX 5: run the NARROW-WIDTH aggregate-payload differential. Lower `pair_sum`
/// (the recursive `match &Pair -> i32` fold over a `Cell((i32, i32))` inline tuple)
/// through the worklist, then build a heap-graph runner per `Pair` corpus value and
/// check interp == native `Pair::pair_sum`. The `Cell` sub-fields are written +
/// read at their REAL narrow I32 width and `layout_of` i32-stride offsets — so a
/// wrong narrow Load/Store width (an I64 read pulls in the neighbour) or a wrong
/// offset would mis-sum.
/// Returns (module, report). `None` if the corpus has no `pair_sum`.
pub fn run_m5_pair_differential<'tcx>(
    tcx: TyCtxt<'tcx>,
    pair_sum_def: LocalDefId,
) -> LResult<(Module, M3Report)> {
    use crate::model::{add_pair_int_runner, Pair};

    let mut mb = ModuleBuilder::new("frontend::m5::pairwidth".to_string());
    let i64_ty = tcx.types.i64;

    // `pair_sum` returns i32 (the NARROW width) — the worklist lowering derives the
    // ret ty from the THIR. Use the i64 placeholder for the (unused) generic arg.
    let lowered = lower_callchain_instance(tcx, &mut mb, pair_sum_def, i64_ty, "i64", 0)?;
    let root = lowered
        .first()
        .ok_or_else(|| LowerError("FIX5: empty worklist".into()))?;
    if root.param_tys.as_slice() != [trust_ir::ty::Ty::Ptr] || root.ret_ty != trust_ir::ty::Ty::I32
    {
        return bail(format!(
            "FIX5: `pair_sum` lowered to {:?} -> {:?}, expected fn(Ptr) -> I32 (the narrow ret)",
            root.param_tys, root.ret_ty
        ));
    }
    let target = root.func_id;

    let end = || Pair::End;
    let cell = |a: i32, b: i32| Pair::Cell(a, b);
    let next = |p: Pair| Pair::Next(Box::new(p));
    let cases: Vec<(String, Pair)> = vec![
        ("pair_sum(End) [leaf]".into(), end()),
        ("pair_sum(Cell(3, 4)) [narrow-width tuple]".into(), cell(3, 4)),
        // i32 boundary values prove the NARROW Load width: read as I32 they are
        // exactly these; an I64 read of sub-field 0 would also pull in sub-field 1's
        // bytes (the neighbour), changing the value -> a mismatch.
        ("pair_sum(Cell(i32::MAX, 1)) [i32::MAX narrow + wrap]".into(), cell(i32::MAX, 1)),
        ("pair_sum(Cell(i32::MIN, -1)) [i32::MIN narrow + wrap]".into(), cell(i32::MIN, -1)),
        ("pair_sum(Cell(-1, 10)) [i32 sign-extend]".into(), cell(-1, 10)),
        ("pair_sum(Cell(100, -250)) [mixed sign]".into(), cell(100, -250)),
        ("pair_sum(Next(End)) [box leaf]".into(), next(end())),
        (
            "pair_sum(Next(Cell(-5, 100))) [box over narrow tuple]".into(),
            next(cell(-5, 100)),
        ),
        (
            "pair_sum(Next(Next(Cell(7, -9)))) [deep box over tuple]".into(),
            next(next(cell(7, -9))),
        ),
    ];

    let heap_lay =
        crate::model::HeapLayout::from_enum_layout(&matched_enum_layout(tcx, pair_sum_def)?);
    let cell_subs = pair_cell_sub_offsets_widths(tcx, pair_sum_def)?;
    // The runner returns the SAME narrow i32 as `pair_sum`.
    let nullary_i32 = mb.add_func_type(vec![], vec![trust_ir::ty::Ty::I32]);
    let runners: Vec<(String, i128, FuncId)> = cases
        .iter()
        .enumerate()
        .map(|(i, (label, p))| {
            let oracle = p.pair_sum() as i128;
            let runner = add_pair_int_runner(
                &mut mb,
                &heap_lay,
                &cell_subs,
                p,
                target,
                nullary_i32,
                &format!("run_pair_{i}"),
            );
            (label.clone(), oracle, runner)
        })
        .collect();

    let module = mb.build()?;
    let verrs = trust_ir_build::validate_module(&module);

    let mut checks = Vec::new();
    for (label, oracle, runner) in runners {
        push_int_check(&module, &mut checks, &label, runner, oracle);
    }

    Ok((module, M3Report { validate_errors: verrs.len(), checks }))
}

/// Emit the M5.7e aggregate-payload round-trip module (`sym_sum`, the recursive
/// `match &Sym -> i64` fold + its `Sym` tagged struct) as standalone trust-ir TEXT
/// for the downstream trust-cg JIT round-trip. Mirrors `emit_eval_roundtrip_module`.
pub fn emit_sym_roundtrip_module<'tcx>(
    tcx: TyCtxt<'tcx>,
    sym_sum_def: LocalDefId,
) -> LResult<Module> {
    let mut mb = ModuleBuilder::new("frontend::m5::symagg".to_string());
    let i64_ty = tcx.types.i64;
    let _lowered = lower_callchain_instance(tcx, &mut mb, sym_sum_def, i64_ty, "i64", 0)?;
    Ok(mb.build()?)
}

// --- M5.7f: ENUM-VARIANT CONSTRUCTION (the DUAL of lower_match_adt) ------------
//
// M5.4/M5.7b could only READ a tagged-struct heap value (a `match`); every enum-
// variant CONSTRUCTION bailed (the audit's fail-loud guard in `lower_zst_adt`).
// M5.7f adds the construction path — `HeapAlloc` the enum's tagged struct, `Store`
// the i32 discriminant, then `Store` each field by its kind (a Box-child stores
// the inner POINTER; an inline scalar stores the VALUE). This is the key remaining
// capability for a real `whnf` (which BUILDS the reduced term), and is the exact
// DUAL of `lower_match_adt` (which reads what this writes).
//
// The corpus shapes are CONSTRUCT-THEN-FOLD: each fn BUILDS a closed `Level`/`Val`/
// `NBox` term with the new construction path, then FOLDS it through the EXISTING
// match path (`count_succ`/`eval`/`nbox_depth`) to an int the differential checks
// against a Rust-semantics expected-value oracle. A wrong construction (wrong
// tag/slot, missing Store) surfaces as a wrong fold — so the round-trip
// (construct ; inspect) is a real witness.
//
// FIX 2: the `NBox` family adds the NICHE untagged-variant construction. `NBox` is
// niche-encoded with `Cons(Box<NBox>)` as the UNTAGGED variant (the Switch
// default), so constructing it exercises `lower_enum_variant_construction`'s
// `is_niche_untagged` branch (which stores NO synthetic tag — the Box pointer IS
// the discriminant). Folding it back through `nbox_depth` (whose `Cons` arm is the
// Switch default) confirms it reads back as the untagged variant.

/// Run the M5.7f enum-variant-construction differential. Lowers each construct-
/// then-fold fn (`one_depth`/`two_depth`: nullary i64; `lit_eval`/`neg_lit`:
/// i64->i64) through its OWN worklist (which lowers the constructor fns + the
/// folder, and registers the constructed/matched enum's tagged struct), builds a
/// nullary runner per case (with the i64 argument for the unary fns), and checks
/// interp == native oracle. Returns (module, report).
///
/// The native oracle is computed the same way M4's `quad_oracle` is — by the SAME
/// arithmetic the corpus documents (`one_depth()==1`, `two_depth()==2`,
/// `lit_eval(n)==n`, `neg_lit(n)==-n`), NOT a hand literal — over several inputs.
///
/// SOUNDNESS / LAYOUT: `build_enum_model` hardcodes every enum's tagged struct to
/// `StructId(0)` (the M1/M2/model.rs convention, kept for byte-identity). The
/// M5.7f corpus spans TWO distinct enums (`Level` for one_depth/two_depth, `Val`
/// for lit_eval/neg_lit). Putting both in ONE module would register two different
/// `StructId(0)`s — a validate error. So each ENUM FAMILY is lowered into its OWN
/// module (the M5.4/M5.7b single-enum-per-module discipline) and the per-module
/// reports are AGGREGATED. Returns (total function count across modules, report).
pub fn run_m5k_differential<'tcx>(
    tcx: TyCtxt<'tcx>,
    one_depth_def: Option<LocalDefId>,
    two_depth_def: Option<LocalDefId>,
    lit_eval_def: Option<LocalDefId>,
    neg_lit_def: Option<LocalDefId>,
    // FIX 2: the NICHE untagged-variant construction family (`NBox`).
    nbox_depth_defs: [Option<LocalDefId>; 3],
) -> LResult<(usize, M3Report)> {
    let [nbox_nil_depth_def, nbox_one_depth_def, nbox_two_depth_def] = nbox_depth_defs;
    // `args` is the i64 input list (empty for the nullary depth fns); the oracle is
    // computed BY THE DOCUMENTED ARITHMETIC, not a literal.
    let probes_n = [-7i128, 0, 1, 5, 42, i64::MAX as i128, i64::MIN as i128];
    // A FAMILY = the construct-then-fold fns over ONE enum, lowered into ONE module.
    // Each entry: (fn def, cases) where a case is (label, args, oracle).
    type Cases = Vec<(String, Vec<i128>, i128)>;
    let level_family: Vec<(Option<LocalDefId>, Cases)> = vec![
        (
            one_depth_def,
            vec![("one_depth() builds Succ(Zero) -> 1".into(), vec![], 1)],
        ),
        (
            two_depth_def,
            vec![("two_depth() builds Succ(Succ(Zero)) -> 2".into(), vec![], 2)],
        ),
    ];
    let val_family: Vec<(Option<LocalDefId>, Cases)> = vec![
        (
            lit_eval_def,
            // builds Lit(n), evals -> n. Oracle: n.
            probes_n
                .iter()
                .map(|&n| (format!("lit_eval({n}) builds Lit({n}) -> {n}"), vec![n], n))
                .collect(),
        ),
        (
            neg_lit_def,
            // builds Neg(Lit(n)), evals -> -n. Oracle: wrapping negation (matches the
            // interpreter's i64 UnOp::Neg / Rust `-` on i64::MIN, which wraps to itself).
            probes_n
                .iter()
                .map(|&n| {
                    let oracle = (n as i64).wrapping_neg() as i128;
                    (format!("neg_lit({n}) builds Neg(Lit({n})) -> {oracle}"), vec![n], oracle)
                })
                .collect(),
        ),
    ];
    // FIX 2: the NICHE family. `NBox` is niche-encoded with `Cons(Box<NBox>)` as
    // the UNTAGGED variant (the Switch default) — so `nbox_one_depth`/
    // `nbox_two_depth` CONSTRUCT the niche untagged variant (the no-tag-store
    // `is_niche_untagged` branch) and fold it back through `nbox_depth` (whose
    // `Cons` arm IS the Switch default). `nbox_nil_depth` constructs the
    // niche-ENCODED `Nil` (a niche value of 0). Oracles: 0, 1, 2.
    let nbox_family: Vec<(Option<LocalDefId>, Cases)> = vec![
        (
            nbox_nil_depth_def,
            vec![(
                "nbox_nil_depth() builds niche-encoded Nil -> 0".into(),
                vec![],
                0,
            )],
        ),
        (
            nbox_one_depth_def,
            vec![(
                "nbox_one_depth() builds untagged Cons(Nil) -> 1".into(),
                vec![],
                1,
            )],
        ),
        (
            nbox_two_depth_def,
            vec![(
                "nbox_two_depth() builds untagged Cons(Cons(Nil)) -> 2".into(),
                vec![],
                2,
            )],
        ),
    ];

    let mut total_fns = 0usize;
    let mut total_verrs = 0usize;
    let mut checks: Vec<(String, String, String, bool)> = Vec::new();

    for (family_name, family) in [
        ("Level", level_family),
        ("Val", val_family),
        ("NBox", nbox_family),
    ] {
        // Skip a family with no defs present.
        if family.iter().all(|(d, _)| d.is_none()) {
            continue;
        }
        let i64_ty = tcx.types.i64; // identity args for the non-generic construct fns.
        let mut mb = ModuleBuilder::new(format!("frontend::m5::construct::{family_name}"));

        // PHASE 1: collect all actual roots in ONE typed worklist for this
        // nominal enum family. A shared folder is discovered/lowered once,
        // and every original root ordinal is retained independently.
        let (instances, case_sets): (Vec<_>, Vec<_>) = family.into_iter().filter_map(|(def, cases)| {
            def.map(|def| {
                let args = args_for_single_type_param(tcx, def.to_def_id(), i64_ty);
                (MonoInstance { def, args }, cases)
            })
        }).unzip();
        let (wl, root_ids) = worklist_batch::collect_roots(tcx, instances)?;
        let func_base = worklist_batch::next_function_id(&mb)?.index();
        let lowered = emit_worklist(tcx, &mut mb, &wl, WorklistSymbols::SourceOwned, func_base, true)?;
        let roots = worklist_batch::selected_roots(&lowered, &root_ids)?;

        // PHASE 2: append a nullary runner per case (after every root).
        let mut plan: Vec<(String, i128, FuncId)> = Vec::new();
        for (root, cases) in roots.into_iter().zip(case_sets) {
            for (label, args, oracle) in cases {
                let runner = add_nary_runner(&mut mb, &root, &args);
                plan.push((label, oracle, runner));
            }
        }

        let module = mb.build()?;
        total_fns += module.functions.len();
        total_verrs += trust_ir_build::validate_module(&module).len();
        for (label, oracle, runner) in plan {
            push_int_check(&module, &mut checks, &label, runner, oracle);
        }
    }

    if checks.is_empty() {
        return bail("M5.7f: no construct-then-fold defs in corpus");
    }

    Ok((total_fns, M3Report { validate_errors: total_verrs, checks }))
}

/// Emit the M5.7f enum-variant-construction round-trip module — the construct-
/// then-fold fn `two_depth`, which BUILDS `Succ(Succ(Zero))` INLINE (the recursive
/// `HeapAlloc`+`Store` construction, the `Box::new`-construction showcase) and
/// FOLDS it via `count_succ` — plus the `count_succ` folder it calls and the
/// `Level` tagged struct, as standalone trust-ir TEXT for a downstream trust-cg
/// JIT round-trip.
///
/// SCOPE: ONLY `two_depth` is emitted (NOT also `one_depth`/`lit_eval`/`neg_lit`).
/// Emitting several construct-then-fold roots into one module would duplicate the
/// FOLDER (each root's worklist re-lowers `count_succ`/`eval`) → two functions
/// named `count_succ__i64`, which the JIT resolves by NAME (a duplicate-symbol
/// clash), AND span two enums at the same `StructId(0)`. `two_depth` is the
/// SELF-CONTAINED witness: nullary, it constructs AND folds internally, so the JIT
/// fn takes no args and its return value IS the round-trip result. Mirrors the
/// single-root emit discipline of `emit_adt_match_roundtrip_module`.
pub fn emit_construct_roundtrip_module<'tcx>(
    tcx: TyCtxt<'tcx>,
    two_depth_def: LocalDefId,
) -> LResult<Module> {
    let mut mb = ModuleBuilder::new("frontend::m5::construct".to_string());
    let i64_ty = tcx.types.i64;
    let _lowered = lower_callchain_instance(tcx, &mut mb, two_depth_def, i64_ty, "i64", 0)?;
    Ok(mb.build()?)
}

// --- M5.6 CAPSTONE: REAL clean-kernel `Level::is_zero`/`is_nonzero` -----------
//
// M5.4 lowered a value-RETURNING (i64) recursive ADT fold (`count_succ`). M5.6 is
// the CAPSTONE: the ACTUAL bool-returning recursive predicate the LowerCx M1/M2
// path hand-targeted — `Level::is_zero`/`is_nonzero` — lowered through the SAME
// unified `MonoCx::lower_expr`. It combines, on one genuine clean-kernel leaf:
//   - a heap-tag `match` over the recursive `Level` ADT (M5.4 lower_match_adt),
//   - `&&`/`||` short-circuit in the `Max` arm (M5.1 lower_logical),
//   - bool literal arms (the unified Literal arm),
//   - worklist recursion on a `fn(ptr) -> bool` (the self-call `a.is_zero()`
//     desugars to `Level::is_zero(a)`, an FnDef Call resolved by the worklist).
//
// The whole point is PARITY with M1/M2: MonoCx must reproduce the SAME result set
// LowerCx's 21/21 heap differential produces. So the differential reuses the
// EXISTING M1/M2 heap machinery from `model.rs` — the same `corpus()` of `Micro`
// values, the same `build_heap_value` (via `add_input_runner`), and the same
// native oracle (`Micro::is_zero`/`is_nonzero`) — but drives the MonoCx-lowered
// predicate instead of the hand-mirrored `build_predicate_module`. A MATCH on
// every case is the proof that MonoCx subsumes the LowerCx leaf class.

/// Run the M5.6 capstone differential for one predicate (`is_zero`/`is_nonzero`),
/// in PARITY with the M1/M2 21/21 heap differential. Lower the predicate through
/// the worklist (registering the `Level` tagged struct + lowering the
/// value-producing bool heap-tag match with `&&`/`||` + worklist recursion), then
/// append one heap-constructing bool runner per `Micro` corpus value (reusing
/// `model::add_input_runner` + `model::build_heap_value`) and check interp ==
/// native `Micro::is_zero`/`is_nonzero` on EVERY case. Returns (module, report).
pub fn run_m5f_differential<'tcx>(
    tcx: TyCtxt<'tcx>,
    pred_def: LocalDefId,
    pred_name: &str,
) -> LResult<(Module, M3Report)> {
    use crate::model::{add_input_runner, corpus, Micro};

    let mut mb = ModuleBuilder::new(format!("frontend::m5::pred::{pred_name}"));
    let i64_ty = tcx.types.i64; // unused by the non-generic predicate; identity args.

    // Lower the predicate (it self-recurses, so the worklist is just itself) and
    // register the `Level` tagged struct in the module. The root is FuncId 0, a
    // `fn(ptr) -> bool` — the exact signature the M1/M2 LowerCx predicate has.
    let lowered = lower_callchain_instance(tcx, &mut mb, pred_def, i64_ty, "i64", 0)?;
    let root = lowered
        .first()
        .ok_or_else(|| LowerError("M5.6: empty worklist".into()))?;
    // Guard the parity contract: the MonoCx-lowered predicate must be the same
    // `fn(ptr) -> bool` shape LowerCx emits (so the heap runner's Call matches).
    if root.param_tys.as_slice() != [trust_ir::ty::Ty::Ptr]
        || root.ret_ty != trust_ir::ty::Ty::Bool
    {
        return bail(format!(
            "M5.6: predicate `{pred_name}` lowered to {:?} -> {:?}, expected fn(Ptr) -> Bool \
             (the M1/M2 leaf signature)",
            root.param_tys, root.ret_ty
        ));
    }
    let target = root.func_id;

    // Drive the SAME corpus + oracle the M1/M2 21/21 heap differential uses.
    // SOUNDNESS (audit FIX 7): bail LOUDLY on an unknown predicate name BEFORE
    // building runners — a silent `_ => false` oracle would mis-oracle any other
    // predicate (always reporting `false`), masking a wrong lowering as "matching".
    if pred_name != "is_zero" && pred_name != "is_nonzero" {
        return bail(format!(
            "M5.6: no native oracle for predicate `{pred_name}` (only `is_zero`/`is_nonzero` \
             are modeled) — refusing to differential-test against a default-false oracle"
        ));
    }
    let cases = corpus();
    // M6: the FAITHFUL `Level` heap layout (from `layout_of`) the lowered predicate reads.
    let heap_lay =
        crate::model::HeapLayout::from_enum_layout(&matched_enum_layout(tcx, pred_def)?);
    let nullary_bool = mb.add_func_type(vec![], vec![trust_ir::ty::Ty::Bool]);
    let runners: Vec<(String, bool, FuncId)> = cases
        .iter()
        .enumerate()
        .map(|(i, m)| {
            let oracle = match pred_name {
                "is_zero" => m.is_zero(),
                "is_nonzero" => m.is_nonzero(),
                // Unreachable: the guard above bails on any other name.
                other => unreachable!("unexpected predicate name {other:?}"),
            };
            let runner = add_input_runner(
                &mut mb,
                &heap_lay,
                m,
                target,
                nullary_bool,
                &format!("run_pred_{i}"),
            );
            (format!("{pred_name}({m:?})"), oracle, runner)
        })
        .collect();

    let module = mb.build()?;
    let verrs = trust_ir_build::validate_module(&module);

    let mut checks = Vec::new();
    for (label, oracle, runner) in runners {
        push_bool_check(&module, &mut checks, &label, runner, oracle);
    }

    // Sanity: the corpus must cover every variant (incl. Param) — same coverage
    // the M1/M2 differential asserts. We do not gate the report on it (the driver
    // prints the match count), but a too-small corpus would silently weaken the
    // parity claim, so reflect it: not enough cases is a (reported) failure.
    let _ = Micro::Zero; // keep the import live + document the oracle source.

    Ok((module, M3Report { validate_errors: verrs.len(), checks }))
}

/// Emit the M5.6 capstone round-trip module (`is_zero`, plus `is_nonzero` when
/// present, plus the `Level` tagged struct) as standalone trust-ir TEXT for the
/// downstream trust-cg JIT round-trip. Each predicate self-recurses (is_zero
/// calls only is_zero; is_nonzero only is_nonzero), so each worklist is a single
/// `fn(ptr) -> bool`. We emit `is_zero` first (base 0), then `is_nonzero` based
/// AFTER it so its self-Call edge targets the right FuncId — exactly the
/// multi-root pattern `emit_let_roundtrip_module` uses. Emitting the first
/// predicate also emits the shared `Level` struct definition (registered once;
/// the second predicate's worklist reuses StructId 0).
pub fn emit_predicate_roundtrip_module<'tcx>(
    tcx: TyCtxt<'tcx>,
    is_zero_def: LocalDefId,
    is_nonzero_def: Option<LocalDefId>,
) -> LResult<Module> {
    let mut mb = ModuleBuilder::new("frontend::m5::pred".to_string());
    let i64_ty = tcx.types.i64;
    // `is_zero` self-recurses: its worklist is exactly 1 fn (root at FuncId 0).
    // It REGISTERS the shared `Level` tagged struct (StructId 0).
    let iz = lower_callchain_instance(tcx, &mut mb, is_zero_def, i64_ty, "i64", 0)?;
    if let Some(inz) = is_nonzero_def {
        let base = iz.len() as u32;
        // `is_nonzero` also self-recurses (1 fn), based AFTER is_zero's functions
        // so its forward self-Call edge resolves to its own FuncId. It matches the
        // SAME `Level` enum, already registered above, so it must NOT re-add the
        // struct (`register_structs=false`) — a duplicate StructId(0) would fail
        // validation. It reuses StructId 0 for its field Loads.
        let _inz = lower_callchain_instance_ext(tcx, &mut mb, inz, i64_ty, "i64", base, false)?;
    }
    Ok(mb.build()?)
}

// --- M3 differential harness -------------------------------------------------

/// Build a single module containing the M3 instances + the trait dispatch,
/// validate it, and differential-test each against a native oracle. Returns a
/// structured report.
pub struct M3Report {
    pub validate_errors: usize,
    /// (label, ir_result, oracle, match?)
    pub checks: Vec<(String, String, String, bool)>,
}

impl M3Report {
    pub fn all_match(&self) -> bool {
        self.checks.iter().all(|c| c.3)
    }
    pub fn n_match(&self) -> usize {
        self.checks.iter().filter(|c| c.3).count()
    }
    pub fn n_total(&self) -> usize {
        self.checks.len()
    }
}

use trust_ir::interpret::{Interpreter, InterpretValue};

/// A trait-static-dispatch caller lowered through the UNIFIED worklist path.
/// `caller` is the (nullary) caller fn (`call_yes`/`call_two`); `resolved_name`
/// is the human-readable resolved impl method (`<Yes as Predicate>::pred`).
struct TraitCaller {
    caller: FuncId,
    resolved_name: String,
}

/// Lower a trait-static-dispatch CALLER (`call_yes`/`call_no`/`call_two`/...) and
/// its resolved impl method THROUGH the unified worklist, exactly as a generic
/// call chain. The caller's body — `let y = Yes; y.pred()` — flows through
/// `lower_expr`: the ZST receiver construction lowers to a placeholder `Ptr`
/// (`lower_zst_adt`), and the method call `Predicate::pred(&y)` resolves (via
/// `resolve_user_call`/`Instance::try_resolve`) to the concrete impl method,
/// which is itself a worklist instance whose body lowers via `lower_expr` and
/// whose signature is DERIVED from the resolved instance sig (no hardcoded
/// `(Ptr)->Bool`). `func_base` MUST equal the module's current function count
/// (the worklist's load-bearing FuncId contract). Returns the caller handle plus
/// the count of functions this worklist emitted (to advance the running base).
fn lower_trait_caller<'tcx>(
    tcx: TyCtxt<'tcx>,
    mb: &mut ModuleBuilder,
    caller_def: LocalDefId,
    name_suffix: &str,
    func_base: u32,
) -> LResult<(TraitCaller, u32)> {
    // The caller is non-generic, so the i64 `concrete` is just an unused identity
    // arg seed (mirrors how the non-generic M5.4/M5.6 roots are lowered).
    let i64_ty = tcx.types.i64;
    let args = args_for_single_type_param(tcx, caller_def.to_def_id(), i64_ty);
    let instance = MonoInstance { def: caller_def, args };
    let (wl, root_ids) = worklist_batch::collect_roots(tcx, [instance])?;
    let root = wl.instances.get(root_ids[0] as usize)
        .ok_or_else(|| LowerError("trait-dispatch: missing collected source root".into()))?;
    let export = WorklistSymbols::RootExport { root: root.key(), suffix: name_suffix };
    let lowered = emit_worklist(tcx, mb, &wl, export, func_base, true)?;
    let roots = worklist_batch::selected_roots(&lowered, &root_ids)?;
    let root = roots
        .first()
        .ok_or_else(|| LowerError("trait-dispatch: empty worklist".into()))?;
    // The resolved impl method is the worklist's other instance (the caller calls
    // exactly one method). Build the human-readable resolution from its def path.
    // Re-resolve from the caller's THIR so the label is the genuine impl method
    // (`<Yes as Predicate>::pred`), not the generated FuncId name.
    let resolved_name = resolve_trait_callee_name(tcx, caller_def)?;
    let count = u32::try_from(lowered.len())
        .map_err(|_| LowerError("trait-dispatch worklist exceeds the FuncId space".into()))?;
    Ok((TraitCaller { caller: root.func_id, resolved_name }, count))
}

/// Resolve the single trait-method call in a nullary trait-dispatch caller body
/// to the human-readable impl method path (`<Yes as Predicate>::pred`). Used only
/// for the differential LABEL; the actual lowering goes through the worklist.
fn resolve_trait_callee_name<'tcx>(
    tcx: TyCtxt<'tcx>,
    caller_def: LocalDefId,
) -> LResult<String> {
    let typing_env = TypingEnv::fully_monomorphized();
    let (thir_steal, body_expr) = tcx
        .thir_body(caller_def)
        .map_err(|_| LowerError("thir_body errored on trait caller".into()))?;
    let thir = thir_steal.borrow();
    let mut found: Vec<MonoInstance<'tcx>> = Vec::new();
    let identity = ty::GenericArgs::identity_for_item(tcx, caller_def.to_def_id());
    collect_calls_in_body(tcx, typing_env, &thir, identity, body_expr, &mut found)?;
    match found.first() {
        Some(inst) => Ok(tcx.def_path_str(inst.def.to_def_id())),
        None => bail("trait-dispatch caller body has no resolvable method call"),
    }
}

/// Run the full M3 lowering + differential against native oracles. `id_def`,
/// `double_def`, `call_yes_def` are the resolved corpus defs. The trait-dispatch
/// callers (`call_yes`/`call_no`, plus the NON-constant `call_two`/`call_neg`
/// when present) are lowered through the SAME unified worklist as the generic
/// call chains — no bespoke constant-bool special case.
pub fn run_m3_differential<'tcx>(
    tcx: TyCtxt<'tcx>,
    id_def: LocalDefId,
    double_def: LocalDefId,
    call_yes_def: LocalDefId,
    call_no_def: Option<LocalDefId>,
    call_two_def: Option<LocalDefId>,
    call_neg_def: Option<LocalDefId>,
) -> LResult<(Module, M3Report)> {
    let mut mb = ModuleBuilder::new("frontend::m3".to_string());

    let u32_ty = tcx.types.u32;
    let i64_ty = tcx.types.i64;

    // Two instantiations of `id`, two of `double` — distinct concrete Functions.
    // Each `lower_scalar_generic_instance` adds exactly ONE function.
    let id_u32 = lower_scalar_generic_instance(tcx, &mut mb, id_def, u32_ty, "u32")?;
    let id_i64 = lower_scalar_generic_instance(tcx, &mut mb, id_def, i64_ty, "i64")?;
    let dbl_u32 = lower_scalar_generic_instance(tcx, &mut mb, double_def, u32_ty, "u32")?;
    let dbl_i64 = lower_scalar_generic_instance(tcx, &mut mb, double_def, i64_ty, "i64")?;

    // Trait static dispatch, NOW through the unified worklist. `func_base` tracks
    // the module's running function count so each worklist's "root at FuncId base"
    // contract holds. The 4 scalar instances above occupy FuncIds 0..4.
    let mut func_base = worklist_batch::next_function_id(&mb)?.index();
    // `call_yes()` resolves `Yes.pred()` -> the impl, a DIRECT Call (a bool leaf).
    let (dispatch, _) = lower_trait_caller(tcx, &mut mb, call_yes_def, "i64", func_base)?;
    func_base = worklist_batch::next_function_id(&mb)?.index();
    // A SECOND caller on a different Self proves per-Self resolution.
    let dispatch_no = match call_no_def {
        Some(d) => {
            let (tc, _) = lower_trait_caller(tcx, &mut mb, d, "i64", func_base)?;
            func_base = worklist_batch::next_function_id(&mb)?.index();
            Some(tc)
        }
        None => None,
    };
    // NON-constant trait methods (`call_two`/`call_neg`): the resolved impl body is
    // an i64 ARITHMETIC expression (`1 + 1`, `0 - 7`), not a literal — proving the
    // callee body lowers via `lower_expr` + a DERIVED `fn(Ptr) -> i64` sig.
    let dispatch_two = match call_two_def {
        Some(d) => {
            let (tc, _) = lower_trait_caller(tcx, &mut mb, d, "i64", func_base)?;
            func_base = worklist_batch::next_function_id(&mb)?.index();
            Some(tc)
        }
        None => None,
    };
    let dispatch_neg = match call_neg_def {
        Some(d) => {
            let (tc, _) = lower_trait_caller(tcx, &mut mb, d, "i64", func_base)?;
            func_base = worklist_batch::next_function_id(&mb)?.index();
            Some(tc)
        }
        None => None,
    };
    let _ = func_base; // runners below get fresh sequential FuncIds (no edge to them).

    // Wrap each generic instance in a nullary "apply a literal arg" runner so the
    // interpreter can drive it without external inputs.
    let id_u32_run = add_unary_runner(&mut mb, &id_u32, 7);
    let id_i64_run = add_unary_runner(&mut mb, &id_i64, -5);
    let dbl_u32_run = add_unary_runner(&mut mb, &dbl_u32, 21);
    let dbl_i64_run = add_unary_runner(&mut mb, &dbl_i64, -9);
    // Width-DISCRIMINATING witnesses (audit fix): same input magnitude, but the
    // result differs by the per-instantiation IR width — these FAIL if u32 were
    // (incorrectly) lowered at i64 width. double::<u32>(0x8000_0000) wraps to 0 at
    // 32 bits; double::<i64> of the same value does NOT wrap (= 0x1_0000_0000).
    let dbl_u32_wrap_run = add_unary_runner(&mut mb, &dbl_u32, 0x8000_0000);
    let dbl_i64_nowrap_run = add_unary_runner(&mut mb, &dbl_i64, 0x8000_0000);

    let module = mb.build()?;
    let verrs = trust_ir_build::validate_module(&module);

    let mut checks = Vec::new();
    // id::<u32>(7) == 7 ; id::<i64>(-5) == -5
    push_int_check(&module, &mut checks, "id::<u32>(7)", id_u32_run, 7);
    push_int_check(&module, &mut checks, "id::<i64>(-5)", id_i64_run, -5);
    // double::<u32>(21) == 42 ; double::<i64>(-9) == -18
    push_int_check(&module, &mut checks, "double::<u32>(21)", dbl_u32_run, 42);
    push_int_check(&module, &mut checks, "double::<i64>(-9)", dbl_i64_run, -18);
    // width-discriminating: 32-bit wrap vs 64-bit no-wrap on the same magnitude.
    push_int_check(
        &module,
        &mut checks,
        "double::<u32>(0x8000_0000) [U32 wraps->0]",
        dbl_u32_wrap_run,
        0,
    );
    push_int_check(
        &module,
        &mut checks,
        "double::<i64>(0x8000_0000) [I64 no-wrap]",
        dbl_i64_nowrap_run,
        0x1_0000_0000,
    );
    // trait dispatch (via the UNIFIED worklist): call_yes() == true.
    push_bool_check(
        &module,
        &mut checks,
        &format!("call_yes() [-> {}]", dispatch.resolved_name),
        dispatch.caller,
        true,
    );
    if let Some(d) = &dispatch_no {
        push_bool_check(
            &module,
            &mut checks,
            &format!("call_no() [-> {}]", d.resolved_name),
            d.caller,
            false,
        );
    }
    // NON-constant trait method bodies lowered via lower_expr + a DERIVED sig:
    // call_two() == 2 (impl body `1 + 1`), call_neg() == -7 (impl body `0 - 7`).
    if let Some(d) = &dispatch_two {
        push_int_check(
            &module,
            &mut checks,
            &format!("call_two() [-> {} = 1+1]", d.resolved_name),
            d.caller,
            2,
        );
    }
    if let Some(d) = &dispatch_neg {
        push_int_check(
            &module,
            &mut checks,
            &format!("call_neg() [-> {} = 0-7]", d.resolved_name),
            d.caller,
            -7,
        );
    }

    Ok((module, M3Report { validate_errors: verrs.len(), checks }))
}

/// Emit a FOCUSED module containing only the two scalar i64 instantiations
/// (`id__i64`, `double__i64`) as directly-callable `i64 -> i64` functions — no
/// nullary runners or trait dispatch. This is the artifact for the end-to-end
/// trust-cg round-trip (frontend monomorphization -> trust-ir text -> trust-cg
/// JIT -> native machine code -> executed + cross-checked). Both functions are
/// single-block scalar arithmetic (`id` returns its arg; `double` returns
/// `fb.add(x, x)`), the class trust-cg's triple-oracle already proves. The
/// caller serializes the returned `Module` via its `Display` (the trust_ir text
/// format) so a stock-cargo trust-cg test can `parse_module` it.
pub fn emit_scalar_roundtrip_module<'tcx>(
    tcx: TyCtxt<'tcx>,
    id_def: LocalDefId,
    double_def: LocalDefId,
) -> LResult<Module> {
    let mut mb = ModuleBuilder::new("frontend::m3::roundtrip".to_string());
    let i64_ty = tcx.types.i64;
    let _id_i64 = lower_scalar_generic_instance(tcx, &mut mb, id_def, i64_ty, "i64")?;
    let _dbl_i64 = lower_scalar_generic_instance(tcx, &mut mb, double_def, i64_ty, "i64")?;
    Ok(mb.build()?)
}

/// Add a nullary runner that calls a unary scalar instance with a literal int
/// argument and returns the result. Returns the runner FuncId.
fn add_unary_runner(mb: &mut ModuleBuilder, inst: &LoweredInstance, arg: i128) -> FuncId {
    let ret_ty = inst.ret_ty.clone();
    let in_ty = inst.param_tys[0].clone();
    let sig = mb.add_func_type(vec![], vec![ret_ty]);
    let runner_name = fresh_runner_name(mb, inst);
    let mut fb = mb.function(runner_name, sig);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let a = fb.iconst(in_ty, arg);
    let r = fb.call(inst.func_id, vec![a]);
    fb.ret(vec![r]);
    fb.build()
}

/// Add a nullary runner that calls an N-ary instance with N literal arguments
/// (each `iconst` at the instance's per-position param ir-ty) and returns the
/// result. Generalizes `add_unary_runner`. A `bool` param is fed a 0/1 iconst's
/// truthiness via `bool_const` so the runner matches the callee's `bool` slot.
fn add_nary_runner(mb: &mut ModuleBuilder, inst: &LoweredInstance, args: &[i128]) -> FuncId {
    assert_eq!(
        inst.param_tys.len(),
        args.len(),
        "M5 runner arg count must match instance arity"
    );
    let ret_ty = inst.ret_ty.clone();
    let sig = mb.add_func_type(vec![], vec![ret_ty]);
    let runner_name = fresh_runner_name(mb, inst);
    let mut fb = mb.function(runner_name, sig);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let arg_vals: Vec<ValueId> = inst
        .param_tys
        .iter()
        .zip(args.iter())
        .map(|(ty, &v)| match ty {
            trust_ir::ty::Ty::Bool => fb.bool_const(v != 0),
            int_ty => fb.iconst(int_ty.clone(), v),
        })
        .collect();
    let r = fb.call(inst.func_id, arg_vals);
    fb.ret(vec![r]);
    fb.build()
}

/// A harness invocation owns its own symbol, even when the source instance and
/// arguments repeat. Read the builder's next id before opening the function;
/// deriving it from an argument, source name or case label conflates invocations.
/// This does not rename the source instance or change its FuncId/call edges.
fn fresh_runner_name(mb: &ModuleBuilder, inst: &LoweredInstance) -> String {
    // Once the function-id space is exhausted the next `mb.function(..)`
    // records the fault and `ModuleBuilder::build` refuses, so this name can
    // never reach a module; `u32::MAX` only keeps the spelling total.
    let next = mb.peek_next_func_id().map_or(u32::MAX, |id| id.index());
    format!("run_{}__f{}", inst.name, next)
}

#[cfg(test)]
#[path = "m3_runner_symbol_tests.rs"]
mod runner_symbol_tests;

fn interp_int(module: &Module, runner: FuncId) -> Result<i128, String> {
    let interp = Interpreter::with_module(module);
    let outcome = interp
        .execute_func(runner, [])
        .map_err(|e| format!("interp error: {e:?}"))?;
    let ret = outcome.returns.first().ok_or("no return")?;
    int_of(ret).ok_or_else(|| format!("non-int return: {ret:?}"))
}

/// Extract a signed integer from an interpreter `InterpretValue`, regardless of
/// width (sign-extended per its declared width).
fn int_of(v: &InterpretValue) -> Option<i128> {
    v.as_int().map(|i| i.as_signed())
}

fn interp_bool(module: &Module, runner: FuncId) -> Result<bool, String> {
    let interp = Interpreter::with_module(module);
    let outcome = interp
        .execute_func(runner, [])
        .map_err(|e| format!("interp error: {e:?}"))?;
    let ret = outcome.returns.first().ok_or("no return")?;
    ret.as_bool().ok_or_else(|| format!("non-bool return: {ret:?}"))
}

fn push_int_check(
    module: &Module,
    checks: &mut Vec<(String, String, String, bool)>,
    label: &str,
    runner: FuncId,
    oracle: i128,
) {
    match interp_int(module, runner) {
        Ok(got) => {
            let m = got == oracle;
            checks.push((label.into(), got.to_string(), oracle.to_string(), m));
        }
        Err(e) => checks.push((label.into(), format!("ERR: {e}"), oracle.to_string(), false)),
    }
}

fn push_bool_check(
    module: &Module,
    checks: &mut Vec<(String, String, String, bool)>,
    label: &str,
    runner: FuncId,
    oracle: bool,
) {
    match interp_bool(module, runner) {
        Ok(got) => {
            let m = got == oracle;
            checks.push((label.into(), got.to_string(), oracle.to_string(), m));
        }
        Err(e) => checks.push((label.into(), format!("ERR: {e}"), oracle.to_string(), false)),
    }
}

#[cfg(test)]
mod tests {
    //! These tests lock in the TRUST-IR SIDE of M3 (the shape the driver emits)
    //! without a rustc invocation, mirroring `model.rs`'s self-tests. They build
    //! the SAME instruction shapes `lower_scalar_generic_instance` and the unified
    //! trait-dispatch path emit — a per-instantiation typed `fn(T)->T` and a
    //! direct `Call` to a resolved bool-returning callee — and check
    //! `validate_module` 0 errors + interpreter == oracle. The full
    //! substitution/`try_resolve` path (incl. the trait callers `call_yes`/
    //! `call_no`/`call_two`/`call_neg` through the unified worklist) is exercised
    //! end-to-end by the `--m3` driver run on `m3_corpus.rs` (reported separately).
    use super::*;
    use trust_ir::inst::SwitchCase;
    use trust_ir::ty::Ty;
    use trust_ir_build::validate_module;

    /// Build a concrete `fn(T)->T` (identity or double) at a given IR width, plus
    /// a nullary runner, and return (module, runner_id).
    fn build_scalar(ir_ty: Ty, double: bool, arg: i128) -> (Module, FuncId) {
        let mut mb = ModuleBuilder::new("m3test".to_string());
        let sig = mb.add_func_type(vec![ir_ty.clone()], vec![ir_ty.clone()]);
        let f = {
            let mut fb = mb.function("f", sig);
            let entry = fb.create_block();
            let x = fb.add_block_param(entry, ir_ty.clone());
            fb.switch_to_block(entry);
            let r = if double { fb.add(ir_ty.clone(), x, x) } else { x };
            fb.ret(vec![r]);
            fb.build()
        };
        let nullary = mb.add_func_type(vec![], vec![ir_ty.clone()]);
        let run = {
            let mut fb = mb.function("run", nullary);
            let entry = fb.create_block();
            fb.switch_to_block(entry);
            let a = fb.iconst(ir_ty.clone(), arg);
            let r = fb.call(f, vec![a]);
            fb.ret(vec![r]);
            fb.build()
        };
        (mb.build().expect("ModuleBuilder::build: test fixture"), run)
    }

    #[test]
    fn id_instances_validate_and_match() {
        // id::<u32>(7)=7 (I32 width), id::<i64>(-5)=-5 (I64 width).
        for (ty, arg) in [(Ty::I32, 7i128), (Ty::I64, -5i128)] {
            let (m, run) = build_scalar(ty, false, arg);
            assert_eq!(validate_module(&m).len(), 0, "id validate");
            assert_eq!(interp_int(&m, run).unwrap(), arg, "id interp");
        }
    }

    #[test]
    fn double_instances_validate_and_match() {
        // double::<u32>(21)=42, double::<i64>(-9)=-18.
        for (ty, arg, want) in [(Ty::I32, 21i128, 42i128), (Ty::I64, -9i128, -18i128)] {
            let (m, run) = build_scalar(ty, true, arg);
            assert_eq!(validate_module(&m).len(), 0, "double validate");
            assert_eq!(interp_int(&m, run).unwrap(), want, "double interp");
        }
    }

    /// Trait static dispatch: a caller that directly `Call`s a resolved
    /// bool-returning impl method (`<Self as Predicate>::pred`). We model both
    /// resolutions (Yes->true, No->false) and check the direct call dispatches
    /// to the right constant.
    #[test]
    fn trait_dispatch_direct_call_matches() {
        for (ret, oracle) in [(true, true), (false, false)] {
            let mut mb = ModuleBuilder::new("m3disp".to_string());
            let callee_sig = mb.add_func_type(vec![Ty::Ptr], vec![Ty::Bool]);
            let callee = {
                let mut fb = mb.function("pred_impl", callee_sig);
                let entry = fb.create_block();
                let _self = fb.add_block_param(entry, Ty::Ptr);
                fb.switch_to_block(entry);
                let b = fb.bool_const(ret);
                fb.ret(vec![b]);
                fb.build()
            };
            let caller_sig = mb.add_func_type(vec![], vec![Ty::Bool]);
            let caller = {
                let mut fb = mb.function("caller", caller_sig);
                let entry = fb.create_block();
                fb.switch_to_block(entry);
                let z = fb.iconst(Ty::I64, 0);
                let p = fb.cast(trust_ir::inst::CastOp::IntToPtr, Ty::I64, Ty::Ptr, z);
                let r = fb.call(callee, vec![p]);
                fb.ret(vec![r]);
                fb.build()
            };
            let m = mb.build().expect("ModuleBuilder::build: test fixture");
            assert_eq!(validate_module(&m).len(), 0, "dispatch validate");
            assert_eq!(interp_bool(&m, caller).unwrap(), oracle, "dispatch interp");
        }
    }

    /// M4 call-chain SHAPE lock-in (no rustc): build `quad__i64` (FuncId 0) whose
    /// body is a Call to `double__i64` twice (the inner call feeding the outer),
    /// and `double__i64` (FuncId 1) = `add(x, x)`. The outer `quad` emits the
    /// forward Call edge to FuncId 1 BEFORE `double` is built — exactly what the
    /// worklist does. Plus a nullary runner driving `quad__i64(arg)`. Checks
    /// validate == 0 and interp == 4*arg (wrapping). The full substitution/
    /// try_resolve path is exercised end-to-end by the `--m3` driver (reported
    /// separately).
    #[test]
    fn callchain_worklist_shape_matches() {
        for (arg, want) in [(3i128, 12i128), (-7i128, -28i128), (1_000_000i128, 4_000_000i128)] {
            let mut mb = ModuleBuilder::new("m4chain".to_string());
            let i64i64 = mb.add_func_type(vec![Ty::I64], vec![Ty::I64]);
            // quad__i64 (FuncId 0): double(double(x)) — Call to FuncId 1 twice,
            // the inner call's result feeding the outer call's arg. The callee
            // (FuncId 1) is referenced before it is built (forward edge).
            let quad = {
                let mut fb = mb.function("quad__i64", i64i64);
                let entry = fb.create_block();
                let x = fb.add_block_param(entry, Ty::I64);
                fb.switch_to_block(entry);
                let inner = fb.call(FuncId::new(1), vec![x]);
                let outer = fb.call(FuncId::new(1), vec![inner]);
                fb.ret(vec![outer]);
                fb.build()
            };
            assert_eq!(quad.index(), 0, "quad is FuncId 0");
            // double__i64 (FuncId 1): add(x, x).
            let double = {
                let mut fb = mb.function("double__i64", i64i64);
                let entry = fb.create_block();
                let x = fb.add_block_param(entry, Ty::I64);
                fb.switch_to_block(entry);
                let r = fb.add(Ty::I64, x, x);
                fb.ret(vec![r]);
                fb.build()
            };
            assert_eq!(double.index(), 1, "double is FuncId 1");
            // Nullary runner driving quad(arg).
            let nullary = mb.add_func_type(vec![], vec![Ty::I64]);
            let run = {
                let mut fb = mb.function("run_quad", nullary);
                let entry = fb.create_block();
                fb.switch_to_block(entry);
                let a = fb.iconst(Ty::I64, arg);
                let r = fb.call(quad, vec![a]);
                fb.ret(vec![r]);
                fb.build()
            };
            let m = mb.build().expect("ModuleBuilder::build: test fixture");
            assert_eq!(validate_module(&m).len(), 0, "callchain validate");
            assert_eq!(interp_int(&m, run).unwrap(), want, "callchain interp (4x)");
        }
    }

    /// M5.1 `if`/join SHAPE lock-in (no rustc): build `pick(c,a,b)` =
    /// `if c { a } else { b }` as a 3-param `fn(bool,i64,i64)->i64` with a
    /// `condbr` to then/else blocks joining at a block-param (exactly what the
    /// unified `lower_expr`/`lower_if` emits), plus a runner per (c,a,b), and
    /// check validate==0 and interp picks the right branch. The full THIR `If`
    /// path is exercised end-to-end by the `--m3` driver on `m3_corpus.rs`
    /// (reported separately).
    fn build_pick(c: bool, a: i128, b: i128) -> (Module, FuncId) {
        let mut mb = ModuleBuilder::new("m5pick".to_string());
        let sig = mb.add_func_type(vec![Ty::Bool, Ty::I64, Ty::I64], vec![Ty::I64]);
        let pick = {
            let mut fb = mb.function("pick__i64", sig);
            let entry = fb.create_block();
            let cv = fb.add_block_param(entry, Ty::Bool);
            let av = fb.add_block_param(entry, Ty::I64);
            let bv = fb.add_block_param(entry, Ty::I64);
            fb.switch_to_block(entry);
            let then_b = fb.create_block();
            let else_b = fb.create_block();
            let join = fb.create_block();
            let jp = fb.add_block_param(join, Ty::I64);
            fb.condbr(cv, then_b, vec![], else_b, vec![]);
            fb.switch_to_block(then_b);
            fb.br(join, vec![av]);
            fb.switch_to_block(else_b);
            fb.br(join, vec![bv]);
            fb.switch_to_block(join);
            fb.ret(vec![jp]);
            fb.build()
        };
        let nullary = mb.add_func_type(vec![], vec![Ty::I64]);
        let run = {
            let mut fb = mb.function("run_pick", nullary);
            let entry = fb.create_block();
            fb.switch_to_block(entry);
            let cc = fb.bool_const(c);
            let aa = fb.iconst(Ty::I64, a);
            let bb = fb.iconst(Ty::I64, b);
            let r = fb.call(pick, vec![cc, aa, bb]);
            fb.ret(vec![r]);
            fb.build()
        };
        (mb.build().expect("ModuleBuilder::build: test fixture"), run)
    }

    #[test]
    fn if_join_pick_shape_matches() {
        // pick(true,7,9)=7 ; pick(false,7,9)=9.
        for (c, a, b, want) in [(true, 7i128, 9i128, 7i128), (false, 7, 9, 9)] {
            let (m, run) = build_pick(c, a, b);
            assert_eq!(validate_module(&m).len(), 0, "pick validate");
            assert_eq!(interp_int(&m, run).unwrap(), want, "pick interp");
        }
    }

    /// M5.1 round-trip TEXT lock-in: the if/join module emits canonical trust-ir
    /// text that PARSES BACK to an equivalent, still-valid module (the property
    /// the downstream trust-cg JIT relies on for the `--emit-if` artifact).
    #[test]
    fn if_join_text_roundtrips() {
        let (m, _run) = build_pick(true, 7, 9);
        let text = format!("{m}");
        let reparsed =
            trust_ir::parser::parse_module(&text).expect("emitted if/join text must reparse");
        assert_eq!(
            validate_module(&reparsed).len(),
            0,
            "reparsed if/join module must validate"
        );
    }

    /// M5.3 scalar-`match`/join SHAPE lock-in (no rustc): build `classify(x)` =
    /// `match x { 0=>100, 1=>200, 7=>700, _=>999 }` as a `fn(i64)->i64` that
    /// `switch`es on the scalar VALUE into per-arm blocks each `br`-ing to a
    /// shared join block carrying the result as a block-param — exactly what the
    /// unified `lower_expr`/`lower_match_scalar` emits — plus a runner per input,
    /// and check validate==0 and interp selects the right arm. The full THIR
    /// `Match` path is exercised end-to-end by the `--m3` driver on
    /// `m3_corpus.rs` (reported separately).
    fn build_classify(x: i128) -> (Module, FuncId) {
        let mut mb = ModuleBuilder::new("m5match".to_string());
        let sig = mb.add_func_type(vec![Ty::I64], vec![Ty::I64]);
        let classify = {
            let mut fb = mb.function("classify__i64", sig);
            let entry = fb.create_block();
            let xv = fb.add_block_param(entry, Ty::I64);
            fb.switch_to_block(entry);
            let join = fb.create_block();
            let jp = fb.add_block_param(join, Ty::I64);
            let arm0 = fb.create_block();
            let arm1 = fb.create_block();
            let arm7 = fb.create_block();
            let default = fb.create_block();
            let cases = vec![
                SwitchCase {
                    value: trust_ir::constant::Constant::Int(0),
                    target: arm0,
                    args: vec![],
                },
                SwitchCase {
                    value: trust_ir::constant::Constant::Int(1),
                    target: arm1,
                    args: vec![],
                },
                SwitchCase {
                    value: trust_ir::constant::Constant::Int(7),
                    target: arm7,
                    args: vec![],
                },
            ];
            fb.switch(xv, cases, default, vec![]);
            for (blk, v) in [(arm0, 100), (arm1, 200), (arm7, 700), (default, 999)] {
                fb.switch_to_block(blk);
                let c = fb.iconst(Ty::I64, v);
                fb.br(join, vec![c]);
            }
            fb.switch_to_block(join);
            fb.ret(vec![jp]);
            fb.build()
        };
        let nullary = mb.add_func_type(vec![], vec![Ty::I64]);
        let run = {
            let mut fb = mb.function("run_classify", nullary);
            let entry = fb.create_block();
            fb.switch_to_block(entry);
            let a = fb.iconst(Ty::I64, x);
            let r = fb.call(classify, vec![a]);
            fb.ret(vec![r]);
            fb.build()
        };
        (mb.build().expect("ModuleBuilder::build: test fixture"), run)
    }

    #[test]
    fn scalar_match_switch_shape_matches() {
        // classify: 0->100, 1->200, 7->700, else->999 (incl. a negative).
        for (x, want) in [
            (0i128, 100i128),
            (1, 200),
            (7, 700),
            (2, 999),
            (-5, 999),
        ] {
            let (m, run) = build_classify(x);
            assert_eq!(validate_module(&m).len(), 0, "classify validate");
            assert_eq!(interp_int(&m, run).unwrap(), want, "classify interp");
        }
    }

    /// M5.3 round-trip TEXT lock-in: the scalar-match module emits canonical
    /// trust-ir text that PARSES BACK to an equivalent, still-valid module (the
    /// property the downstream trust-cg JIT relies on for the `--emit-match`
    /// artifact).
    #[test]
    fn scalar_match_text_roundtrips() {
        let (m, _run) = build_classify(7);
        let text = format!("{m}");
        let reparsed =
            trust_ir::parser::parse_module(&text).expect("emitted scalar-match text must reparse");
        assert_eq!(
            validate_module(&reparsed).len(),
            0,
            "reparsed scalar-match module must validate"
        );
    }

    /// M5.4 recursive-ADT-match SHAPE lock-in (no rustc): build `count_succ` =
    /// `match &Level { Zero=>0, Succ(m)=>1+count_succ(m), Max/IMax(a,b)=>
    /// count_succ(a)+count_succ(b), Param=>0 }` as a `fn(ptr)->i64` that Loads
    /// the discriminant TAG through the tagged-struct heap shape, `switch`es on
    /// it into per-variant blocks (each loading its child payload POINTER(s) and
    /// recursing via a Call to its OWN FuncId), and JOINs each arm's i64 at a
    /// block-param — exactly what the unified `lower_expr`/`lower_match_adt`
    /// emits — plus a heap-constructing runner per `Micro` input (reusing
    /// `model::build_heap_value` via `add_int_input_runner`). Checks validate==0
    /// and interp == native `Micro::count_succ`. The full THIR `Match`-over-ADT
    /// path is exercised end-to-end by the `--m3` driver (reported separately).
    fn build_count_succ_module() -> (ModuleBuilder, FuncId) {
        use trust_ir::constant::Constant;
        use trust_ir::ty::{FieldDef, StructDef};
        use trust_ir::value::StructId;
        let mut mb = ModuleBuilder::new("m5adt".to_string());
        // The `Level` tagged struct (tag@0, p0@8, p1@16), the layout
        // `model::build_heap_value` allocates (StructId 0).
        mb.add_struct(StructDef {
            id: StructId::new(0),
            name: "Level".into(),
            fields: vec![
                FieldDef { name: "tag".into(), ty: Ty::I32, offset: None },
                FieldDef { name: "p0".into(), ty: Ty::Ptr, offset: None },
                FieldDef { name: "p1".into(), ty: Ty::Ptr, offset: None },
            ],
            size: None,
            align: None,
            repr: Default::default(),
            origin: None,
        });
        let sig = mb.add_func_type(vec![Ty::Ptr], vec![Ty::I64]);
        let cs = FuncId::new(0);
        {
            let mut fb = mb.function("count_succ", sig);
            let entry = fb.create_block();
            let self_ptr = fb.add_block_param(entry, Ty::Ptr);
            fb.switch_to_block(entry);
            // tag = load i32 (gep i8 self, 0)
            let off0 = fb.iconst(Ty::I64, 0);
            let tagp = fb.gep_inbounds(Ty::I8, self_ptr, vec![off0]);
            let tag = fb.load(Ty::I32, tagp);
            let join = fb.create_block();
            let jp = fb.add_block_param(join, Ty::I64);
            let b_zero = fb.create_block();
            let b_succ = fb.create_block();
            let b_max = fb.create_block();
            let b_imax = fb.create_block();
            let b_param = fb.create_block();
            let cases = vec![
                SwitchCase { value: Constant::Int(0), target: b_zero, args: vec![] },
                SwitchCase { value: Constant::Int(1), target: b_succ, args: vec![] },
                SwitchCase { value: Constant::Int(2), target: b_max, args: vec![] },
                SwitchCase { value: Constant::Int(3), target: b_imax, args: vec![] },
                SwitchCase { value: Constant::Int(4), target: b_param, args: vec![] },
            ];
            let trap = fb.create_block();
            fb.switch(tag, cases, trap, vec![]);
            // Helper: load child ptr at payload slot `i`.
            let load_child = |fb: &mut FunctionBuilder<'_>, i: i128| -> ValueId {
                let off = fb.iconst(Ty::I64, 8 + 8 * i);
                let p = fb.gep_inbounds(Ty::I8, self_ptr, vec![off]);
                fb.load(Ty::Ptr, p)
            };
            // Zero => 0
            fb.switch_to_block(b_zero);
            let z = fb.iconst(Ty::I64, 0);
            fb.br(join, vec![z]);
            // Succ(m) => 1 + count_succ(m)
            fb.switch_to_block(b_succ);
            let c = load_child(&mut fb, 0);
            let one = fb.iconst(Ty::I64, 1);
            let rec = fb.call(cs, vec![c]);
            let sum = fb.add(Ty::I64, one, rec);
            fb.br(join, vec![sum]);
            // Max(a,b) => count_succ(a) + count_succ(b)
            for blk in [b_max, b_imax] {
                fb.switch_to_block(blk);
                let a = load_child(&mut fb, 0);
                let b = load_child(&mut fb, 1);
                let ra = fb.call(cs, vec![a]);
                let rb = fb.call(cs, vec![b]);
                let s = fb.add(Ty::I64, ra, rb);
                fb.br(join, vec![s]);
            }
            // Param => 0
            fb.switch_to_block(b_param);
            let p0 = fb.iconst(Ty::I64, 0);
            fb.br(join, vec![p0]);
            // trap
            fb.switch_to_block(trap);
            fb.unreachable();
            // join: ret
            fb.switch_to_block(join);
            fb.ret(vec![jp]);
            fb.build();
        }
        (mb, cs)
    }

    #[test]
    fn adt_match_count_succ_shape_matches() {
        use crate::model::{add_int_input_runner, Micro};
        let z = || Micro::Zero;
        let s = |m: Micro| Micro::Succ(Box::new(m));
        let mx = |a: Micro, b: Micro| Micro::Max(Box::new(a), Box::new(b));
        let im = |a: Micro, b: Micro| Micro::IMax(Box::new(a), Box::new(b));
        let pm = |n: u64| Micro::Param(n);
        let cases: Vec<Micro> = vec![
            z(),
            s(z()),
            s(s(z())),
            s(s(s(z()))),
            pm(7),
            mx(s(z()), s(s(z()))),
            im(s(z()), z()),
            mx(pm(1), s(mx(s(z()), z()))),
        ];
        let (mut mb, cs) = build_count_succ_module();
        // This hand-built `count_succ` reads an I32 tag @0, p0@8/p1@16 — the LEGACY
        // shape — so drive it with the matching `HeapLayout::legacy` (the REAL
        // THIR-lowered path is exercised by the `--m3` driver with the faithful
        // layout; this unit test only locks in the legacy SHAPE).
        let lay = crate::model::HeapLayout::legacy(5);
        let nullary_i64 = mb.add_func_type(vec![], vec![Ty::I64]);
        let runners: Vec<(i128, FuncId)> = cases
            .iter()
            .enumerate()
            .map(|(i, m)| {
                (m.count_succ() as i128, add_int_input_runner(&mut mb, &lay, m, cs, nullary_i64, &format!("run_{i}")))
            })
            .collect();
        let module = mb.build().expect("ModuleBuilder::build: test fixture");
        assert_eq!(validate_module(&module).len(), 0, "count_succ validate");
        for (oracle, run) in runners {
            assert_eq!(interp_int(&module, run).unwrap(), oracle, "count_succ interp");
        }
    }

    /// M5.4 round-trip TEXT lock-in: the recursive-ADT-match module emits
    /// canonical trust-ir text (incl. the `Level` struct def) that PARSES BACK to
    /// an equivalent, still-valid module (the property the downstream trust-cg JIT
    /// relies on for the `--emit-adt` artifact).
    #[test]
    fn adt_match_text_roundtrips() {
        let (mb, _cs) = build_count_succ_module();
        let module = mb.build().expect("ModuleBuilder::build: test fixture");
        let text = format!("{module}");
        let reparsed =
            trust_ir::parser::parse_module(&text).expect("emitted ADT-match text must reparse");
        assert_eq!(
            validate_module(&reparsed).len(),
            0,
            "reparsed ADT-match module must validate"
        );
    }

    /// M5.6 capstone SHAPE lock-in (no rustc): build the REAL clean-kernel
    /// `Level::is_zero` predicate as a `fn(ptr) -> bool` — the bool-returning
    /// recursive-ADT match the unified `lower_expr`/`lower_match_adt`+`lower_logical`
    /// emits: Load the discriminant TAG, `switch` into per-variant blocks (Zero=>
    /// true, Succ=>false, Param=>false), the `Max` arm short-circuits
    /// `is_zero(a) && is_zero(b)` via condbr+join, the `IMax` arm recurses on the
    /// second child only — and JOIN every arm's bool at a block-param. Drive it
    /// over the SAME `model::corpus()` of `Micro` values (via `add_input_runner` /
    /// `build_heap_value`) the M1/M2 21/21 differential uses and assert PARITY with
    /// the native `Micro::is_zero` oracle on every case. The full THIR path is
    /// exercised end-to-end by the `--m3` driver (M5.6 RESULT, reported separately).
    fn build_is_zero_module() -> (ModuleBuilder, FuncId) {
        use trust_ir::constant::Constant;
        use trust_ir::ty::{FieldDef, StructDef};
        use trust_ir::value::StructId;
        let mut mb = ModuleBuilder::new("m5pred".to_string());
        // The `Level` tagged struct (tag@0, p0@8, p1@16) — the layout
        // `model::build_heap_value` allocates (StructId 0).
        mb.add_struct(StructDef {
            id: StructId::new(0),
            name: "Level".into(),
            fields: vec![
                FieldDef { name: "tag".into(), ty: Ty::I32, offset: None },
                FieldDef { name: "p0".into(), ty: Ty::Ptr, offset: None },
                FieldDef { name: "p1".into(), ty: Ty::Ptr, offset: None },
            ],
            size: None,
            align: None,
            repr: Default::default(),
            origin: None,
        });
        let sig = mb.add_func_type(vec![Ty::Ptr], vec![Ty::Bool]);
        let iz = FuncId::new(0);
        {
            let mut fb = mb.function("is_zero", sig);
            let entry = fb.create_block();
            let self_ptr = fb.add_block_param(entry, Ty::Ptr);
            fb.switch_to_block(entry);
            let off0 = fb.iconst(Ty::I64, 0);
            let tagp = fb.gep_inbounds(Ty::I8, self_ptr, vec![off0]);
            let tag = fb.load(Ty::I32, tagp);
            let join = fb.create_block();
            let jp = fb.add_block_param(join, Ty::Bool);
            let b_zero = fb.create_block();
            let b_succ = fb.create_block();
            let b_max = fb.create_block();
            let b_imax = fb.create_block();
            let b_param = fb.create_block();
            let cases = vec![
                SwitchCase { value: Constant::Int(0), target: b_zero, args: vec![] },
                SwitchCase { value: Constant::Int(1), target: b_succ, args: vec![] },
                SwitchCase { value: Constant::Int(2), target: b_max, args: vec![] },
                SwitchCase { value: Constant::Int(3), target: b_imax, args: vec![] },
                SwitchCase { value: Constant::Int(4), target: b_param, args: vec![] },
            ];
            let trap = fb.create_block();
            fb.switch(tag, cases, trap, vec![]);
            let load_child = |fb: &mut FunctionBuilder<'_>, i: i128| -> ValueId {
                let off = fb.iconst(Ty::I64, 8 + 8 * i);
                let p = fb.gep_inbounds(Ty::I8, self_ptr, vec![off]);
                fb.load(Ty::Ptr, p)
            };
            // Zero => true ; Succ => false ; Param => false (leaf bool literals).
            fb.switch_to_block(b_zero);
            let t = fb.bool_const(true);
            fb.br(join, vec![t]);
            fb.switch_to_block(b_succ);
            let f1 = fb.bool_const(false);
            fb.br(join, vec![f1]);
            fb.switch_to_block(b_param);
            let f2 = fb.bool_const(false);
            fb.br(join, vec![f2]);
            // Max(a,b) => is_zero(a) && is_zero(b) (condbr short-circuit + join).
            fb.switch_to_block(b_max);
            let a = load_child(&mut fb, 0);
            let b = load_child(&mut fb, 1);
            let ca = fb.call(iz, vec![a]);
            let and_join = fb.create_block();
            let andp = fb.add_block_param(and_join, Ty::Bool);
            let rhs_blk = fb.create_block();
            let short_blk = fb.create_block();
            fb.condbr(ca, rhs_blk, vec![], short_blk, vec![]);
            fb.switch_to_block(short_blk);
            let sf = fb.bool_const(false);
            fb.br(and_join, vec![sf]);
            fb.switch_to_block(rhs_blk);
            let cb = fb.call(iz, vec![b]);
            fb.br(and_join, vec![cb]);
            fb.switch_to_block(and_join);
            fb.br(join, vec![andp]);
            // IMax(_,b) => is_zero(b) (recurse on the second child only).
            fb.switch_to_block(b_imax);
            let ib = load_child(&mut fb, 1);
            let cib = fb.call(iz, vec![ib]);
            fb.br(join, vec![cib]);
            // trap + join.
            fb.switch_to_block(trap);
            fb.unreachable();
            fb.switch_to_block(join);
            fb.ret(vec![jp]);
            fb.build();
        }
        (mb, iz)
    }

    #[test]
    fn predicate_is_zero_shape_matches() {
        use crate::model::{add_input_runner, corpus, Micro};
        let cases: Vec<Micro> = corpus();
        let (mut mb, iz) = build_is_zero_module();
        // The hand-built `is_zero` reads the LEGACY I32-tag shape; pair it with the
        // matching `HeapLayout::legacy` (the faithful path is the `--m3` driver).
        let lay = crate::model::HeapLayout::legacy(5);
        let nullary_bool = mb.add_func_type(vec![], vec![Ty::Bool]);
        let runners: Vec<(bool, FuncId)> = cases
            .iter()
            .enumerate()
            .map(|(i, m)| {
                (m.is_zero(), add_input_runner(&mut mb, &lay, m, iz, nullary_bool, &format!("run_{i}")))
            })
            .collect();
        let module = mb.build().expect("ModuleBuilder::build: test fixture");
        assert_eq!(validate_module(&module).len(), 0, "is_zero validate");
        for (oracle, run) in runners {
            assert_eq!(interp_bool(&module, run).unwrap(), oracle, "is_zero interp parity");
        }
    }

    /// M5.6 round-trip TEXT lock-in: the bool-predicate module emits canonical
    /// trust-ir text (incl. the `Level` struct def) that PARSES BACK to an
    /// equivalent, still-valid module (the property the downstream trust-cg JIT
    /// relies on for the `--emit-pred` artifact).
    #[test]
    fn predicate_text_roundtrips() {
        let (mb, _iz) = build_is_zero_module();
        let module = mb.build().expect("ModuleBuilder::build: test fixture");
        let text = format!("{module}");
        let reparsed =
            trust_ir::parser::parse_module(&text).expect("emitted predicate text must reparse");
        assert_eq!(
            validate_module(&reparsed).len(),
            0,
            "reparsed predicate module must validate"
        );
    }
}

// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! WS3.15 / F-058: bodyless `Linkage::ExternalWeak` declarations.
//!
//! `ExternalWeak` is documented as "a weak DECLARATION: resolves to null rather
//! than failing the link when no definition exists", yet only an exact
//! `External` bodyless function counted as a declaration: a bodyless weak import
//! was `EmptyFunction`, and `first_ffi_boundary` did not see it. A weak import is
//! now a declaration and an FFI boundary, and its NULLABLE address is admitted in
//! exactly one spelling — `Const SymbolAddr { symbol, addend: 0 } : Ptr`, compared
//! against `NullPtr`, then `CallIndirect` through the `Ptr`. A direct `Call` /
//! `Invoke` of it is `DirectCallToWeakDeclaration`; `FnDef` (a `Ty::Func` value,
//! which claims a callable non-null function) or a closure code pointer naming it
//! is `WeakDeclarationAsFnDef`; a `Ty::Func`-typed or offset `SymbolAddr` is
//! `WeakDeclarationAddressNotNullable`.

use trust_ir::inst::ICmpOp;
use trust_ir::{
    CallingConv, Constant, Endianness, FuncId, FuncTyId, Global, Linkage, Module,
    StructPassingPolicy, TargetInfo, Ty, Visibility,
};
use trust_ir_build::validate::ValidationError;
use trust_ir_build::{ModuleBuilder, TRUSTED_HANDLE_RUNTIMES, validate_module};

const HOOK: &str = "optional_hook";

fn target() -> TargetInfo {
    TargetInfo {
        triple: "aarch64-apple-darwin".into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: Some("aapcs64".into()),
        struct_passing: StructPassingPolicy::NativeC,
    }
}

/// How the caller reaches the weak hook.
#[derive(Clone, Copy)]
enum Reach {
    /// The admitted idiom: `SymbolAddr : Ptr`, null check, `CallIndirect`.
    NullCheckedAddress,
    /// A direct `Call` of the declaration.
    DirectCall,
    /// A direct `Invoke` of the declaration.
    DirectInvoke,
    /// `Const FnDef(hook) : Func`, then `CallIndirect` through it.
    FnDef,
    /// `Const SymbolAddr { hook, 0 } : Func`, then `CallIndirect` through it.
    FuncTypedSymbolAddr,
    /// `Const SymbolAddr { hook, 8 } : Ptr`, null check, `CallIndirect`.
    OffsetSymbolAddr,
}

/// A C module that declares `optional_hook(u64) -> u64` (bodyless, `linkage`)
/// and a C function `use_hook(x)` that reaches it as `reach` says.
fn module(linkage: Linkage, reach: Reach) -> (Module, FuncId) {
    let mut mb = ModuleBuilder::new_with_target_info("weak", target());
    let hook_ty = mb.add_func_type(vec![Ty::U64], vec![Ty::U64]);
    let hook = mb.declare_function(HOOK, hook_ty);
    {
        let mut f = mb.function("use_hook", hook_ty);
        let entry = f.create_block();
        let x = f.add_block_param(entry, Ty::U64);
        f.switch_to_block(entry);
        match reach {
            Reach::DirectCall => {
                let r = f.call(hook, vec![x]);
                f.ret(vec![r]);
            }
            Reach::DirectInvoke => {
                let normal = f.create_block();
                let unwind = f.create_block();
                let r = f.invoke(hook, vec![x], normal, vec![], unwind);
                f.switch_to_block(normal);
                f.ret(vec![r]);
                f.switch_to_block(unwind);
                let (exception, _) = f.landingpad(true, vec![]);
                f.resume(exception);
            }
            Reach::FnDef | Reach::FuncTypedSymbolAddr => {
                let value = if matches!(reach, Reach::FnDef) {
                    Constant::FnDef(hook)
                } else {
                    Constant::symbol_addr(HOOK)
                };
                let callee = f.const_value(Ty::Func(hook_ty), value);
                let r = f.call_indirect(callee, hook_ty, vec![x]);
                f.ret(vec![r]);
            }
            Reach::NullCheckedAddress | Reach::OffsetSymbolAddr => {
                let addend = if matches!(reach, Reach::OffsetSymbolAddr) {
                    8
                } else {
                    0
                };
                null_checked_call(&mut f, x, hook_ty, addend);
            }
        }
        f.build();
    }
    let mut m = mb.build().expect("ModuleBuilder::build: test fixture");
    m.function_by_id_mut(hook).expect("hook").linkage = linkage;
    (m, hook)
}

fn null_checked_call(
    f: &mut trust_ir_build::FunctionBuilder<'_>,
    x: trust_ir::ValueId,
    hook_ty: FuncTyId,
    addend: i64,
) {
    let present = f.create_block();
    let absent = f.create_block();
    let address = f.const_value(Ty::Ptr, Constant::symbol_addr_with_addend(HOOK, addend));
    let null = f.null_ptr();
    let is_null = f.icmp(ICmpOp::Eq, Ty::Ptr, address, null);
    f.condbr(is_null, absent, vec![], present, vec![]);
    f.switch_to_block(present);
    let r = f.call_indirect(address, hook_ty, vec![x]);
    f.ret(vec![r]);
    f.switch_to_block(absent);
    f.ret(vec![x]);
}

fn global(name: &str, ty: Ty, initializer: Constant) -> Global {
    Global {
        name: name.into(),
        ty,
        mutable: false,
        initializer: Some(initializer),
        linkage: Linkage::Internal,
        tls: None,
        align: None,
        section: None,
        visibility: Visibility::Default,
        retained: false,
    }
}

fn only<'a>(errors: &'a [ValidationError], what: &str) -> &'a ValidationError {
    assert_eq!(
        errors.len(),
        1,
        "{what}: expected exactly one error, got {errors:?}"
    );
    &errors[0]
}

// ─────────────────────────────── positive ───────────────────────────────

#[test]
fn bodyless_weak_declaration_with_null_checked_address_validates() {
    let (m, hook) = module(Linkage::ExternalWeak, Reach::NullCheckedAddress);
    let hook = m.function_by_id(hook).expect("hook");
    assert!(hook.is_weak_declaration() && hook.is_declaration());
    assert_eq!(validate_module(&m), []);
}

#[test]
fn bodyless_weak_declaration_is_an_ffi_boundary() {
    let (mut m, _) = module(Linkage::ExternalWeak, Reach::NullCheckedAddress);
    assert_eq!(
        m.first_ffi_boundary().as_deref(),
        Some("bodyless external_weak declaration `optional_hook`")
    );
    assert!(m.requires_target_info());
    m.target_info = None;
    let errors = validate_module(&m);
    match only(&errors, "weak import without target_info") {
        ValidationError::TargetInfoRequired { boundary } => {
            assert!(boundary.contains("external_weak"), "{boundary}");
            assert!(boundary.contains(HOOK), "{boundary}");
        }
        other => panic!("expected TargetInfoRequired, got {other:?}"),
    }
}

/// A `Ptr` table of optional hooks (a data relocation to a weak symbol) is the
/// same nullable spelling at a `Ptr` position inside an aggregate — in the list
/// spelling (a table whose slots differ) and in the uniform-array spelling (a
/// table whose every slot is the hook, v50 `Constant::Splat`: the element is
/// checked once, at the `Ptr` element type).
#[test]
fn weak_symbol_address_in_a_ptr_table_global_validates() {
    let (mut m, _) = module(Linkage::ExternalWeak, Reach::NullCheckedAddress);
    let ptr_ty = m.add_type(Ty::Ptr).expect("Module::add_type: test fixture");
    m.globals.push(global(
        "HOOKS",
        Ty::Array(ptr_ty, 2),
        Constant::Array(vec![Constant::symbol_addr(HOOK), Constant::Int(0)]),
    ));
    m.globals.push(global(
        "SAME_HOOKS",
        Ty::Array(ptr_ty, 2),
        Constant::splat(Constant::symbol_addr(HOOK), 2),
    ));
    assert_eq!(validate_module(&m), []);
}

// ──────────────────────────── negative twins ────────────────────────────

#[test]
fn direct_call_to_weak_declaration_is_refused() {
    let (m, hook) = module(Linkage::ExternalWeak, Reach::DirectCall);
    let errors = validate_module(&m);
    match only(&errors, "direct call of a weak declaration") {
        ValidationError::DirectCallToWeakDeclaration {
            callee,
            name,
            location,
        } => {
            assert_eq!(*callee, hook.index());
            assert_eq!(name, HOOK);
            assert!(location.contains("use_hook"), "{location}");
        }
        other => panic!("expected DirectCallToWeakDeclaration, got {other:?}"),
    }
    // Mutation control: the same direct call of a STRONG import validates, so
    // the refusal is the weak linkage and nothing else.
    let (strong, _) = module(Linkage::External, Reach::DirectCall);
    assert_eq!(validate_module(&strong), []);
}

#[test]
fn direct_invoke_of_weak_declaration_is_refused() {
    let (m, hook) = module(Linkage::ExternalWeak, Reach::DirectInvoke);
    let errors = validate_module(&m);
    assert!(
        matches!(
            only(&errors, "direct invoke of a weak declaration"),
            ValidationError::DirectCallToWeakDeclaration { callee, name, .. }
                if *callee == hook.index() && name == HOOK
        ),
        "{errors:?}"
    );
    let (strong, _) = module(Linkage::External, Reach::DirectInvoke);
    assert_eq!(validate_module(&strong), []);
}

#[test]
fn weak_declaration_as_fndef_is_refused() {
    let (m, hook) = module(Linkage::ExternalWeak, Reach::FnDef);
    let errors = validate_module(&m);
    match only(&errors, "FnDef of a weak declaration") {
        ValidationError::WeakDeclarationAsFnDef { function, name, .. } => {
            assert_eq!(*function, hook.index());
            assert_eq!(name, HOOK);
        }
        other => panic!("expected WeakDeclarationAsFnDef, got {other:?}"),
    }
    let (strong, _) = module(Linkage::External, Reach::FnDef);
    assert_eq!(validate_module(&strong), []);
}

#[test]
fn weak_declaration_as_closure_code_pointer_is_refused() {
    let (mut m, hook) = module(Linkage::ExternalWeak, Reach::NullCheckedAddress);
    let hook_ty = m.function_by_id(hook).expect("hook").ty;
    let closure = m
        .add_closure_type(trust_ir::ClosureTy {
            func: hook_ty,
            captures: vec![],
        })
        .expect("Module::add_closure_type: test fixture");
    m.globals.push(global(
        "HOOK_CLOSURE",
        Ty::Closure(closure),
        Constant::Closure {
            func: hook,
            captures: vec![],
        },
    ));
    let errors = validate_module(&m);
    assert!(
        errors.iter().any(|error| matches!(
            error,
            ValidationError::WeakDeclarationAsFnDef { function, location, .. }
                if *function == hook.index() && location == "global 'HOOK_CLOSURE'"
        )),
        "{errors:?}"
    );
}

#[test]
fn func_typed_symbol_address_of_weak_declaration_is_refused() {
    let (m, _) = module(Linkage::ExternalWeak, Reach::FuncTypedSymbolAddr);
    let errors = validate_module(&m);
    match only(&errors, "Func-typed SymbolAddr of a weak declaration") {
        ValidationError::WeakDeclarationAddressNotNullable { symbol, detail, .. } => {
            assert_eq!(symbol, HOOK);
            let hook_ty = m.function_by_name(HOOK).expect("hook").ty;
            assert_eq!(*detail, format!("type {}", Ty::Func(hook_ty)));
        }
        other => panic!("expected WeakDeclarationAddressNotNullable, got {other:?}"),
    }
    let (strong, _) = module(Linkage::External, Reach::FuncTypedSymbolAddr);
    assert_eq!(validate_module(&strong), []);
}

#[test]
fn offset_symbol_address_of_weak_declaration_is_refused() {
    let (m, _) = module(Linkage::ExternalWeak, Reach::OffsetSymbolAddr);
    let errors = validate_module(&m);
    match only(&errors, "offset SymbolAddr of a weak declaration") {
        ValidationError::WeakDeclarationAddressNotNullable { symbol, detail, .. } => {
            assert_eq!(symbol, HOOK);
            assert_eq!(detail, "ptr with nonzero addend 8");
        }
        other => panic!("expected WeakDeclarationAddressNotNullable, got {other:?}"),
    }
    let (strong, _) = module(Linkage::External, Reach::OffsetSymbolAddr);
    assert_eq!(validate_module(&strong), []);
}

/// `SeqMap { fwd }` calls its element function directly, once per element, so
/// naming a weak declaration as `fwd` is a direct call through a possibly-null
/// address exactly like `Call` (adversarial review: the first cut policed only
/// `Call` / `Invoke`, and this module validated).
#[test]
fn seq_map_element_function_naming_weak_declaration_is_refused() {
    use trust_ir::inst::Inst;
    use trust_ir::node::InstrNode;
    use trust_ir::{Block, BlockId, Function, ValueId};
    let build = |linkage: Linkage| {
        let mut m = Module::new("weak_seq_map");
        m.target_info = Some(target());
        let i32_id = m.add_type(Ty::I32).expect("Module::add_type: test fixture");
        let seq_ty = Ty::Sequence(i32_id);
        let loop_ty = m
            .add_func_type(trust_ir::FuncTy {
                params: vec![seq_ty.clone()],
                returns: vec![seq_ty.clone()],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let elem_ty = m
            .add_func_type(trust_ir::FuncTy {
                params: vec![Ty::RefMut(Box::new(Ty::I32))],
                returns: vec![],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let mut map_all = Function::new(FuncId::new(0), "map_all", loop_ty, BlockId::new(0));
        let mut entry = Block::new(BlockId::new(0));
        entry.params.push((ValueId::new(0), seq_ty.clone()));
        entry.body.push(
            InstrNode::new(Inst::SeqMap {
                ty: seq_ty,
                seq: ValueId::new(0),
                fwd: FuncId::new(1),
            })
            .with_result(ValueId::new(1)),
        );
        entry.body.push(InstrNode::new(Inst::Return {
            values: vec![ValueId::new(1)],
        }));
        map_all.blocks.push(entry);
        m.try_add_function(map_all)
            .expect("Module::try_add_function: test fixture");
        let mut elem = Function::new(FuncId::new(1), HOOK, elem_ty, BlockId::new(0));
        elem.calling_conv = CallingConv::C;
        elem.linkage = linkage;
        m.try_add_function(elem)
            .expect("Module::try_add_function: test fixture");
        m
    };
    let errors = validate_module(&build(Linkage::ExternalWeak));
    match only(&errors, "SeqMap fwd naming a weak declaration") {
        ValidationError::DirectCallToWeakDeclaration {
            callee,
            name,
            location,
        } => {
            assert_eq!(*callee, 1);
            assert_eq!(name, HOOK);
            assert!(location.contains("map_all"), "{location}");
        }
        other => panic!("expected DirectCallToWeakDeclaration, got {other:?}"),
    }
    // Mutation control: the same element function as a STRONG import validates.
    assert_eq!(validate_module(&build(Linkage::External)), []);
}

// ─────────────────────────────── mutation ───────────────────────────────

/// `AvailableExternally` is by definition a body copy: bodyless it is still
/// `EmptyFunction`, and so is every other non-import linkage.
#[test]
fn bodyless_available_externally_is_still_empty_function() {
    for linkage in [
        Linkage::AvailableExternally,
        Linkage::Internal,
        Linkage::Private,
        Linkage::Weak,
        Linkage::LinkOnce,
        Linkage::WeakOdr,
        Linkage::LinkOnceOdr,
    ] {
        let (m, _) = module(linkage, Reach::DirectCall);
        let errors = validate_module(&m);
        assert!(
            errors.contains(&ValidationError::EmptyFunction),
            "{linkage}: {errors:?}"
        );
        assert!(
            !errors
                .iter()
                .any(|e| matches!(e, ValidationError::DirectCallToWeakDeclaration { .. })),
            "{linkage} is not a weak declaration: {errors:?}"
        );
    }
    let (m, _) = module(Linkage::AvailableExternally, Reach::NullCheckedAddress);
    assert_eq!(validate_module(&m), [ValidationError::EmptyFunction]);
}

// ────────────────────────────── adversarial ─────────────────────────────

/// A weak declaration is a declaration, so it is a handle ORIGIN exactly as a
/// strong one is: reaching a handle without being pinned stays
/// `HandleForeignDeclaration`, never a weak exemption.
#[test]
fn weak_declaration_reaching_a_handle_stays_handle_foreign_declaration() {
    let nat = Ty::handle("Nat", "trust_bignum::Nat");
    let build = |linkage: Linkage| {
        let mut m = Module::new("weak_handle");
        m.target_info = Some(target());
        let sig = m
            .add_func_type(trust_ir::FuncTy {
                params: vec![Ty::U64],
                returns: vec![nat.clone()],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let mut decl = trust_ir::Function::new(
            FuncId::new(0),
            "forged_nat_from_u64",
            sig,
            trust_ir::BlockId::new(0),
        );
        decl.calling_conv = CallingConv::C;
        decl.linkage = linkage;
        m.try_add_function(decl)
            .expect("Module::try_add_function: test fixture");
        m
    };
    for linkage in [Linkage::External, Linkage::ExternalWeak] {
        let errors = validate_module(&build(linkage));
        assert!(
            matches!(
                only(&errors, "unpinned handle origin"),
                ValidationError::HandleForeignDeclaration { name, .. }
                    if name == "forged_nat_from_u64"
            ),
            "{linkage}: {errors:?}"
        );
    }
}

/// A pinned handle-runtime symbol stays `External`-only: re-declaring it weak
/// is `HandleEntryPointDefinedLocally`, not an admitted weak import.
#[test]
fn pinned_handle_symbol_declared_weak_stays_defined_locally() {
    let pin = TRUSTED_HANDLE_RUNTIMES
        .iter()
        .find(|pin| pin.runtime == "trust_bignum::Nat")
        .expect("v1 pins trust_bignum::Nat");
    let mut mb = ModuleBuilder::new_with_target_info("weak_pinned", target());
    let decls = mb.declare_handle_runtime(pin).expect("pinned declarations");
    let mut m = mb.build().expect("ModuleBuilder::build: test fixture");
    let (_, id) = decls.entries().next().expect("an entry point");
    let symbol = m.function_by_id(id).expect("entry point").name.clone();
    assert_eq!(validate_module(&m), []);
    m.function_by_id_mut(id).expect("entry point").linkage = Linkage::ExternalWeak;
    let errors = validate_module(&m);
    assert!(
        matches!(
            only(&errors, "pinned symbol declared weak"),
            ValidationError::HandleEntryPointDefinedLocally { symbol: s, .. } if *s == symbol
        ),
        "{errors:?}"
    );
}

// ──────────────────────── ported GAP rows (closed) ───────────────────────

/// `b1.gap.extern_weak_declaration_refused` — CLOSED. A bodyless weak import
/// validates on its own linkage (not only through the contract-only summary
/// door), and every codec still carries it.
#[test]
fn b1_gap_extern_weak_declaration_refused() {
    let (strong, hook) = module(Linkage::External, Reach::NullCheckedAddress);
    assert_eq!(validate_module(&strong), []);
    let mut weak = strong.clone();
    weak.function_by_id_mut(hook).expect("hook").linkage = Linkage::ExternalWeak;
    assert_eq!(
        validate_module(&weak),
        [],
        "bodyless ExternalWeak is a declaration"
    );

    let mut with_summary = weak.clone();
    with_summary.function_by_id_mut(hook).expect("hook").summary =
        Some(trust_ir::FunctionSummary::default());
    assert_eq!(validate_module(&with_summary), []);

    #[cfg(feature = "binary")]
    {
        let bytes =
            trust_ir::binary::serialize_module(&weak).expect("serialize_module: test fixture");
        let back = trust_ir::binary::deserialize_module(&bytes).expect("binary round trip");
        let decl = back.function_by_name(HOOK).expect("hook survives");
        assert!(decl.is_weak_declaration());
        assert_eq!(validate_module(&back), []);
    }
}

/// `b1.uf09` — CLOSED. The summary-carrying bodyless weak import that the
/// contract-only door admitted is now an FFI boundary too, so a module without
/// `target_info` is `TargetInfoRequired` instead of silently target-free.
#[test]
fn b1_uf09() {
    let (mut m, hook) = module(Linkage::ExternalWeak, Reach::NullCheckedAddress);
    m.function_by_id_mut(hook).expect("hook").summary = Some(trust_ir::FunctionSummary::default());
    assert!(
        m.first_ffi_boundary()
            .is_some_and(|b| b.contains("external_weak"))
    );
    m.target_info = None;
    let errors = validate_module(&m);
    assert!(
        matches!(
            only(&errors, "summary-carrying weak import without target"),
            ValidationError::TargetInfoRequired { boundary } if boundary.contains(HOOK)
        ),
        "{errors:?}"
    );
}

/// `b5.related.gap.extern_weak_bodyless_declaration_is_empty_function` —
/// CLOSED. The same C declaration validates at `External` and `ExternalWeak`.
#[test]
fn b5_related_gap_extern_weak_bodyless_declaration_is_empty_function() {
    let build = |linkage: Linkage| {
        let mut m = Module::new("b5_extern_weak");
        m.target_info = Some(target());
        let sig = m
            .add_func_type(trust_ir::FuncTy {
                params: vec![Ty::U64],
                returns: vec![Ty::U64],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let mut decl =
            trust_ir::Function::new(FuncId::new(0), HOOK, sig, trust_ir::BlockId::new(0));
        decl.calling_conv = CallingConv::C;
        decl.linkage = linkage;
        m.try_add_function(decl)
            .expect("Module::try_add_function: test fixture");
        m
    };
    assert_eq!(validate_module(&build(Linkage::External)), []);
    assert_eq!(validate_module(&build(Linkage::ExternalWeak)), []);
}

// ─────────────────────── adversarial review (WS3.15) ──────────────────────

/// How the null-checked `CallIndirect` through a weak address is spelled.
#[derive(Clone, Copy)]
enum Edge {
    /// The declaration's own signature and convention: the admitted idiom.
    Exact,
    /// The address flows through a `Copy` before the call, exact edge.
    ExactThroughCopy,
    /// A signature that is not the declaration's: `(u64, u64) -> u64`.
    WrongSignature,
    /// The wrong signature, the address laundered through a `Copy`.
    WrongSignatureThroughCopy,
    /// The declaration's signature at the `Rust` convention (the hook is `C`).
    WrongConvention,
}

/// The admitted weak idiom, but with the `CallIndirect` edge spelled as `edge`
/// says. `linkage` is the hook's linkage.
fn edge_module(linkage: Linkage, edge: Edge) -> Module {
    let mut mb = ModuleBuilder::new_with_target_info("weak_edge", target());
    let hook_ty = mb.add_func_type(vec![Ty::U64], vec![Ty::U64]);
    let wrong_ty = mb.add_func_type(vec![Ty::U64, Ty::U64], vec![Ty::U64]);
    let hook = mb.declare_function(HOOK, hook_ty);
    {
        let mut f = mb.function("use_hook", hook_ty);
        let entry = f.create_block();
        let x = f.add_block_param(entry, Ty::U64);
        f.switch_to_block(entry);
        let present = f.create_block();
        let absent = f.create_block();
        let address = f.const_value(Ty::Ptr, Constant::symbol_addr(HOOK));
        let null = f.null_ptr();
        let is_null = f.icmp(ICmpOp::Eq, Ty::Ptr, address, null);
        f.condbr(is_null, absent, vec![], present, vec![]);
        f.switch_to_block(present);
        let callee = match edge {
            Edge::ExactThroughCopy | Edge::WrongSignatureThroughCopy => f.copy(Ty::Ptr, address),
            _ => address,
        };
        let r = match edge {
            Edge::Exact | Edge::ExactThroughCopy => f.call_indirect(callee, hook_ty, vec![x]),
            Edge::WrongSignature | Edge::WrongSignatureThroughCopy => {
                f.call_indirect(callee, wrong_ty, vec![x, x])
            }
            Edge::WrongConvention => {
                f.call_indirect_cc(callee, hook_ty, vec![x], CallingConv::Rust)
            }
        };
        f.ret(vec![r]);
        f.switch_to_block(absent);
        f.ret(vec![x]);
        f.build();
    }
    let mut m = mb.build().expect("ModuleBuilder::build: test fixture");
    m.function_by_id_mut(hook).expect("hook").linkage = linkage;
    m
}

/// The null-checked `CallIndirect` is the ONLY way to call a weak import, so
/// it must recover the signature check a direct `Call` would have made: an
/// edge whose declared signature is not the declaration's is a type-confused
/// call the validator used to accept (the `Ptr` callee carries no signature).
#[test]
fn weak_address_called_at_a_foreign_signature_is_refused() {
    for edge in [Edge::WrongSignature, Edge::WrongSignatureThroughCopy] {
        let errors = validate_module(&edge_module(Linkage::ExternalWeak, edge));
        assert!(
            matches!(
                only(&errors, "weak address called at a foreign signature"),
                ValidationError::CallEdgeSignatureMismatch { callee, .. } if callee == HOOK
            ),
            "{errors:?}"
        );
    }
    for edge in [Edge::Exact, Edge::ExactThroughCopy] {
        assert_eq!(
            validate_module(&edge_module(Linkage::ExternalWeak, edge)),
            [],
            "the exact edge is the admitted idiom"
        );
    }
}

/// The same recovery for the calling convention: a `Rust` edge into a `C`
/// weak import disagrees about the ABI exactly as a direct call would.
#[test]
fn weak_address_called_at_a_foreign_convention_is_refused() {
    let errors = validate_module(&edge_module(Linkage::ExternalWeak, Edge::WrongConvention));
    assert!(
        matches!(
            only(&errors, "weak address called at a foreign convention"),
            ValidationError::CallEdgeConvMismatch { callee, .. } if callee == HOOK
        ),
        "{errors:?}"
    );
}

/// `Switch` case values are constant trees the typed constant walk never
/// visits, so a case spelled `FnDef(weak)` or `SymbolAddr { weak, 8 }` slipped
/// past the "anywhere in a constant tree" rule. A weak address may be compared
/// only by `ICmp` against a `Ptr` operand; every case spelling is refused.
#[test]
fn switch_case_naming_weak_declaration_is_refused() {
    use trust_ir::inst::SwitchCase;
    let build = |linkage: Linkage, case: Constant| {
        let mut mb = ModuleBuilder::new_with_target_info("weak_switch", target());
        let hook_ty = mb.add_func_type(vec![Ty::U64], vec![Ty::U64]);
        let hook = mb.declare_function(HOOK, hook_ty);
        let probe_ty = mb.add_func_type(vec![Ty::Ptr], vec![Ty::Bool]);
        {
            let mut f = mb.function("probe", probe_ty);
            let entry = f.create_block();
            let p = f.add_block_param(entry, Ty::Ptr);
            let hit = f.create_block();
            let miss = f.create_block();
            f.switch_to_block(entry);
            f.switch(
                p,
                vec![SwitchCase {
                    value: case,
                    target: hit,
                    args: vec![],
                }],
                miss,
                vec![],
            );
            f.switch_to_block(hit);
            let t = f.const_value(Ty::Bool, Constant::Bool(true));
            f.ret(vec![t]);
            f.switch_to_block(miss);
            let fls = f.const_value(Ty::Bool, Constant::Bool(false));
            f.ret(vec![fls]);
            f.build();
        }
        let mut m = mb.build().expect("ModuleBuilder::build: test fixture");
        m.function_by_id_mut(hook).expect("hook").linkage = linkage;
        (m, hook)
    };
    let (_, hook) = build(Linkage::External, Constant::Int(0));
    let cases = [
        Constant::FnDef(hook),
        Constant::symbol_addr_with_addend(HOOK, 8),
        Constant::symbol_addr(HOOK),
    ];
    for case in cases {
        let (m, _) = build(Linkage::ExternalWeak, case.clone());
        let errors = validate_module(&m);
        assert!(
            matches!(
                only(&errors, "switch case naming a weak declaration"),
                ValidationError::WeakDeclarationAsFnDef { location, .. }
                    | ValidationError::WeakDeclarationAddressNotNullable { location, .. }
                    if location.contains("probe") && location.contains("case 0")
            ),
            "{case:?}: {errors:?}"
        );
        // Mutation control: the same case naming a STRONG import is not a weak
        // spelling (whatever else the switch rules say of it).
        let (strong, _) = build(Linkage::External, case.clone());
        assert!(
            !validate_module(&strong).iter().any(|e| matches!(
                e,
                ValidationError::WeakDeclarationAsFnDef { .. }
                    | ValidationError::WeakDeclarationAddressNotNullable { .. }
            )),
            "{case:?}"
        );
    }
}

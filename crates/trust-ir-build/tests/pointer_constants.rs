// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! WS3.8 / F-049: non-null pointer constants at typed-reference and fat-pointer
//! positions.
//!
//! Before WS3.8 the only `Ty::FatPtr` constant was the null pair
//! `[Int(0), Int(0)]` and `Constant::SymbolAddr` fit only `Ty::Ptr` /
//! `Ty::Func`, so `static S: &str = "..."`, a const table of `&str`, and a
//! `&'static T` field of a static initializer had no spelling except erasing
//! the fat type to a `(ptr, u64)` tuple. The module-table-aware constant walk
//! (`validate_constant_against_ty`) now admits exactly two non-null spellings:
//!
//! 1. `SymbolAddr { symbol, addend: 0 }` at `Ref(T)` / `PtrConst(T)` /
//!    `PtrMut(T)`, naming one module-defined global of type `T` (immutable at
//!    `Ref`, mutable at `PtrMut`);
//! 2. `Aggregate[SymbolAddr { G, addend: k }, Int(n)]` at `FatPtr(Str)` /
//!    `FatPtr(Slice(t))`, a window of one IMMUTABLE array global (UTF-8 on
//!    char boundaries for `str`).
//!
//! Every other shape of those two spellings is
//! `ValidationError::PointerConstantRefused` with a named
//! `PointerConstantRefusal`; `Rc` / `RefMut` / `TraitObject` / `ContainerLen` /
//! `ContainerVtable` keep `ConstTypeMismatch`. The reference interpreter
//! resolves an admitted constant to the global's own allocation.

use trust_ir::interpret::{InterpretErrorCode, Interpreter};
use trust_ir::ty::{ClosureTy, EnumDef, EnumVariant, FieldDef, StructDef};
use trust_ir::value::GlobalId;
use trust_ir::{Constant, FatPtrKind, Global, Linkage, Module, StructId, TlsModel, Ty, Visibility};
use trust_ir_build::validate::ValidationError;
use trust_ir_build::{
    ModuleBuilder, PointerConstantRefusal, TRUSTED_HANDLE_RUNTIMES, validate_module,
};

fn global(name: &str, ty: Ty, mutable: bool, initializer: Option<Constant>) -> Global {
    Global {
        name: name.into(),
        ty,
        mutable,
        initializer,
        linkage: Linkage::Internal,
        tls: None,
        align: None,
        section: None,
        visibility: Visibility::Default,
        retained: false,
    }
}

fn str_ty() -> Ty {
    Ty::FatPtr(FatPtrKind::Str)
}

/// The null fat pointer, the one constant every fat kind admits.
fn null_fat() -> Constant {
    Constant::Aggregate(vec![Constant::Int(0), Constant::Int(0)])
}

fn fat_str(symbol: &str, addend: i64, len: i128) -> Constant {
    Constant::Aggregate(vec![
        Constant::symbol_addr_with_addend(symbol, addend),
        Constant::Int(len),
    ])
}

/// `static BYTES: [u8; N] = <init>; static GREETING: &str = <fat>;` plus
/// `body_first()` (the fat constant as a body `Const`, first byte),
/// `global_first()` (the same through `GREETING`, first byte) and `body_len()`.
fn str_module(bytes_len: u64, bytes: Constant, fat: Constant) -> Module {
    let mut mb = ModuleBuilder::new("ws3_8_str");
    let u8_id = mb.add_type(Ty::U8);
    mb.add_global(global(
        "BYTES",
        Ty::Array(u8_id, bytes_len),
        false,
        Some(bytes),
    ));
    mb.add_global(global("GREETING", str_ty(), false, Some(fat.clone())));
    let first_ty = mb.add_func_type(vec![], vec![Ty::U8]);
    let len_ty = mb.add_func_type(vec![], vec![Ty::U64]);
    {
        let mut f = mb.function("body_first", first_ty);
        let e = f.create_block();
        f.switch_to_block(e);
        let s = f.const_value(str_ty(), fat.clone());
        let data = f.ptr_data(str_ty(), s);
        let byte = f.load(Ty::U8, data);
        f.ret(vec![byte]);
        f.build();
    }
    {
        let mut f = mb.function("global_first", first_ty);
        let e = f.create_block();
        f.switch_to_block(e);
        let slot = f.global_addr(GlobalId::new(1));
        let s = f.load(str_ty(), slot);
        let data = f.ptr_data(str_ty(), s);
        let byte = f.load(Ty::U8, data);
        f.ret(vec![byte]);
        f.build();
    }
    {
        let mut f = mb.function("body_len", len_ty);
        let e = f.create_block();
        f.switch_to_block(e);
        let s = f.const_value(str_ty(), fat);
        let len = f.ptr_metadata(str_ty(), Ty::U64, s);
        f.ret(vec![len]);
        f.build();
    }
    mb.build().expect("ModuleBuilder::build: test fixture")
}

fn run_u(module: &Module, name: &str) -> Result<u128, InterpretErrorCode> {
    let func = module
        .functions
        .iter()
        .find(|f| f.name == name)
        .unwrap_or_else(|| panic!("no function {name}"));
    let out = Interpreter::with_module(module)
        .execute_func(func.id, [])
        .map_err(|e| e.code)?;
    Ok(out.returns[0].as_int().expect("int return").as_unsigned())
}

/// The WS3.8 refusals in `errors`, as `(location, reason)`.
fn refusals(errors: &[ValidationError]) -> Vec<(String, PointerConstantRefusal)> {
    errors
        .iter()
        .filter_map(|e| match e {
            ValidationError::PointerConstantRefused {
                location, reason, ..
            } => Some((location.clone(), reason.clone())),
            _ => None,
        })
        .collect()
}

/// Assert `errors` is EXACTLY one refusal per listed location, each `reason`.
fn assert_refused_only(
    errors: &[ValidationError],
    locations: &[&str],
    reason: &PointerConstantRefusal,
) {
    assert_eq!(
        errors.len(),
        locations.len(),
        "expected exactly {} refusal(s) ({reason:?}), got {errors:?}",
        locations.len()
    );
    let found = refusals(errors);
    for location in locations {
        assert!(
            found
                .iter()
                .any(|(l, r)| l.contains(location) && r == reason),
            "expected {reason:?} at {location}, got {errors:?}"
        );
    }
}

// ---------------------------------------------------------------------------
// The positive fixture and its negative twin
// ---------------------------------------------------------------------------

/// POSITIVE: `&'static str` "hello" as `[SymbolAddr(BYTES), Int(5)]` at
/// `fatptr<str>` validates in a body `Const` AND a global initializer, and the
/// interpreter reads `'h'` through both (and the length 5).
#[test]
fn ws3_8_static_str_constant_validates_and_reads_h() {
    let m = str_module(5, Constant::str_bytes("hello"), fat_str("BYTES", 0, 5));
    let errors = validate_module(&m);
    assert!(errors.is_empty(), "{errors:?}");
    assert_eq!(run_u(&m, "body_first"), Ok(u128::from(b'h')));
    assert_eq!(run_u(&m, "global_first"), Ok(u128::from(b'h')));
    assert_eq!(run_u(&m, "body_len"), Ok(5));

    // An interior window (`&"hello"[1..4]`) reads its own first byte.
    let m = str_module(5, Constant::str_bytes("hello"), fat_str("BYTES", 1, 3));
    assert!(validate_module(&m).is_empty(), "{:?}", validate_module(&m));
    assert_eq!(run_u(&m, "body_first"), Ok(u128::from(b'e')));
    assert_eq!(run_u(&m, "global_first"), Ok(u128::from(b'e')));
}

/// NEGATIVE TWIN: `Int(6)` over the 5-byte global is refused at both
/// positions as `WindowOutOfBounds`, and the interpreter refuses to fabricate
/// the window.
#[test]
fn ws3_8_str_constant_longer_than_its_global_is_refused() {
    let m = str_module(5, Constant::str_bytes("hello"), fat_str("BYTES", 0, 6));
    assert_refused_only(
        &validate_module(&m),
        &[
            "global 'GREETING'",
            "function 'body_first'",
            "function 'body_len'",
        ],
        &PointerConstantRefusal::WindowOutOfBounds {
            offset: 0,
            length: 6,
            capacity: 5,
        },
    );
    assert_eq!(run_u(&m, "body_first"), Err(InterpretErrorCode::TypeError));
    // An offset past the end is the same refusal.
    let m = str_module(5, Constant::str_bytes("hello"), fat_str("BYTES", 6, 0));
    assert!(refusals(&validate_module(&m)).iter().all(|(_, r)| matches!(
        r,
        PointerConstantRefusal::WindowOutOfBounds { offset: 6, .. }
    )));
    // A negative length is not a length.
    let m = str_module(5, Constant::str_bytes("hello"), fat_str("BYTES", 0, -1));
    assert!(
        refusals(&validate_module(&m))
            .iter()
            .all(|(_, r)| matches!(r, PointerConstantRefusal::InvalidLength { .. }))
    );
}

// ---------------------------------------------------------------------------
// Mutation / adversarial controls (a)..(g)
// ---------------------------------------------------------------------------

/// (a) A length landing mid-UTF-8 sequence is refused; the char-boundary
/// window over the same bytes validates (the control). "héllo" is
/// `68 C3 A9 6C 6C 6F`.
#[test]
fn ws3_8_str_window_mid_utf8_sequence_is_refused() {
    let bytes = || Constant::str_bytes("héllo");
    let control = str_module(6, bytes(), fat_str("BYTES", 0, 3));
    assert!(
        validate_module(&control).is_empty(),
        "{:?}",
        validate_module(&control)
    );
    for (addend, len) in [(0, 2), (2, 1), (2, 4)] {
        let m = str_module(6, bytes(), fat_str("BYTES", addend, len));
        assert_refused_only(
            &validate_module(&m),
            &[
                "global 'GREETING'",
                "function 'body_first'",
                "function 'body_len'",
            ],
            &PointerConstantRefusal::NotOnCharBoundary,
        );
    }
}

/// (e) Bytes that happen to be valid UTF-8 but carry `utf8: false` are not a
/// `str` referent; neither is an `Array` of integers.
#[test]
fn ws3_8_str_over_bytes_without_the_utf8_claim_is_refused() {
    for init in [
        Constant::bytes(*b"hello"),
        Constant::Array(
            b"hello"
                .iter()
                .map(|b| Constant::Int(i128::from(*b)))
                .collect(),
        ),
    ] {
        let m = str_module(5, init, fat_str("BYTES", 0, 5));
        assert_refused_only(
            &validate_module(&m),
            &[
                "global 'GREETING'",
                "function 'body_first'",
                "function 'body_len'",
            ],
            &PointerConstantRefusal::NotUtf8Bytes,
        );
    }
}

/// A module holding `static ANSWER: <global_ty> = 42` (with the given
/// mutability, TLS and linkage) and `read()`, which takes
/// `Const <ptr_ty> symaddr<symbol + addend>` and loads a `u64` through it.
fn thin_module(
    global_ty: Ty,
    mutable: bool,
    tls: Option<TlsModel>,
    linkage: Linkage,
    ptr_ty: Ty,
    symbol: &str,
    addend: i64,
) -> Module {
    let mut mb = ModuleBuilder::new("ws3_8_thin");
    let mut g = global("ANSWER", global_ty, mutable, Some(Constant::Int(42)));
    g.tls = tls;
    g.linkage = linkage;
    mb.add_global(g);
    let ft = mb.add_func_type(vec![], vec![Ty::U64]);
    let mut f = mb.function("read", ft);
    let e = f.create_block();
    f.switch_to_block(e);
    let p = f.const_value(ptr_ty, Constant::symbol_addr_with_addend(symbol, addend));
    let v = f.load(Ty::U64, p);
    f.ret(vec![v]);
    f.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

fn thin(global_ty: Ty, mutable: bool, ptr_ty: Ty) -> Module {
    thin_module(
        global_ty,
        mutable,
        None,
        Linkage::Internal,
        ptr_ty,
        "ANSWER",
        0,
    )
}

fn r(t: Ty) -> Ty {
    Ty::Ref(Box::new(t))
}

/// POSITIVE (rule 1): `&'static u64` / `*const u64` of an immutable global and
/// `*mut u64` of a mutable one validate, and the interpreter loads 42 through
/// each.
#[test]
fn ws3_8_typed_reference_constants_validate_and_load() {
    for (mutable, ptr_ty) in [
        (false, r(Ty::U64)),
        (false, Ty::PtrConst(Box::new(Ty::U64))),
        (true, Ty::PtrConst(Box::new(Ty::U64))),
        (true, Ty::PtrMut(Box::new(Ty::U64))),
    ] {
        let m = thin(Ty::U64, mutable, ptr_ty.clone());
        assert!(
            validate_module(&m).is_empty(),
            "{ptr_ty}: {:?}",
            validate_module(&m)
        );
        assert_eq!(run_u(&m, "read"), Ok(42), "{ptr_ty}");
    }
}

/// (b) `SymbolAddr` of a `u64` global at `Ref(u32)` is refused.
#[test]
fn ws3_8_ref_to_a_global_of_another_type_is_refused() {
    let m = thin(Ty::U64, false, r(Ty::U32));
    assert_refused_only(
        &validate_module(&m),
        &["function 'read'"],
        &PointerConstantRefusal::PointeeTypeMismatch {
            global_ty: "u64".into(),
        },
    );
}

/// (c) `SymbolAddr` of an undeclared (external) symbol at `Ref(T)` is
/// refused; so is a FUNCTION symbol, and a global that is only DECLARED
/// (no initializer: the linked walk's extern data declaration).
#[test]
fn ws3_8_ref_to_an_undeclared_symbol_is_refused() {
    let external = thin_module(
        Ty::U64,
        false,
        None,
        Linkage::Internal,
        r(Ty::U64),
        "EXTERN_STATIC",
        0,
    );
    assert_refused_only(
        &validate_module(&external),
        &["function 'read'"],
        &PointerConstantRefusal::NotAModuleGlobal,
    );

    let function = thin_module(
        Ty::U64,
        false,
        None,
        Linkage::Internal,
        r(Ty::U64),
        "read",
        0,
    );
    assert_refused_only(
        &validate_module(&function),
        &["function 'read'"],
        &PointerConstantRefusal::NotAModuleGlobal,
    );

    let mut declared = thin(Ty::U64, false, r(Ty::U64));
    declared.globals[0].initializer = None;
    declared.globals[0].linkage = Linkage::External;
    assert_refused_only(
        &validate_module(&declared),
        &["function 'read'"],
        &PointerConstantRefusal::GlobalNotDefined,
    );
}

/// (d) `SymbolAddr` at `Rc(T)` / `RefMut(T)` is still `ConstTypeMismatch`: a
/// static is not an RC allocation, and `&'static mut` needs a uniqueness
/// proof the format lacks.
#[test]
fn ws3_8_symbol_address_at_rc_or_ref_mut_is_still_a_type_mismatch() {
    for ptr_ty in [Ty::Rc(Box::new(Ty::U64)), Ty::RefMut(Box::new(Ty::U64))] {
        for mutable in [false, true] {
            let m = thin(Ty::U64, mutable, ptr_ty.clone());
            let errors = validate_module(&m);
            assert_eq!(errors.len(), 1, "{ptr_ty}: {errors:?}");
            assert!(
                matches!(&errors[0], ValidationError::ConstTypeMismatch { expected, actual, .. }
                    if *expected == ptr_ty.to_string() && actual == "symaddr<ANSWER + 0>"),
                "{ptr_ty}: {errors:?}"
            );
        }
    }
}

/// (f) A `mutable` global at `Ref(T)` is refused while the same at
/// `PtrMut(T)` validates (the close twin); an immutable global at `PtrMut(T)`
/// is refused.
#[test]
fn ws3_8_mutability_must_match_the_pointer_type() {
    let shared_into_mutable = thin(Ty::U64, true, r(Ty::U64));
    assert_refused_only(
        &validate_module(&shared_into_mutable),
        &["function 'read'"],
        &PointerConstantRefusal::MutabilityMismatch {
            global_mutable: true,
        },
    );
    let twin = thin(Ty::U64, true, Ty::PtrMut(Box::new(Ty::U64)));
    assert!(
        validate_module(&twin).is_empty(),
        "{:?}",
        validate_module(&twin)
    );

    let mut_into_frozen = thin(Ty::U64, false, Ty::PtrMut(Box::new(Ty::U64)));
    assert_refused_only(
        &validate_module(&mut_into_frozen),
        &["function 'read'"],
        &PointerConstantRefusal::MutabilityMismatch {
            global_mutable: false,
        },
    );
}

/// (g) A thread-local global at `Ref(T)` is refused: its address is per
/// thread, not a link-time constant.
#[test]
fn ws3_8_ref_to_a_thread_local_global_is_refused() {
    let m = thin_module(
        Ty::U64,
        false,
        Some(TlsModel::GeneralDynamic),
        Linkage::Internal,
        r(Ty::U64),
        "ANSWER",
        0,
    );
    assert_refused_only(
        &validate_module(&m),
        &["function 'read'"],
        &PointerConstantRefusal::ThreadLocal,
    );
    assert_eq!(run_u(&m, "read"), Err(InterpretErrorCode::TypeError));
}

/// Further adversarial shapes of rule 1: a nonzero addend (a typed reference
/// addresses the whole global), an interposable definition, and a symbol two
/// module items share.
#[test]
fn ws3_8_ref_constant_addend_linkage_and_ambiguity_are_refused() {
    let offset = thin_module(
        Ty::U64,
        false,
        None,
        Linkage::Internal,
        r(Ty::U64),
        "ANSWER",
        8,
    );
    assert_refused_only(
        &validate_module(&offset),
        &["function 'read'"],
        &PointerConstantRefusal::NonzeroAddend { addend: 8 },
    );

    for linkage in [Linkage::Weak, Linkage::LinkOnce, Linkage::ExternalWeak] {
        let m = thin_module(Ty::U64, false, None, linkage, r(Ty::U64), "ANSWER", 0);
        assert!(
            refusals(&validate_module(&m))
                == vec![(
                    "function 'read' bb0".into(),
                    PointerConstantRefusal::InterposableLinkage { linkage }
                )],
            "{linkage:?}: {:?}",
            validate_module(&m)
        );
    }
    // The one-definition-rule linkages stay admitted (the WS8.14 premise).
    for linkage in [Linkage::WeakOdr, Linkage::LinkOnceOdr, Linkage::External] {
        let m = thin_module(Ty::U64, false, None, linkage, r(Ty::U64), "ANSWER", 0);
        assert!(
            refusals(&validate_module(&m)).is_empty(),
            "{linkage:?}: {:?}",
            validate_module(&m)
        );
    }

    let mut twice = thin(Ty::U64, false, r(Ty::U64));
    let copy = twice.globals[0].clone();
    twice.globals.push(copy);
    assert!(
        refusals(&validate_module(&twice))
            == vec![(
                "function 'read' bb0".into(),
                PointerConstantRefusal::AmbiguousSymbol {
                    globals: 2,
                    functions: 0
                }
            )],
        "{:?}",
        validate_module(&twice)
    );
}

// ---------------------------------------------------------------------------
// Slices, and the kinds that stay null-only
// ---------------------------------------------------------------------------

/// `static TABLE: [u32; 4] = [10, 20, 30, 40]; static VIEW: &[u32] = <fat>;`
/// with `second()` reading element 1 of the view through `VIEW`.
fn slice_module(elem: Ty, mutable: bool, fat: Constant) -> Module {
    let mut mb = ModuleBuilder::new("ws3_8_slice");
    let u32_id = mb.add_type(Ty::U32);
    let elem_id = mb.add_type(elem);
    let table = Constant::Array((1..=4).map(|i| Constant::Int(i * 10)).collect());
    mb.add_global(global("TABLE", Ty::Array(elem_id, 4), mutable, Some(table)));
    let view_ty = Ty::FatPtr(FatPtrKind::Slice(u32_id));
    mb.add_global(global("VIEW", view_ty.clone(), false, Some(fat)));
    let ft = mb.add_func_type(vec![], vec![Ty::U32]);
    let mut f = mb.function("second", ft);
    let e = f.create_block();
    f.switch_to_block(e);
    let slot = f.global_addr(GlobalId::new(1));
    let view = f.load(view_ty.clone(), slot);
    let data = f.ptr_data(view_ty, view);
    let second = f.gep_byte_offset(data, 4);
    let v = f.load(Ty::U32, second);
    f.ret(vec![v]);
    f.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

/// POSITIVE (rule 2, slice): `&TABLE[1..4]` validates and reads 30 as its
/// element 1; the element-misaligned, overlong, mutable-array and
/// wrong-element twins are refused by name.
#[test]
fn ws3_8_slice_constant_validates_and_its_twins_are_refused() {
    let m = slice_module(Ty::U32, false, fat_str("TABLE", 4, 3));
    assert!(validate_module(&m).is_empty(), "{:?}", validate_module(&m));
    assert_eq!(run_u(&m, "second"), Ok(30));

    let cases = [
        (
            slice_module(Ty::U32, false, fat_str("TABLE", 2, 1)),
            PointerConstantRefusal::MisalignedOffset {
                offset: 2,
                element_size: 4,
            },
        ),
        (
            slice_module(Ty::U32, false, fat_str("TABLE", 4, 4)),
            PointerConstantRefusal::WindowOutOfBounds {
                offset: 4,
                length: 4,
                capacity: 4,
            },
        ),
        (
            slice_module(Ty::U32, true, fat_str("TABLE", 0, 4)),
            PointerConstantRefusal::MutabilityMismatch {
                global_mutable: true,
            },
        ),
        (
            slice_module(Ty::U16, false, fat_str("TABLE", 0, 4)),
            PointerConstantRefusal::ArrayTypeMismatch {
                global_ty: "[ty.1; 4]".into(),
            },
        ),
    ];
    for (m, reason) in cases {
        let found = refusals(&validate_module(&m));
        assert_eq!(found.len(), 1, "{reason:?}: {:?}", validate_module(&m));
        assert!(found[0].0.contains("global 'VIEW'"), "{found:?}");
        assert!(
            matches!(
                (&found[0].1, &reason),
                (
                    PointerConstantRefusal::ArrayTypeMismatch { .. },
                    PointerConstantRefusal::ArrayTypeMismatch { .. }
                )
            ) || found[0].1 == reason,
            "{reason:?}: {found:?}"
        );
    }
}

/// Rule 3: a non-null `TraitObject` / `ContainerLen` / `ContainerVtable`
/// constant stays `ConstTypeMismatch` — its vtable or container header is not
/// checkable from the format — while the null pair still fits all three.
#[test]
fn ws3_8_trait_object_and_container_fat_pointers_stay_null_only() {
    for kind in [
        FatPtrKind::TraitObject { trait_id: 7 },
        FatPtrKind::ContainerLen,
        FatPtrKind::ContainerVtable,
    ] {
        let fat = Ty::FatPtr(kind);
        let mut mb = ModuleBuilder::new("ws3_8_dyn");
        let u8_id = mb.add_type(Ty::U8);
        mb.add_global(global(
            "BYTES",
            Ty::Array(u8_id, 5),
            false,
            Some(Constant::str_bytes("hello")),
        ));
        mb.add_global(global("NULL", fat.clone(), false, Some(null_fat())));
        mb.add_global(global(
            "DYN",
            fat.clone(),
            false,
            Some(fat_str("BYTES", 0, 5)),
        ));
        let errors = validate_module(&mb.build().expect("ModuleBuilder::build: test fixture"));
        assert_eq!(errors.len(), 1, "{fat}: {errors:?}");
        assert!(
            matches!(&errors[0], ValidationError::ConstTypeMismatch { location, actual, .. }
                if location == "global 'DYN'" && actual == "aggregate[2]"),
            "{fat}: {errors:?}"
        );
    }
}

/// Rule 4: a pinned handle-runtime symbol inside a fat constant is still
/// `HandleEntryPointAddressTaken` (that walk visits every constant tree), on
/// top of the WS3.8 refusal (it names no module global).
#[test]
fn ws3_8_pinned_handle_symbol_in_a_fat_constant_is_still_refused() {
    let pinned = TRUSTED_HANDLE_RUNTIMES[0].entry_points[0].symbol;
    let mut mb = ModuleBuilder::new("ws3_8_handle");
    mb.add_global(global(
        "SNEAK",
        str_ty(),
        false,
        Some(fat_str(pinned, 0, 1)),
    ));
    let errors = validate_module(&mb.build().expect("ModuleBuilder::build: test fixture"));
    assert!(
        errors.iter().any(|e| matches!(e, ValidationError::HandleEntryPointAddressTaken { symbol, .. } if symbol == pinned)),
        "{errors:?}"
    );
    assert_eq!(
        refusals(&errors),
        vec![(
            "global 'SNEAK'".into(),
            PointerConstantRefusal::NotAModuleGlobal
        )]
    );
}

/// A closure capturing a `&'static u64` constant: the closure-capture pass
/// (table-free) must not refuse what the typed walk admits, and must not
/// admit what it refuses.
#[test]
fn ws3_8_closure_capture_of_a_ref_constant_follows_the_typed_walk() {
    let build = |symbol: &str| {
        let mut mb = ModuleBuilder::new("ws3_8_closure");
        mb.add_global(global("ANSWER", Ty::U64, false, Some(Constant::Int(42))));
        let body_ty = mb.add_func_type(vec![r(Ty::U64)], vec![Ty::U64]);
        let body = {
            let mut f = mb.function("body", body_ty);
            let e = f.create_block();
            let p = f.add_block_param(e, r(Ty::U64));
            f.switch_to_block(e);
            let v = f.load(Ty::U64, p);
            f.ret(vec![v]);
            f.build()
        };
        let call_ty = mb.add_func_type(vec![], vec![Ty::U64]);
        let closure_ty = mb.add_closure_type(ClosureTy {
            func: call_ty,
            captures: vec![r(Ty::U64)],
        });
        let mut m = mb.build().expect("ModuleBuilder::build: test fixture");
        m.globals.push(global(
            "CLOSURE",
            Ty::Closure(closure_ty),
            false,
            Some(Constant::Closure {
                func: body,
                captures: vec![Constant::symbol_addr(symbol)],
            }),
        ));
        m
    };
    let ok = build("ANSWER");
    let errors = validate_module(&ok);
    assert!(
        !errors.iter().any(|e| matches!(
            e,
            ValidationError::ClosureCaptureTypeMismatch { .. }
                | ValidationError::PointerConstantRefused { .. }
        )),
        "{errors:?}"
    );
    let bad = build("NOWHERE");
    assert_eq!(
        refusals(&validate_module(&bad)),
        vec![(
            "global 'CLOSURE'".into(),
            PointerConstantRefusal::NotAModuleGlobal
        )]
    );
}

// ---------------------------------------------------------------------------
// Proof-program rows, ported (F-049)
// ---------------------------------------------------------------------------

/// Row `b6.fatptr.non_null_constant_rejected` — GAP → PASS. The archived
/// module (`static HELLO: [u8; 6] = "héllo"; static GREETING: &str =
/// [SymbolAddr(HELLO), Int(6)]`, and the same constant in `greeting()`) was
/// refused as `ConstTypeMismatch { expected: "fatptr<str>", actual:
/// "aggregate[2]" }` at both positions. It now validates, the null and the
/// type-erased spellings still validate, and its negative twin (`Int(7)`) is
/// refused by name at both positions.
#[test]
fn b6_fatptr_non_null_constant_rejected() {
    let build = |init: Constant| {
        let mut mb = ModuleBuilder::new("b6_fatptr_const");
        let u8_id = mb.add_type(Ty::U8);
        mb.add_global(global(
            "HELLO",
            Ty::Array(u8_id, 6),
            false,
            Some(Constant::str_bytes("héllo")),
        ));
        mb.add_global(global("GREETING", str_ty(), false, Some(init.clone())));
        let ft = mb.add_func_type(vec![], vec![str_ty()]);
        let mut f = mb.function("greeting", ft);
        f.set_producer(trust_ir::Producer::TRust);
        let e = f.create_block();
        f.switch_to_block(e);
        let c = f.const_value(str_ty(), init);
        f.ret(vec![c]);
        f.build();
        mb.build().expect("ModuleBuilder::build: test fixture")
    };
    let non_null = validate_module(&build(fat_str("HELLO", 0, 6)));
    assert!(
        non_null.is_empty(),
        "the non-null &str constant must validate: {non_null:?}"
    );
    let null = validate_module(&build(null_fat()));
    assert!(null.is_empty(), "{null:?}");

    let erased = {
        let mut mb = ModuleBuilder::new("b6_fatptr_const_erased");
        let u8_id = mb.add_type(Ty::U8);
        mb.add_global(global(
            "HELLO",
            Ty::Array(u8_id, 6),
            false,
            Some(Constant::str_bytes("héllo")),
        ));
        mb.add_global(global(
            "GREETING",
            Ty::Tuple(vec![Ty::Ptr, Ty::U64]),
            false,
            Some(fat_str("HELLO", 0, 6)),
        ));
        validate_module(&mb.build().expect("ModuleBuilder::build: test fixture"))
    };
    assert!(erased.is_empty(), "{erased:?}");

    let twin = validate_module(&build(fat_str("HELLO", 0, 7)));
    assert_refused_only(
        &twin,
        &["global 'GREETING'", "function 'greeting'"],
        &PointerConstantRefusal::WindowOutOfBounds {
            offset: 0,
            length: 7,
            capacity: 6,
        },
    );
}

/// Row `exec-log-and-tcb/fat-pointer-constants`: `static NAMES: [&str; 2] =
/// ["a", "bc"];` and `static CFG: Cfg = Cfg { name: "bc" }` are written as-is
/// (non-null fat constants inside an array and a struct initializer),
/// validate, and execute: `NAMES[1]` reads `'c'` at index 1, `CFG.name` has
/// length 2.
#[test]
fn exec_log_and_tcb_fat_pointer_constants() {
    let mut mb = ModuleBuilder::new("names");
    let u8_id = mb.add_type(Ty::U8);
    let str_id = mb.add_type(str_ty());
    mb.add_global(global(
        "A",
        Ty::Array(u8_id, 1),
        false,
        Some(Constant::str_bytes("a")),
    ));
    mb.add_global(global(
        "BC",
        Ty::Array(u8_id, 2),
        false,
        Some(Constant::str_bytes("bc")),
    ));
    mb.add_global(global(
        "NAMES",
        Ty::Array(str_id, 2),
        false,
        Some(Constant::Array(vec![
            fat_str("A", 0, 1),
            fat_str("BC", 0, 2),
        ])),
    ));
    let cfg = mb.add_struct(StructDef {
        id: StructId::new(0),
        name: "Cfg".into(),
        fields: vec![FieldDef {
            name: "name".into(),
            ty: str_ty(),
            offset: None,
        }],
        size: None,
        align: None,
        repr: Default::default(),
        origin: None,
    });
    mb.add_global(global(
        "CFG",
        Ty::Struct(cfg),
        false,
        Some(Constant::Aggregate(vec![fat_str("BC", 0, 2)])),
    ));
    let ft = mb.add_func_type(vec![], vec![Ty::U8]);
    {
        let mut f = mb.function("names_1_1", ft);
        let e = f.create_block();
        f.switch_to_block(e);
        let names = f.global_addr(GlobalId::new(2));
        let second = f.gep_byte_offset(names, 16);
        let s = f.load(str_ty(), second);
        let data = f.ptr_data(str_ty(), s);
        let c = f.gep_byte_offset(data, 1);
        let v = f.load(Ty::U8, c);
        f.ret(vec![v]);
        f.build();
    }
    let len_ty = mb.add_func_type(vec![], vec![Ty::U64]);
    {
        let mut f = mb.function("cfg_name_len", len_ty);
        let e = f.create_block();
        f.switch_to_block(e);
        let cfg = f.global_addr(GlobalId::new(3));
        let s = f.load(str_ty(), cfg);
        let len = f.ptr_metadata(str_ty(), Ty::U64, s);
        f.ret(vec![len]);
        f.build();
    }
    let m = mb.build().expect("ModuleBuilder::build: test fixture");
    let errors = validate_module(&m);
    assert!(errors.is_empty(), "{errors:?}");
    assert_eq!(run_u(&m, "names_1_1"), Ok(u128::from(b'c')));
    assert_eq!(run_u(&m, "cfg_name_len"), Ok(2));

    // The twin: a table entry whose length overruns its referent.
    let mut bad = m.clone();
    bad.globals[2].initializer = Some(Constant::Array(vec![
        fat_str("A", 0, 1),
        fat_str("BC", 0, 3),
    ]));
    assert_eq!(
        refusals(&validate_module(&bad)),
        vec![(
            "global 'NAMES'[1]".into(),
            PointerConstantRefusal::WindowOutOfBounds {
                offset: 0,
                length: 3,
                capacity: 2
            }
        )]
    );
}

/// Row `producer-rust-thir/fat-pointer-constant`: `const E: Option<&'static
/// str> = Some("x")` as an enum constant in a body validates (the four-format
/// round trip of the same module is `pointer_constant_formats` in
/// trust-ir-conformance); the same seed over a MUTABLE referent is refused.
#[test]
fn producer_rust_thir_fat_pointer_constant() {
    let build = |mutable: bool| {
        let mut mb = ModuleBuilder::new("option_str");
        let u8_id = mb.add_type(Ty::U8);
        mb.add_global(global(
            "X",
            Ty::Array(u8_id, 1),
            mutable,
            Some(Constant::str_bytes("x")),
        ));
        let option = mb.add_enum(EnumDef::new(
            trust_ir::EnumId::new(0),
            "Option",
            vec![
                EnumVariant {
                    name: "None".into(),
                    fields: vec![],
                    field_names: vec![],
                },
                EnumVariant {
                    name: "Some".into(),
                    fields: vec![str_ty()],
                    field_names: vec![],
                },
            ],
        ));
        let ft = mb.add_func_type(vec![], vec![Ty::Enum(option)]);
        let mut f = mb.function("e", ft);
        let e = f.create_block();
        f.switch_to_block(e);
        let v = f.const_value(
            Ty::Enum(option),
            Constant::Aggregate(vec![Constant::Int(1), fat_str("X", 0, 1)]),
        );
        f.ret(vec![v]);
        f.build();
        mb.build().expect("ModuleBuilder::build: test fixture")
    };
    let m = build(false);
    assert!(validate_module(&m).is_empty(), "{:?}", validate_module(&m));
    assert_eq!(
        refusals(&validate_module(&build(true))),
        vec![(
            "function 'e' bb0".into(),
            PointerConstantRefusal::MutabilityMismatch {
                global_mutable: true
            }
        )]
    );
}

#[test]
fn ws3_8_refusal_renders_its_reason() {
    let m = str_module(5, Constant::str_bytes("hello"), fat_str("BYTES", 0, 6));
    let rendered = validate_module(&m)[0].to_string();
    assert!(
        rendered.contains("symaddr<BYTES>") && rendered.contains("does not fit"),
        "{rendered}"
    );
}

// ---------------------------------------------------------------------------
// Adversarial review (WS3.8 review): shapes the implementation was not written
// against.
// ---------------------------------------------------------------------------

/// `struct Node { val: u64, next: &'static Node }` as a nominal struct.
fn node_struct(mb: &mut ModuleBuilder, index: u32, name: &str) -> StructId {
    let id = StructId::new(index);
    mb.add_struct(StructDef {
        id,
        name: name.into(),
        fields: vec![
            FieldDef {
                name: "val".into(),
                ty: Ty::U64,
                offset: None,
            },
            FieldDef {
                name: "next".into(),
                ty: r(Ty::Struct(id)),
                offset: None,
            },
        ],
        size: None,
        align: None,
        repr: Default::default(),
        origin: None,
    })
}

/// `fn hop(): u64` — load global #0, follow `next` `hops` times, return `val`.
fn add_hop(mb: &mut ModuleBuilder, node: StructId, hops: usize) {
    let ft = mb.add_func_type(vec![], vec![Ty::U64]);
    let mut f = mb.function("hop", ft);
    let e = f.create_block();
    f.switch_to_block(e);
    let slot = f.global_addr(GlobalId::new(0));
    let mut value = f.load(Ty::Struct(node), slot);
    for _ in 0..hops {
        let next = f.extract_field(r(Ty::Struct(node)), value, 1);
        value = f.load(Ty::Struct(node), next);
    }
    let v = f.extract_field(Ty::U64, value, 0);
    f.ret(vec![v]);
    f.build();
}

/// A SELF-REFERENTIAL static (`static N: Node = Node { val: 42, next: &N }`)
/// and a two-static cycle (`A.next = &B`, `B.next = &A`) validate, and the
/// interpreter terminates on both — the global is cached before its
/// initializer is evaluated — resolving every hop to the ONE allocation of the
/// named global.
#[test]
fn ws3_8_self_referential_and_cyclic_statics_validate_and_terminate() {
    let mut mb = ModuleBuilder::new("ws3_8_self");
    let node = node_struct(&mut mb, 0, "Node");
    mb.add_global(global(
        "N",
        Ty::Struct(node),
        false,
        Some(Constant::Aggregate(vec![
            Constant::Int(42),
            Constant::symbol_addr("N"),
        ])),
    ));
    add_hop(&mut mb, node, 3);
    let m = mb.build().expect("ModuleBuilder::build: test fixture");
    assert!(validate_module(&m).is_empty(), "{:?}", validate_module(&m));
    assert_eq!(run_u(&m, "hop"), Ok(42));

    let cycle = |hops| {
        let mut mb = ModuleBuilder::new("ws3_8_cycle");
        let node = node_struct(&mut mb, 0, "Node");
        for (name, val, next) in [("A", 1, "B"), ("B", 2, "A")] {
            mb.add_global(global(
                name,
                Ty::Struct(node),
                false,
                Some(Constant::Aggregate(vec![
                    Constant::Int(val),
                    Constant::symbol_addr(next),
                ])),
            ));
        }
        add_hop(&mut mb, node, hops);
        mb.build().expect("ModuleBuilder::build: test fixture")
    };
    for (hops, expected) in [(0, 1), (1, 2), (2, 1), (5, 2)] {
        let m = cycle(hops);
        assert!(validate_module(&m).is_empty(), "{:?}", validate_module(&m));
        assert_eq!(run_u(&m, "hop"), Ok(expected), "{hops} hop(s)");
    }
}

/// PROVENANCE: a `*mut u64` constant and `GlobalAddr` of the same global are
/// ONE allocation — a store through either is seen by a load through the
/// other, in both orders. A constant that minted a fresh copy of the global
/// would read the stale 1.
#[test]
fn ws3_8_mut_pointer_constant_aliases_the_global_it_names() {
    for store_through_constant in [true, false] {
        let mut mb = ModuleBuilder::new("ws3_8_alias");
        mb.add_global(global("M", Ty::U64, true, Some(Constant::Int(1))));
        let ft = mb.add_func_type(vec![], vec![Ty::U64]);
        let mut f = mb.function("alias", ft);
        let e = f.create_block();
        f.switch_to_block(e);
        let via_global = f.global_addr(GlobalId::new(0));
        let via_constant = f.const_value(Ty::PtrMut(Box::new(Ty::U64)), Constant::symbol_addr("M"));
        let (store_ptr, load_ptr) = if store_through_constant {
            (via_constant, via_global)
        } else {
            (via_global, via_constant)
        };
        let seven = f.const_value(Ty::U64, Constant::Int(7));
        f.store(Ty::U64, store_ptr, seven);
        let v = f.load(Ty::U64, load_ptr);
        f.ret(vec![v]);
        f.build();
        let m = mb.build().expect("ModuleBuilder::build: test fixture");
        assert!(validate_module(&m).is_empty(), "{:?}", validate_module(&m));
        assert_eq!(run_u(&m, "alias"), Ok(7), "{store_through_constant}");
    }
}

/// FALSE-CLAIM CONTROL: a `&refine<u64, nonzero>` constant naming an
/// UNREFINED `u64` global holding 0 would hand every verifier a refinement
/// the memory does not satisfy. Refused as `PointeeTypeMismatch` (the
/// structural comparison keeps the predicate), while the same constant at
/// plain `&u64` validates.
#[test]
fn ws3_8_ref_cannot_launder_a_refinement_onto_an_unrefined_global() {
    let build = |refined: bool| {
        let mut mb = ModuleBuilder::new("ws3_8_refine");
        let nonzero = mb.intern_pred(trust_ir::Pred::NonZero).expect("pred");
        let pointee = if refined {
            mb.refine_ty(Ty::U64, nonzero)
        } else {
            Ty::U64
        };
        mb.add_global(global("ZERO", Ty::U64, false, Some(Constant::Int(0))));
        let ft = mb.add_func_type(vec![], vec![Ty::U64]);
        let mut f = mb.function("read", ft);
        let e = f.create_block();
        f.switch_to_block(e);
        let p = f.const_value(r(pointee), Constant::symbol_addr("ZERO"));
        let v = f.load(Ty::U64, p);
        f.ret(vec![v]);
        f.build();
        mb.build().expect("ModuleBuilder::build: test fixture")
    };
    let plain = build(false);
    assert!(
        validate_module(&plain).is_empty(),
        "{:?}",
        validate_module(&plain)
    );
    assert_refused_only(
        &validate_module(&build(true)),
        &["function 'read'"],
        &PointerConstantRefusal::PointeeTypeMismatch {
            global_ty: "u64".into(),
        },
    );
}

/// NOMINAL CONTROL: `&Other` naming a global of a DIFFERENT struct with the
/// identical field list is refused — two same-shaped nominal types are not
/// the same pointee — while `&Node` naming it validates.
#[test]
fn ws3_8_ref_to_a_same_shaped_struct_of_another_name_is_refused() {
    let build = |pointee_is_other: bool| {
        let mut mb = ModuleBuilder::new("ws3_8_nominal");
        let node = node_struct(&mut mb, 0, "Node");
        let other = node_struct(&mut mb, 1, "Other");
        mb.add_global(global(
            "N",
            Ty::Struct(node),
            false,
            Some(Constant::Aggregate(vec![
                Constant::Int(42),
                Constant::symbol_addr("N"),
            ])),
        ));
        let pointee = Ty::Struct(if pointee_is_other { other } else { node });
        let ft = mb.add_func_type(vec![], vec![Ty::U64]);
        let mut f = mb.function("read", ft);
        let e = f.create_block();
        f.switch_to_block(e);
        let p = f.const_value(r(pointee.clone()), Constant::symbol_addr("N"));
        let n = f.load(pointee, p);
        let v = f.extract_field(Ty::U64, n, 0);
        f.ret(vec![v]);
        f.build();
        mb.build().expect("ModuleBuilder::build: test fixture")
    };
    let same = build(false);
    assert!(
        validate_module(&same).is_empty(),
        "{:?}",
        validate_module(&same)
    );
    assert_eq!(run_u(&same, "read"), Ok(42));
    let found = refusals(&validate_module(&build(true)));
    assert_eq!(found.len(), 1, "{found:?}");
    assert!(
        found[0].0.contains("function 'read'")
            && matches!(
                found[0].1,
                PointerConstantRefusal::PointeeTypeMismatch { .. }
            ),
        "{found:?}"
    );
}

/// NESTED: a `[&u64; 3]` body constant is checked PER ELEMENT — naming an
/// immutable, a mutable and an undeclared global, it is refused exactly twice
/// (`MutabilityMismatch` at element 1, `NotAModuleGlobal` at element 2), each
/// at its own element path; with every element valid the interpreter loads
/// through element 2.
#[test]
fn ws3_8_array_of_references_is_checked_per_element() {
    let build = |symbols: [&str; 3]| {
        let mut mb = ModuleBuilder::new("ws3_8_nested");
        let ref_id = mb.add_type(r(Ty::U64));
        mb.add_global(global("A", Ty::U64, false, Some(Constant::Int(10))));
        mb.add_global(global("B", Ty::U64, false, Some(Constant::Int(20))));
        mb.add_global(global("M", Ty::U64, true, Some(Constant::Int(30))));
        let array_ty = Ty::Array(ref_id, 3);
        let ft = mb.add_func_type(vec![], vec![Ty::U64]);
        let mut f = mb.function("third", ft);
        let e = f.create_block();
        f.switch_to_block(e);
        let table = f.const_value(
            array_ty.clone(),
            Constant::Array(symbols.iter().map(|s| Constant::symbol_addr(*s)).collect()),
        );
        let two = f.const_value(Ty::U64, Constant::Int(2));
        let p = f.extract_element(r(Ty::U64), table, two);
        let v = f.load(Ty::U64, p);
        f.ret(vec![v]);
        f.build();
        mb.build().expect("ModuleBuilder::build: test fixture")
    };
    let ok = build(["A", "A", "B"]);
    assert!(
        validate_module(&ok).is_empty(),
        "{:?}",
        validate_module(&ok)
    );
    assert_eq!(run_u(&ok, "third"), Ok(20));

    let errors = validate_module(&build(["A", "M", "NOWHERE"]));
    let found = refusals(&errors);
    assert_eq!(errors.len(), 2, "{errors:?}");
    assert_eq!(found.len(), 2, "{errors:?}");
    let at = |reason: &PointerConstantRefusal| {
        found
            .iter()
            .find(|(_, r)| r == reason)
            .map(|(l, _)| l.clone())
            .unwrap_or_else(|| panic!("no {reason:?} in {found:?}"))
    };
    let mutable = at(&PointerConstantRefusal::MutabilityMismatch {
        global_mutable: true,
    });
    let missing = at(&PointerConstantRefusal::NotAModuleGlobal);
    assert_eq!(mutable, "function 'third' bb0[1]");
    assert_eq!(missing, "function 'third' bb0[2]");
}

/// A `&[&str]` over a `[&str; 2]` table — a slice whose ELEMENT is itself a
/// fat pointer (16-byte stride) — validates and reads `'x'` from its first
/// element (the table's second string); the half-element offset 8 is refused
/// as `MisalignedOffset`.
#[test]
fn ws3_8_slice_of_str_over_a_str_table_validates_and_executes() {
    let build = |addend: i64| {
        let mut mb = ModuleBuilder::new("ws3_8_str_table");
        let u8_id = mb.add_type(Ty::U8);
        let str_id = mb.add_type(str_ty());
        mb.add_global(global(
            "AB",
            Ty::Array(u8_id, 2),
            false,
            Some(Constant::str_bytes("ab")),
        ));
        mb.add_global(global(
            "XYZ",
            Ty::Array(u8_id, 3),
            false,
            Some(Constant::str_bytes("xyz")),
        ));
        mb.add_global(global(
            "NAMES",
            Ty::Array(str_id, 2),
            false,
            Some(Constant::Array(vec![
                fat_str("AB", 0, 2),
                fat_str("XYZ", 0, 3),
            ])),
        ));
        let view_ty = Ty::FatPtr(FatPtrKind::Slice(str_id));
        let ft = mb.add_func_type(vec![], vec![Ty::U8]);
        let mut f = mb.function("first_byte", ft);
        let e = f.create_block();
        f.switch_to_block(e);
        let view = f.const_value(view_ty.clone(), fat_str("NAMES", addend, 1));
        let data = f.ptr_data(view_ty, view);
        let s = f.load(str_ty(), data);
        let bytes = f.ptr_data(str_ty(), s);
        let b = f.load(Ty::U8, bytes);
        f.ret(vec![b]);
        f.build();
        mb.build().expect("ModuleBuilder::build: test fixture")
    };
    let ok = build(16);
    assert!(
        validate_module(&ok).is_empty(),
        "{:?}",
        validate_module(&ok)
    );
    assert_eq!(run_u(&ok, "first_byte"), Ok(u128::from(b'x')));
    assert_refused_only(
        &validate_module(&build(8)),
        &["function 'first_byte'"],
        &PointerConstantRefusal::MisalignedOffset {
            offset: 8,
            element_size: 16,
        },
    );
}

/// The closure-capture pass defers these spellings to the typed walk; that
/// deferral must not SWALLOW a bad fat constant in a capture. An overlong
/// `&str` capture and one whose length word is a `bool` are each refused by
/// name, while the in-bounds capture validates.
#[test]
fn ws3_8_closure_capture_of_a_fat_constant_is_checked_by_the_typed_walk() {
    let build = |fat: Constant| {
        let mut mb = ModuleBuilder::new("ws3_8_closure_fat");
        let u8_id = mb.add_type(Ty::U8);
        mb.add_global(global(
            "BYTES",
            Ty::Array(u8_id, 5),
            false,
            Some(Constant::str_bytes("hello")),
        ));
        let body_ty = mb.add_func_type(vec![str_ty()], vec![Ty::U8]);
        let body = {
            let mut f = mb.function("body", body_ty);
            let e = f.create_block();
            let s = f.add_block_param(e, str_ty());
            f.switch_to_block(e);
            let data = f.ptr_data(str_ty(), s);
            let b = f.load(Ty::U8, data);
            f.ret(vec![b]);
            f.build()
        };
        let call_ty = mb.add_func_type(vec![], vec![Ty::U8]);
        let closure_ty = mb.add_closure_type(ClosureTy {
            func: call_ty,
            captures: vec![str_ty()],
        });
        let mut m = mb.build().expect("ModuleBuilder::build: test fixture");
        m.globals.push(global(
            "CLOSURE",
            Ty::Closure(closure_ty),
            false,
            Some(Constant::Closure {
                func: body,
                captures: vec![fat],
            }),
        ));
        m
    };
    let pointer_errors = |m: &Module| {
        validate_module(m)
            .into_iter()
            .filter(|e| {
                matches!(
                    e,
                    ValidationError::ClosureCaptureTypeMismatch { .. }
                        | ValidationError::PointerConstantRefused { .. }
                        | ValidationError::ConstTypeMismatch { .. }
                )
            })
            .collect::<Vec<_>>()
    };
    assert!(pointer_errors(&build(fat_str("BYTES", 0, 5))).is_empty());
    assert_eq!(
        refusals(&pointer_errors(&build(fat_str("BYTES", 0, 6)))),
        vec![(
            "global 'CLOSURE'".into(),
            PointerConstantRefusal::WindowOutOfBounds {
                offset: 0,
                length: 6,
                capacity: 5,
            }
        )]
    );
    let bool_length =
        Constant::Aggregate(vec![Constant::symbol_addr("BYTES"), Constant::Bool(true)]);
    let found = refusals(&pointer_errors(&build(bool_length)));
    assert!(
        matches!(found.as_slice(), [(l, PointerConstantRefusal::InvalidLength { .. })] if l == "global 'CLOSURE'"),
        "{found:?}"
    );
}

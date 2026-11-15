//! WS2.16 (F-036, the 32-bit G7 cells): reference execution on wasm32.
//!
//! Before WS2.16 the reference interpreter refused EVERY module whose target
//! was not 64-bit little-endian at function entry — even pure `usize`
//! arithmetic — so no differential evidence could exist for any 32-bit cell.
//! It now executes a pointer-width-parametric byte model on every
//! canonical-scalar-table little-endian target: `Ptr`/`Isize`/`Usize` are
//! `pointer_bits / 8` bytes, addresses are range-checked to `2^pointer_bits`,
//! fat pointers are two pointer words, and GEP faults past the address space.
//!
//! Pinned here:
//! * positive — the archived critic probe `one_module_every_target`
//!   (`critic/crate/tests/c2_format_probes.rs`) wasm32 row executes, to the
//!   same value as x86_64 for a width-independent body;
//! * negative twin — the same module on i686 (not a canonical-scalar-table
//!   target) keeps the NAMED `UnsupportedMemory` refusal;
//! * mutation controls — `usize::MAX + 1` wraps to 0 at 32 bits and not at 64;
//!   a GEP past `2^32` is UB on wasm32 and fine on x86_64; a `usize` stride is
//!   4 bytes on wasm32 and 8 on x86_64. A model that only relabels widths
//!   fails each of these;
//! * subset — v5 selects the target-indexed Lean model for wasm32; byte-model
//!   agreement is tested separately by the required Lean-execution oracle.
//!   Big-endian, malformed widths and unsupported32-bit ABIs stay refused.

use trust_ir::interpret::{InterpretErrorCode, InterpretOptions, InterpretValue, Interpreter};
use trust_ir::ty::{FatPtrKind, Ty};
use trust_ir::{CastOp, Endianness, FuncId, Module, StructPassingPolicy, TargetInfo};
use trust_ir_build::{ModuleBuilder, validate_module};

fn target(triple: &str, pointer_size: u32) -> TargetInfo {
    TargetInfo {
        triple: triple.into(),
        pointer_size,
        endianness: Endianness::Little,
        abi: None,
        struct_passing: StructPassingPolicy::NativeC,
    }
}

const X86_64: (&str, u32) = ("x86_64-unknown-linux-gnu", 8);
const WASM32: (&str, u32) = ("wasm32-unknown-unknown", 4);
const I686: (&str, u32) = ("i686-unknown-linux-gnu", 4);

fn on(mut module: Module, (triple, pointer_size): (&str, u32)) -> Module {
    module.target_info = Some(target(triple, pointer_size));
    module
}

fn run(
    module: &Module,
    args: Vec<InterpretValue>,
) -> Result<u128, trust_ir::interpret::InterpretError> {
    Interpreter::with_module(module)
        .with_options(InterpretOptions {
            fuel: 1_000_000,
            max_call_depth: 64,
            ..InterpretOptions::default()
        })
        .execute_func(FuncId::new(0), args)
        .map(|outcome| {
            outcome.returns[0]
                .as_int()
                .expect("integer return")
                .as_unsigned()
        })
}

/// The critic probe's module verbatim: `(0xFFFF_FFFF: usize) + 1`, widened to
/// `u64`. The wrap point is the pointer width.
fn critic_usize_module() -> Module {
    let mut mb = ModuleBuilder::new("critic_target");
    let sig = mb.add_func_type(vec![], vec![Ty::U64]);
    let mut fb = mb.function("program", sig);
    let e = fb.create_block();
    fb.switch_to_block(e);
    let a = fb.uconst(Ty::Usize, 0xFFFF_FFFF);
    let one = fb.uconst(Ty::Usize, 1);
    let s = fb.add(Ty::Usize, a, one);
    let w = fb.zext(Ty::Usize, Ty::U64, s);
    fb.ret(vec![w]);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

/// A width-INDEPENDENT body that still exercises the byte model: a
/// `[usize; 2]` in memory, a pointer stored through memory and loaded back,
/// GEP to the second slot, and `usize` arithmetic that never overflows.
/// Returns `a[0] + a[1] + arg` (= 42 with `arg = 2`).
fn width_independent_module() -> Module {
    let mut mb = ModuleBuilder::new("ws2_16_width_independent");
    let arr = mb.add_type(Ty::Usize);
    let arr_ty = Ty::Array(arr, 2);
    let sig = mb.add_func_type(vec![Ty::Usize], vec![Ty::U64]);
    let mut fb = mb.function("program", sig);
    let e = fb.create_block();
    let arg = fb.add_block_param(e, Ty::Usize);
    fb.switch_to_block(e);
    let slots = fb.alloca(arr_ty);
    let cell = fb.alloca(Ty::Ptr);
    fb.store(Ty::Ptr, cell, slots);
    let slots_again = fb.load(Ty::Ptr, cell);
    let zero = fb.uconst(Ty::Usize, 0);
    let one = fb.uconst(Ty::Usize, 1);
    let p0 = fb.gep(Ty::Usize, slots_again, vec![zero]);
    let p1 = fb.gep(Ty::Usize, slots_again, vec![one]);
    let forty = fb.uconst(Ty::Usize, 30);
    let ten = fb.uconst(Ty::Usize, 10);
    fb.store(Ty::Usize, p0, forty);
    fb.store(Ty::Usize, p1, ten);
    let a0 = fb.load(Ty::Usize, p0);
    let a1 = fb.load(Ty::Usize, p1);
    let sum = fb.add(Ty::Usize, a0, a1);
    let total = fb.add(Ty::Usize, sum, arg);
    let wide = fb.zext(Ty::Usize, Ty::U64, total);
    fb.ret(vec![wide]);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

/// `&a[1] as usize - &a[0] as usize` for `a: [usize; 2]`: the stride, 4 on
/// wasm32 and 8 on a 64-bit target.
fn usize_stride_module() -> Module {
    let mut mb = ModuleBuilder::new("ws2_16_stride");
    let arr = mb.add_type(Ty::Usize);
    let sig = mb.add_func_type(vec![], vec![Ty::U64]);
    let mut fb = mb.function("program", sig);
    let e = fb.create_block();
    fb.switch_to_block(e);
    let slots = fb.alloca(Ty::Array(arr, 2));
    let zero = fb.uconst(Ty::Usize, 0);
    let one = fb.uconst(Ty::Usize, 1);
    let p0 = fb.gep(Ty::Usize, slots, vec![zero]);
    let p1 = fb.gep(Ty::Usize, slots, vec![one]);
    let a0 = fb.cast(CastOp::PtrToInt, Ty::Ptr, Ty::Usize, p0);
    let a1 = fb.cast(CastOp::PtrToInt, Ty::Ptr, Ty::Usize, p1);
    let stride = fb.sub(Ty::Usize, a1, a0);
    let wide = fb.zext(Ty::Usize, Ty::U64, stride);
    fb.ret(vec![wide]);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

/// A no-provenance pointer at `base`, advanced `by` bytes with a GEP, then
/// exposed as a `u64`.
fn gep_from_module(base: u128, by: u128) -> Module {
    let mut mb = ModuleBuilder::new("ws2_16_gep_bound");
    let sig = mb.add_func_type(vec![], vec![Ty::U64]);
    let mut fb = mb.function("program", sig);
    let e = fb.create_block();
    fb.switch_to_block(e);
    let base = fb.uconst(Ty::Usize, base);
    let ptr = fb.cast(CastOp::IntToPtr, Ty::Usize, Ty::Ptr, base);
    let by = fb.uconst(Ty::Usize, by);
    let moved = fb.gep(Ty::U8, ptr, vec![by]);
    let addr = fb.cast(CastOp::PtrToInt, Ty::Ptr, Ty::U64, moved);
    fb.ret(vec![addr]);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

/// A `&str`-shaped fat pointer (data + `usize` length) stored to memory and
/// loaded back; returns the length. Its image is two pointer words.
fn fat_pointer_module(pointer_bits: u32) -> Module {
    let len_ty = if pointer_bits == 32 { Ty::U32 } else { Ty::U64 };
    let fat = Ty::FatPtr(FatPtrKind::Str);
    let mut mb = ModuleBuilder::new("ws2_16_fat");
    let sig = mb.add_func_type(vec![], vec![Ty::U64]);
    let mut fb = mb.function("program", sig);
    let e = fb.create_block();
    fb.switch_to_block(e);
    let bytes = fb.alloca(Ty::U32);
    let len = fb.uconst(len_ty.clone(), 3);
    let value = fb.ptr_from_parts(fat.clone(), len_ty.clone(), bytes, len);
    let cell = fb.alloca(fat.clone());
    fb.store(fat.clone(), cell, value);
    let back = fb.load(fat.clone(), cell);
    let meta = fb.ptr_metadata(fat, len_ty.clone(), back);
    let wide = if len_ty == Ty::U64 {
        meta
    } else {
        fb.zext(len_ty, Ty::U64, meta)
    };
    fb.ret(vec![wide]);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

/// `critic ... one_module_every_target`, wasm32 row (F-036). Positive: a
/// width-independent module executes on wasm32 to the same value as x86_64,
/// with a real round trip through memory (`Ptr` and `usize` images).
#[test]
fn critic_one_module_every_target_wasm32_row_executes_like_x86_64() {
    let arg = || vec![InterpretValue::int(Ty::Usize, 2).expect("usize arg")];
    let x86 = run(&on(width_independent_module(), X86_64), arg()).expect("x86_64 executes");
    let wasm = run(&on(width_independent_module(), WASM32), arg()).expect("wasm32 executes");
    assert_eq!(x86, 42);
    assert_eq!(wasm, x86, "the wasm32 row must execute to the x86_64 value");
    // The critic's exact module is valid and executes on every target row now.
    for row in [X86_64, ("riscv64gc-unknown-linux-gnu", 8), WASM32] {
        let module = on(critic_usize_module(), row);
        assert!(validate_module(&module).is_empty(), "{}", row.0);
        run(&module, vec![]).unwrap_or_else(|e| panic!("{}: {e:?}", row.0));
    }
}

/// Negative twin: the same modules on i686 — a 4-byte-pointer target whose
/// scalar ABI is NOT the canonical table (`i64` aligns to 4) — keep the named
/// `UnsupportedMemory` refusal. So does a big-endian 32-bit target.
#[test]
fn critic_one_module_every_target_i686_twin_is_refused_by_name() {
    for module in [
        on(critic_usize_module(), I686),
        on(width_independent_module(), I686),
    ] {
        let args = if module.name == "critic_target" {
            vec![]
        } else {
            vec![InterpretValue::int(Ty::Usize, 2).unwrap()]
        };
        let error = run(&module, args).expect_err("i686 is not executable");
        assert_eq!(
            error.code,
            InterpretErrorCode::UnsupportedMemory,
            "{error:?}"
        );
        assert!(error.message.contains("i686"), "{}", error.message);
    }
    let mut big = on(critic_usize_module(), WASM32);
    big.target_info.as_mut().unwrap().endianness = Endianness::Big;
    let error = run(&big, vec![]).expect_err("big-endian is not executable");
    assert_eq!(
        error.code,
        InterpretErrorCode::UnsupportedMemory,
        "{error:?}"
    );
}

/// Mutation control 1: `usize::MAX + 1` wraps to 0 at 32 bits, not at 64.
#[test]
fn usize_max_plus_one_wraps_at_the_target_pointer_width() {
    assert_eq!(run(&on(critic_usize_module(), WASM32), vec![]).unwrap(), 0);
    assert_eq!(
        run(&on(critic_usize_module(), X86_64), vec![]).unwrap(),
        0x1_0000_0000
    );
    // Target-free keeps the 64-bit reference model, byte-identical.
    assert_eq!(run(&critic_usize_module(), vec![]).unwrap(), 0x1_0000_0000);
}

/// Mutation control 2: a GEP whose result lands past `2^32 - 1` is UB on
/// wasm32 (the pointer has no 4-byte image) and ordinary arithmetic at 64 bits.
#[test]
fn gep_past_the_32_bit_address_space_is_ub_on_wasm32() {
    let past = gep_from_module(0xFFFF_FFF0, 0x20);
    let error = run(&on(past.clone(), WASM32), vec![]).expect_err("GEP past 2^32");
    assert_eq!(
        error.code,
        InterpretErrorCode::UndefinedBehavior,
        "{error:?}"
    );
    assert!(error.message.contains("GEP"), "{}", error.message);
    assert_eq!(
        run(&on(past, X86_64), vec![]).unwrap(),
        0x1_0000_0010,
        "64-bit GEP is unchanged"
    );
    // In range, the same GEP is fine on wasm32 — the check is the bound, not
    // a blanket refusal.
    let inside = gep_from_module(0xFFFF_FF00, 0x20);
    assert_eq!(run(&on(inside, WASM32), vec![]).unwrap(), 0xFFFF_FF20);
}

/// Mutation control 3: the byte model is width-parametric, not relabelled —
/// a `usize` stride is 4 bytes on wasm32 and 8 on x86_64, and a fat pointer's
/// memory image is two pointer words and round-trips its metadata.
#[test]
fn pointer_width_sizes_the_byte_model() {
    assert_eq!(run(&on(usize_stride_module(), WASM32), vec![]).unwrap(), 4);
    assert_eq!(run(&on(usize_stride_module(), X86_64), vec![]).unwrap(), 8);
    assert_eq!(run(&on(fat_pointer_module(32), WASM32), vec![]).unwrap(), 3);
    assert_eq!(run(&on(fat_pointer_module(64), X86_64), vec![]).unwrap(), 3);
    // A 64-bit metadata word is the wrong canonical type on wasm32.
    let error =
        run(&on(fat_pointer_module(64), WASM32), vec![]).expect_err("u64 str length on wasm32");
    assert_eq!(error.code, InterpretErrorCode::TypeError, "{error:?}");
}

/// Entry arguments are built outside the run at the 64-bit reference width;
/// a `usize` the 32-bit target cannot represent is refused, never truncated.
#[test]
fn wasm32_entry_usize_argument_must_fit_the_pointer_width() {
    let module = on(width_independent_module(), WASM32);
    let error = run(
        &module,
        vec![InterpretValue::int(Ty::Usize, 1 << 32).unwrap()],
    )
    .expect_err("2^32 does not fit a wasm32 usize");
    assert_eq!(error.code, InterpretErrorCode::TypeError, "{error:?}");
    // The explicit-width constructor spells the same argument directly.
    assert_eq!(
        run(
            &module,
            vec![InterpretValue::int_at(Ty::Usize, 2, 32).unwrap()]
        )
        .unwrap(),
        42
    );
}

/// v5 admits both complete32-bit byte-model probes; its unrelated
/// instruction/type restrictions remain active.
#[test]
fn wasm32_module_selects_the_proved_conformance_byte_model() {
    for module in [
        on(critic_usize_module(), WASM32),
        on(width_independent_module(), WASM32),
    ] {
        assert!(module.check_conformance_subset().is_ok(), "{}", module.name);
        assert!(
            trust_ir_conformance::subset::module_subset_violations(&module).is_empty(),
            "{}",
            module.name
        );
    }
}

// ── Review probes (WS2.16 adversarial pass) ───────────────────────────────

/// `usize` SUBTRACTION wraps at the target width too (the implementer pinned
/// only addition): `0 - 1` is `0xFFFF_FFFF` on wasm32 and `u64::MAX` at 64.
fn usize_zero_minus_one() -> Module {
    let mut mb = ModuleBuilder::new("ws2_16_sub_wrap");
    let sig = mb.add_func_type(vec![], vec![Ty::U64]);
    let mut fb = mb.function("program", sig);
    let e = fb.create_block();
    fb.switch_to_block(e);
    let zero = fb.uconst(Ty::Usize, 0);
    let one = fb.uconst(Ty::Usize, 1);
    let d = fb.sub(Ty::Usize, zero, one);
    let w = fb.zext(Ty::Usize, Ty::U64, d);
    fb.ret(vec![w]);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

#[test]
fn probe_usize_sub_wraps_at_target_width() {
    assert_eq!(
        run(&on(usize_zero_minus_one(), WASM32), vec![]).unwrap(),
        0xFFFF_FFFF
    );
    assert_eq!(
        run(&on(usize_zero_minus_one(), X86_64), vec![]).unwrap(),
        u128::from(u64::MAX)
    );
}

/// `isize::MIN / -1` overflows at the TARGET width: UB on wasm32 (the 32-bit
/// `isize::MIN`), ordinary arithmetic at 64 bits. A model that only relabels
/// widths cannot tell these apart.
fn isize_min32_div_minus_one() -> Module {
    let mut mb = ModuleBuilder::new("ws2_16_sdiv");
    let sig = mb.add_func_type(vec![], vec![Ty::I64]);
    let mut fb = mb.function("program", sig);
    let e = fb.create_block();
    fb.switch_to_block(e);
    let min = fb.iconst(Ty::Isize, i128::from(i32::MIN));
    let neg = fb.iconst(Ty::Isize, -1);
    let q = fb.sdiv(Ty::Isize, min, neg);
    let w = fb.sext(Ty::Isize, Ty::I64, q);
    fb.ret(vec![w]);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

#[test]
fn probe_isize_signed_overflow_is_target_width_sensitive() {
    let e = run(&on(isize_min32_div_minus_one(), WASM32), vec![])
        .expect_err("i32::MIN / -1 overflows a 32-bit isize");
    assert_eq!(e.code, InterpretErrorCode::UndefinedBehavior, "{e:?}");
    assert_eq!(
        run(&on(isize_min32_div_minus_one(), X86_64), vec![]).unwrap(),
        1u128 << 31
    );
}

/// `IntToPtr` of an address past `2^32 - 1` is UB on wasm32 (no 4-byte
/// image), and an ordinary no-provenance pointer at 64 bits.
fn int_to_ptr_module(address: u128) -> Module {
    let mut mb = ModuleBuilder::new("ws2_16_int_to_ptr");
    let sig = mb.add_func_type(vec![], vec![Ty::U64]);
    let mut fb = mb.function("program", sig);
    let e = fb.create_block();
    fb.switch_to_block(e);
    let a = fb.uconst(Ty::U64, address);
    let p = fb.cast(CastOp::IntToPtr, Ty::U64, Ty::Ptr, a);
    let back = fb.cast(CastOp::PtrToInt, Ty::Ptr, Ty::U64, p);
    fb.ret(vec![back]);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

#[test]
fn probe_int_to_ptr_past_the_address_space_is_ub_on_wasm32() {
    let m = int_to_ptr_module(1 << 32);
    let e = run(&on(m.clone(), WASM32), vec![]).expect_err("2^32 has no wasm32 pointer image");
    assert_eq!(e.code, InterpretErrorCode::UndefinedBehavior, "{e:?}");
    assert_eq!(run(&on(m, X86_64), vec![]).unwrap(), 1u128 << 32);
    assert_eq!(
        run(&on(int_to_ptr_module(0xFFFF_FFFF), WASM32), vec![]).unwrap(),
        0xFFFF_FFFF
    );
}

/// The execution's pointer width must not leak out of the run — including
/// when the run ENDS IN AN ERROR (the scope is RAII, not a happy-path reset).
#[test]
fn probe_pointer_width_does_not_leak_out_of_a_run() {
    let _ = run(&on(critic_usize_module(), WASM32), vec![]).unwrap();
    let outside = InterpretValue::int(Ty::Usize, 1 << 32).expect("usize");
    assert_eq!(
        outside.as_int().unwrap().bits,
        64,
        "after a clean wasm32 run"
    );
    let _ = run(&on(int_to_ptr_module(1 << 32), WASM32), vec![]).expect_err("UB");
    let outside = InterpretValue::int(Ty::Usize, 1 << 32).expect("usize");
    assert_eq!(
        outside.as_int().unwrap().bits,
        64,
        "after a failed wasm32 run"
    );
    assert_eq!(outside.as_int().unwrap().as_unsigned(), 1 << 32);
}

/// A `dyn`-tail fat pointer is two pointer WORDS on wasm32 too — its
/// metadata lane is a thin `Ptr` (4 bytes), not a length.
fn trait_object_module() -> Module {
    let mut mb = ModuleBuilder::new("ws2_16_dyn");
    let fat = Ty::FatPtr(FatPtrKind::TraitObject { trait_id: 0 });
    let sig = mb.add_func_type(vec![], vec![Ty::U64]);
    let mut fb = mb.function("program", sig);
    let e = fb.create_block();
    fb.switch_to_block(e);
    let obj = fb.alloca(Ty::U32);
    let vtable = fb.alloca(Ty::U32);
    let value = fb.ptr_from_parts(fat.clone(), Ty::Ptr, obj, vtable);
    let cell = fb.alloca(fat.clone());
    fb.store(fat.clone(), cell, value);
    let back = fb.load(fat.clone(), cell);
    let data = fb.ptr_data(fat.clone(), back);
    let lhs = fb.cast(CastOp::PtrToInt, Ty::Ptr, Ty::U64, data);
    let rhs = fb.cast(CastOp::PtrToInt, Ty::Ptr, Ty::U64, obj);
    let d = fb.sub(Ty::U64, lhs, rhs);
    fb.ret(vec![d]);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

#[test]
fn probe_trait_object_fat_pointer_round_trips_on_wasm32() {
    assert_eq!(run(&on(trait_object_module(), WASM32), vec![]).unwrap(), 0);
    assert_eq!(run(&on(trait_object_module(), X86_64), vec![]).unwrap(), 0);
}

/// A legitimate wasm32 module must not be refused by the VALIDATOR either:
/// a `&str` whose metadata lane is the target's `U32` is well-formed there.
#[test]
fn probe_wasm32_fat_pointer_module_validates() {
    let m = on(fat_pointer_module(32), WASM32);
    assert!(validate_module(&m).is_empty(), "{:?}", validate_module(&m));
    let m64 = on(fat_pointer_module(64), X86_64);
    assert!(
        validate_module(&m64).is_empty(),
        "{:?}",
        validate_module(&m64)
    );
}

/// The pointer width is a property of the RUN, not of the thread: a host
/// model that re-enters the interpreter on a 64-bit module from inside a
/// wasm32 run must not leave the 64-bit width installed behind it. The host
/// below does exactly that and then mints its `usize` result with the
/// width-implicit `InterpretValue::int`, so a lost restore makes the result a
/// 64-bit `usize` and `check_host_result` refuses the call by type.
#[test]
fn probe_a_nested_64_bit_run_does_not_leak_its_width_into_the_caller() {
    use trust_ir::interpret::{HostCalls, HostState, InterpretResult};
    use trust_ir::{FuncTy, Function};

    struct Reentrant;
    impl HostCalls for Reentrant {
        fn call(
            &self,
            callee: &Function,
            _sig: &FuncTy,
            _args: &[InterpretValue],
            _host: &mut HostState,
        ) -> Option<InterpretResult<Vec<InterpretValue>>> {
            if callee.name != "nested_probe" {
                return None;
            }
            // A whole 64-bit execution, nested inside the wasm32 one.
            let inner = on(critic_usize_module(), X86_64);
            let value = run(&inner, vec![]).expect("nested 64-bit run");
            assert_eq!(value, 0x1_0000_0000, "the nested run is 64-bit");
            // Width-implicit: this is 32-bit only if the scope was restored.
            Some(Ok(vec![InterpretValue::int(Ty::Usize, 10).unwrap()]))
        }
    }

    let mut mb = ModuleBuilder::new("ws2_16_reentrant");
    let probe_sig = mb.add_func_type(vec![], vec![Ty::Usize]);
    let probe = mb.declare_function("nested_probe", probe_sig);
    let sig = mb.add_func_type(vec![], vec![Ty::U64]);
    let mut fb = mb.function("program", sig);
    let e = fb.create_block();
    fb.switch_to_block(e);
    let from_host = fb.call(probe, vec![]);
    let thirty_two = fb.uconst(Ty::Usize, 32);
    let sum = fb.add(Ty::Usize, from_host, thirty_two);
    let wide = fb.zext(Ty::Usize, Ty::U64, sum);
    fb.ret(vec![wide]);
    fb.build();
    let module = on(
        mb.build().expect("ModuleBuilder::build: test fixture"),
        WASM32,
    );

    let outcome = Interpreter::with_module(&module)
        .with_host(&Reentrant)
        .execute_func(FuncId::new(1), [])
        .expect("the wasm32 caller resumes at its own width");
    assert_eq!(
        outcome.returns[0].as_int().unwrap().as_unsigned(),
        42,
        "the host result must be a 32-bit usize the wasm32 run accepts"
    );
    // And the width is back to the 64-bit reference model outside the run.
    assert_eq!(
        InterpretValue::int(Ty::Usize, 1 << 32)
            .unwrap()
            .as_int()
            .unwrap()
            .bits,
        64
    );
}

/// Executed and in-subset implies one of the two supported little-endian
/// byte models. Unknown ABIs and malformed representations cannot become
/// differential evidence merely because they carry a target name.
#[test]
fn executed_and_in_subset_implies_a_supported_little_endian_byte_model() {
    let rows: &[(&str, u32, Endianness)] = &[
        ("x86_64-unknown-linux-gnu", 8, Endianness::Little),
        ("aarch64-apple-darwin", 8, Endianness::Little),
        ("riscv64gc-unknown-linux-gnu", 8, Endianness::Little),
        ("wasm64-unknown-unknown", 8, Endianness::Little),
        ("wasm32-unknown-unknown", 4, Endianness::Little),
        ("wasm32-unknown-unknown", 4, Endianness::Big),
        ("i686-unknown-linux-gnu", 4, Endianness::Little),
        ("powerpc64le-unknown-linux-gnu", 8, Endianness::Little),
        ("x86_64-unknown-linux-gnu", 8, Endianness::Big),
        ("avr-unknown-unknown", 2, Endianness::Little),
        ("x86_64-unknown-linux-gnu", u32::MAX, Endianness::Little),
    ];
    let mut executed_and_in_subset = 0usize;
    for &(triple, pointer_size, endianness) in rows {
        // A subset-CLEAN body (`Ty::Usize` is not in the proven subset until
        // WS2.17, so a `usize` module would make the in-subset half vacuous
        // on every row and prove nothing).
        let mut module = subset_clean_module();
        module.target_info = Some(TargetInfo {
            triple: triple.into(),
            pointer_size,
            endianness,
            abi: None,
            struct_passing: StructPassingPolicy::NativeC,
        });
        let executes = run(&module, vec![]).is_ok();
        let in_subset = module.check_conformance_subset().is_ok();
        if executes && in_subset {
            executed_and_in_subset += 1;
            assert!(
                pointer_size == 8
                    || (pointer_size == 4 && triple.split('-').next() == Some("wasm32")),
                "{triple}/{endianness:?} has no proved byte model"
            );
            assert_eq!(
                endianness,
                Endianness::Little,
                "{triple} is not little-endian"
            );
        }
    }
    assert!(
        executed_and_in_subset == 5,
        "the implication must be non-vacuous"
    );
    // The same body is now both executable and admitted on canonical wasm32.
    let wasm = on(subset_clean_module(), WASM32);
    assert!(run(&wasm, vec![]).is_ok());
    assert!(wasm.check_conformance_subset().is_ok());
    assert!(subset_clean_module().check_conformance_subset().is_ok());
}

/// A body with no pointer-width type at all: `40 + 2` in `u64`. Inside the
/// proven subset on a 64-bit little-endian target, executable on every
/// canonical-table one.
fn subset_clean_module() -> Module {
    let mut mb = ModuleBuilder::new("ws2_16_subset_clean");
    let sig = mb.add_func_type(vec![], vec![Ty::U64]);
    let mut fb = mb.function("program", sig);
    let e = fb.create_block();
    fb.switch_to_block(e);
    let a = fb.uconst(Ty::U64, 40);
    let b = fb.uconst(Ty::U64, 2);
    let s = fb.add(Ty::U64, a, b);
    fb.ret(vec![s]);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

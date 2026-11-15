//! Fixtures of the b5 `Nat` handle rows, shared by the `two_language_b5`
//! target and by `trust-ir-cli`'s `two_language_cli` target (which runs the
//! handle program through the real CLI). Only trust-ir / trust-ir-build are
//! used here.
#![allow(dead_code)]

use trust_ir::inst::ICmpOp;
use trust_ir::{
    BodyGate, Endianness, FuncId, Module, Producer, StructPassingPolicy, TargetInfo, Ty, ValueId,
};
use trust_ir_build::builder::{FunctionBuilder, HandleRuntimeDecls};
use trust_ir_build::{HandleRuntimePin, ModuleBuilder, TRUSTED_HANDLE_RUNTIMES};

pub fn nat() -> Ty {
    Ty::handle("Nat", "trust_bignum::Nat")
}

pub fn target() -> TargetInfo {
    TargetInfo {
        triple: "aarch64-apple-darwin".into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: Some("aapcs64".into()),
        struct_passing: StructPassingPolicy::NativeC,
    }
}

pub fn nat_pin() -> &'static HandleRuntimePin {
    TRUSTED_HANDLE_RUNTIMES
        .iter()
        .find(|pin| pin.name == "Nat" && pin.runtime == "trust_bignum::Nat")
        .expect("v1 pins (Nat, trust_bignum::Nat)")
}

pub fn clean_gate() -> BodyGate {
    BodyGate::Gated {
        authority: "clean-kernel-nat-rec".into(),
        evidence: None,
    }
}

pub fn rust_gate() -> BodyGate {
    BodyGate::Gated {
        authority: "trust-verify".into(),
        evidence: None,
    }
}

/// The carrier the SAME program is built over. `Nat` = the design's end state (the pinned
/// opaque handle). `U64` = the closest handle-free analog (every pinned entry point replaced
/// by the machine operation with the same meaning below 2^64; `sub` is truncating like the
/// pinned one). The analog exists ONLY as the well-formed baseline of the wire-version twin and
/// of the interpreter GAP ratchet — it is never claimed to CARRY a Nat.
#[derive(Clone)]
pub enum Carrier {
    Nat(HandleRuntimeDecls),
    U64,
}

impl Carrier {
    pub fn ty(&self) -> Ty {
        match self {
            Carrier::Nat(decls) => decls.handle.clone(),
            Carrier::U64 => Ty::U64,
        }
    }

    pub fn entry(decls: &HandleRuntimeDecls, role: &str) -> FuncId {
        decls
            .entry(role)
            .unwrap_or_else(|| panic!("pinned role `{role}`"))
    }

    pub fn lift_u64(&self, fb: &mut FunctionBuilder<'_>, v: ValueId) -> ValueId {
        match self {
            Carrier::Nat(d) => fb.call(Self::entry(d, "from_u64"), vec![v]),
            Carrier::U64 => fb.copy(Ty::U64, v),
        }
    }

    pub fn add(&self, fb: &mut FunctionBuilder<'_>, a: ValueId, b: ValueId) -> ValueId {
        match self {
            Carrier::Nat(d) => fb.call(Self::entry(d, "add"), vec![a, b]),
            Carrier::U64 => fb.add(Ty::U64, a, b),
        }
    }

    /// Truncating subtraction (`a - b`, saturating at zero) — the pinned `sub`'s meaning.
    pub fn sub(&self, fb: &mut FunctionBuilder<'_>, a: ValueId, b: ValueId) -> ValueId {
        match self {
            Carrier::Nat(d) => fb.call(Self::entry(d, "sub"), vec![a, b]),
            Carrier::U64 => {
                let under = fb.icmp(ICmpOp::Ult, Ty::U64, a, b);
                let diff = fb.sub(Ty::U64, a, b);
                let zero = fb.uconst(Ty::U64, 0);
                fb.select(Ty::U64, under, zero, diff)
            }
        }
    }

    pub fn is_zero(&self, fb: &mut FunctionBuilder<'_>, a: ValueId) -> ValueId {
        match self {
            Carrier::Nat(d) => fb.call(Self::entry(d, "is_zero"), vec![a]),
            Carrier::U64 => {
                let zero = fb.uconst(Ty::U64, 0);
                fb.icmp(ICmpOp::Eq, Ty::U64, a, zero)
            }
        }
    }
}

/// How the Rust caller feeds the Clean callee. `Skewed` is the negative twin of the call
/// edge: the Rust side passes its raw `u64` where the Clean side takes a `Nat`.
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum CallEdge {
    Exact,
    Skewed,
}

/// ```text
/// [C decl ] trust_bignum_nat_{from_u64,add,sub,is_zero}          (pinned, bodyless; Nat only)
/// [Clean  ] nat_double(n: Nat) -> Nat        -- Lean: def double : Nat -> Nat
///              bb0(n):  z = is_zero(n); condbr z, bb1, bb2       --   | 0     => 0
///              bb1:     br bb3(n)                                --   | n + 1 => double n + 2
///              bb2:     p = sub(n, from_u64(1)); r = nat_double(p);
///                       s = add(r, from_u64(2)); br bb3(s)
///              bb3(res): ret res
/// [Clean  ] nat_mul(a: Nat, b: Nat) -> Nat   -- DERIVED multiplication by recursion on b
/// [TRust  ] rust_nat_or(a: Nat, b: Nat) -> Nat = select(is_zero(a), b, copy a)
/// [TRust  ] rust_double_eq(k: u64, expect: u64) -> bool
///              d = nat_double(from_u64(k)); e = from_u64(expect)
///              is_zero(sub(d, e)) && is_zero(sub(e, d))           (the only observation
///                                                                  the four pins allow)
/// [TRust  ] program() -> bool = rust_double_eq(21, 42)
/// ```
pub fn build_program(name: &str, use_nat: bool, edge: CallEdge) -> Module {
    let mut mb = ModuleBuilder::new_with_target_info(name, target());
    let carrier = if use_nat {
        Carrier::Nat(
            mb.declare_handle_runtime(nat_pin())
                .expect("pinned declarations on an empty module"),
        )
    } else {
        Carrier::U64
    };
    let c = carrier.ty();
    let unop = mb.add_func_type(vec![c.clone()], vec![c.clone()]);
    let binop = mb.add_func_type(vec![c.clone(), c.clone()], vec![c.clone()]);
    let eq_sig = mb.add_func_type(vec![Ty::U64, Ty::U64], vec![Ty::Bool]);
    let nullary = mb.add_func_type(vec![], vec![Ty::Bool]);

    // ---- [Clean] nat_double ------------------------------------------------
    let nat_double = {
        let me = mb
            .peek_next_func_id()
            .expect("peek_next_func_id: test fixture");
        let mut fb = mb.function("nat_double", unop);
        fb.set_producer(Producer::Clean);
        fb.set_display_path("NatLane.double");
        fb.set_body_gate(clean_gate());
        let bb0 = fb.create_block();
        let n = fb.add_block_param(bb0, c.clone());
        let bb1 = fb.create_block();
        let bb2 = fb.create_block();
        let bb3 = fb.create_block();
        let res = fb.add_block_param(bb3, c.clone());
        fb.switch_to_block(bb0);
        let z = carrier.is_zero(&mut fb, n);
        fb.condbr(z, bb1, vec![], bb2, vec![]);
        fb.switch_to_block(bb1);
        fb.br(bb3, vec![n]);
        fb.switch_to_block(bb2);
        let one = fb.uconst(Ty::U64, 1);
        let one_n = carrier.lift_u64(&mut fb, one);
        let pred = carrier.sub(&mut fb, n, one_n);
        let rec = fb.call(me, vec![pred]);
        let two = fb.uconst(Ty::U64, 2);
        let two_n = carrier.lift_u64(&mut fb, two);
        let sum = carrier.add(&mut fb, rec, two_n);
        fb.br(bb3, vec![sum]);
        fb.switch_to_block(bb3);
        fb.ret(vec![res]);
        let id = fb.build();
        assert_eq!(id, me);
        id
    };

    // ---- [Clean] nat_mul (derived: NOT a pinned entry point) ----------------
    {
        let me = mb
            .peek_next_func_id()
            .expect("peek_next_func_id: test fixture");
        let mut fb = mb.function("nat_mul", binop);
        fb.set_producer(Producer::Clean);
        fb.set_display_path("NatLane.mul");
        fb.set_body_gate(clean_gate());
        let bb0 = fb.create_block();
        let a = fb.add_block_param(bb0, c.clone());
        let b = fb.add_block_param(bb0, c.clone());
        let bb1 = fb.create_block();
        let bb2 = fb.create_block();
        fb.switch_to_block(bb0);
        let z = carrier.is_zero(&mut fb, b);
        fb.condbr(z, bb1, vec![], bb2, vec![]);
        fb.switch_to_block(bb1);
        let zero = fb.uconst(Ty::U64, 0);
        let zero_n = carrier.lift_u64(&mut fb, zero);
        fb.ret(vec![zero_n]);
        fb.switch_to_block(bb2);
        let one = fb.uconst(Ty::U64, 1);
        let one_n = carrier.lift_u64(&mut fb, one);
        let pred = carrier.sub(&mut fb, b, one_n);
        let rec = fb.call(me, vec![a, pred]);
        let sum = carrier.add(&mut fb, rec, a);
        fb.ret(vec![sum]);
        fb.build();
    }

    // ---- [TRust] rust_nat_or: Copy + Select transport of a Nat --------------
    {
        let mut fb = mb.function("rust_nat_or", binop);
        fb.set_producer(Producer::TRust);
        fb.set_display_path("nat_lane::nat_or");
        fb.set_body_gate(rust_gate());
        let bb0 = fb.create_block();
        let a = fb.add_block_param(bb0, c.clone());
        let b = fb.add_block_param(bb0, c.clone());
        fb.switch_to_block(bb0);
        let z = carrier.is_zero(&mut fb, a);
        let a2 = fb.copy(c.clone(), a);
        let out = fb.select(c.clone(), z, b, a2);
        fb.ret(vec![out]);
        fb.build();
    }

    // ---- [TRust] rust_double_eq: the Rust -> Lean call edge ------------------
    let rust_double_eq = {
        let mut fb = mb.function("rust_double_eq", eq_sig);
        fb.set_producer(Producer::TRust);
        fb.set_display_path("nat_lane::double_eq");
        fb.set_body_gate(rust_gate());
        let bb0 = fb.create_block();
        let k = fb.add_block_param(bb0, Ty::U64);
        let expect = fb.add_block_param(bb0, Ty::U64);
        fb.switch_to_block(bb0);
        let arg = match edge {
            CallEdge::Exact => carrier.lift_u64(&mut fb, k),
            // The stale producer: hands the Clean callee a raw machine word.
            CallEdge::Skewed => k,
        };
        let d = fb.call(nat_double, vec![arg]);
        let e = carrier.lift_u64(&mut fb, expect);
        let d_minus_e = carrier.sub(&mut fb, d, e);
        let e_minus_d = carrier.sub(&mut fb, e, d);
        let le = carrier.is_zero(&mut fb, d_minus_e);
        let ge = carrier.is_zero(&mut fb, e_minus_d);
        let eq = fb.select(Ty::Bool, le, ge, le);
        fb.ret(vec![eq]);
        fb.build()
    };

    // ---- [TRust] program ------------------------------------------------------
    {
        let mut fb = mb.function("program", nullary);
        fb.set_producer(Producer::TRust);
        fb.set_display_path("nat_lane::program");
        fb.set_body_gate(rust_gate());
        let bb0 = fb.create_block();
        fb.switch_to_block(bb0);
        let k = fb.uconst(Ty::U64, 21);
        let expect = fb.uconst(Ty::U64, 42);
        let out = fb.call(rust_double_eq, vec![k, expect]);
        fb.ret(vec![out]);
        fb.build();
    }

    mb.build().expect("ModuleBuilder::build: test fixture")
}

pub fn nat_program() -> Module {
    build_program("b5_nat_handle", true, CallEdge::Exact)
}

pub fn u64_program() -> Module {
    build_program("b5_u64_analog", false, CallEdge::Exact)
}

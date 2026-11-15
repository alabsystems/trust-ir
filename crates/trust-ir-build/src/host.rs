// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Reference host models of the pinned trusted runtimes (roadmap WS2.13,
//! closes the model half of F-035).
//!
//! The reference interpreter executes a bodyless declaration only through an
//! installed [`HostCalls`] model (WS2.12). This module supplies the ONE such
//! model this repository owns, [`PinnedHandleHost`], keyed by the validator's
//! own pin tables and nothing else:
//!
//! * every entry point of [`TRUSTED_HANDLE_RUNTIMES`] — the
//!   `("Nat", "trust_bignum::Nat")` row, modelled over [`Nat`], a
//!   dependency-free little-endian base-2^64 magnitude with the Lean `Nat`
//!   semantics the row pins (`sub` truncates at zero, `n / 0 = 0`,
//!   `n % 0 = n`, `to_u64` ABORTS when the value does not fit); and
//! * every entry point of [`TRUSTED_RC_RUNTIMES`] — the Clean triple
//!   `clean_inc` / `clean_dec` / `clean_is_exclusive`, which the model
//!   CLASSIFIES ([`HostCalls::rc_op`]) so the interpreter performs the count
//!   on its own `HeapAlloc { origin: CleanHeap }` cells.
//!
//! A model serves a call only when the declaration carries the EXACT pinned
//! signature and calling convention; any other declaration of a pinned symbol
//! is "not mine" (`None`), so the interpreter refuses it as `UnsupportedCall`
//! exactly as if no host were installed. There is one exception. A VARIADIC
//! declaration of a pinned symbol at the pinned calling convention is refused
//! as `SignatureMismatch` ("non-executable vararg signature",
//! [`HostCalls::models_fixed_arity`]), because every pinned entry point is
//! fixed-arity. The test
//! `every_pinned_entry_point_has_a_host_model` fails when a pin row gains an
//! entry point this module does not model.
//!
//! # These are TRUSTED models, and a run that used one is host-assisted
//!
//! `TRUST.md` items 9 and 13 name the real runtimes (`trust-bignum`'s
//! `handle_abi.rs` shims, Clean's C runtime) as trusted base. A host model is a
//! second, independent statement of what those runtimes do — written from the
//! pin tables' documented semantics, not derived from the runtimes' code — so
//! a run that went through it is EVIDENCE ABOUT THE MODEL'S READING OF THE
//! RUNTIME, never in-format execution and never evidence for items 9/13
//! themselves. The interpreter counts every served call in
//! `InterpretOutcome::host_calls`; a consumer that presents a `host_calls > 0`
//! run as in-format execution evidence is misreporting. The differential the
//! roadmap names (the model against `trust-bignum` and against Clean's linked
//! runtime) is the only thing that can find drift between the two, and a
//! disagreement is a bug in one of them — reported, never averaged.
//!
//! # What the model DOES observe that the runtime cannot
//!
//! Handle liveness. Item 9(c) discloses that nothing in TrustIr or TrustCg
//! detects a double release or a use after release of a `Nat` handle. The
//! model's handles live in the interpreter's per-execution `HostState`, which
//! records each release, so here — and only here — a second `drop` or any use
//! of a dropped handle is `UndefinedBehavior` by name. That is the residue
//! surfacing at run time under the model; it is not a validator guarantee and
//! does not change item 9(c).
//!
//! # A release is keyed on the one-place release table (WS3.22, F-060)
//!
//! `Inst::Dealloc` cannot state a free (it names neither the `AllocOrigin`
//! nor the layout; G18-1 excludes it from the lowering-target subset), so
//! every shipping producer spells a free as a CALL to the owning runtime, and
//! such a call is opaque to the interpreter unless the callee is KNOWN to be a
//! release. The release entry points of the pinned runtimes are named in ONE
//! place, [`crate::validate::pinned_release_entry_points`] (`trust_bignum_nat_drop`,
//! `clean_dec`), derived from the pin tables. This model decides "this call is
//! a free" by that table and by nothing else — never by a role string — and
//! models it as a dead-marking step on the released subject:
//! [`HostState::release_handle`] for a handle (runtime-opaque; no Lean model),
//! and for a `CleanHeap` cell the interpreter's own `Release`
//! (`HostRcRole::Release` via [`HostCalls::rc_op`]), which marks the cell dead
//! at count zero — the step Lean's `semRelease` performs through
//! `deallocARC`, never `semDealloc`, which is undefined behaviour on a
//! reference-counted cell (`semDealloc_arcRef_is_ub`; SPEC "A
//! reference-counted cell is released by `Release`, never by `Dealloc`"). A
//! pinned release the table stopped naming is therefore NOT served (the
//! interpreter refuses the call as `UnsupportedCall`, fail closed), never a
//! silent no-op. `RustHeap` frees (`__rust_dealloc`) are pinned by no table
//! and stay opaque.

use trust_ir::Function;
use trust_ir::interpret::{
    HostCalls, HostRcOp, HostRcRole, HostState, InterpretError, InterpretErrorCode,
    InterpretResult, InterpretValue, InterpretValueKind,
};
use trust_ir::ty::{FuncTy, HandleTy, Ty};

use crate::validate::{
    HandleEntryPoint, HandleRegistry, HandleRuntimePin, PinnedReleaseSubject, RcEntryPoint,
    RcRuntimePin, pinned_release_entry_for_symbol, rc_entry_for_symbol,
};

/// The runtime path of the one handle runtime this module models.
const NAT_RUNTIME: &str = "trust_bignum::Nat";

/// The runtime name of the one RC runtime this module models.
const CLEAN_RC_RUNTIME: &str = "clean_runtime";

/// The roles of the `trust_bignum::Nat` row this model serves. Compared
/// against the pin table by `every_pinned_entry_point_has_a_host_model`, so a
/// new pinned role fails that test until a model arm exists.
const NAT_ROLES: &[&str] = &[
    "from_u64",
    "add",
    "sub",
    "is_zero",
    "drop",
    "mul",
    "div",
    "mod",
    "beq",
    "ble",
    "fits_u64",
    "to_u64",
    "clone",
    "land",
    "lor",
    "xor",
    "shift_left",
    "shift_right",
    "pow",
];

/// The roles of the Clean RC row this model classifies.
const RC_ROLES: &[&str] = &["retain", "release", "is_unique"];

/// Reference host model of every pinned trusted runtime (module docs).
///
/// Stateless: every handle lives in the interpreter's per-execution
/// [`HostState`] under the owner name [`PinnedHandleHost::OWNER`]. Install it
/// with `Interpreter::with_host(&PinnedHandleHost::new())`; `trust-ir run
/// --host pinned` does the same.
#[derive(Debug, Clone, Copy, Default)]
pub struct PinnedHandleHost {
    _private: (),
}

impl PinnedHandleHost {
    /// The owner name this model mints its handles under. A handle minted by
    /// any other model is refused at this model's entry points by the
    /// interpreter's cross-model check.
    pub const OWNER: &'static str = "trust_ir_build::host::PinnedHandleHost";

    pub const fn new() -> Self {
        Self { _private: () }
    }

    /// Whether this model serves `entry` of the handle-runtime row `pin`:
    /// the row is one the model is written for and the role has an arm.
    pub fn models_handle_entry(pin: &HandleRuntimePin, entry: &HandleEntryPoint) -> bool {
        pin.runtime == NAT_RUNTIME && NAT_ROLES.contains(&entry.role)
    }

    /// Whether this model classifies `entry` of the RC-runtime row `pin`.
    pub fn models_rc_entry(pin: &RcRuntimePin, entry: &RcEntryPoint) -> bool {
        pin.runtime == CLEAN_RC_RUNTIME && RC_ROLES.contains(&entry.role)
    }

    /// The pinned handle-runtime row and entry point `callee` is an EXACT
    /// declaration of: pinned symbol, pinned calling convention and the
    /// pinned `FuncTy` (`HandleRuntimePin::func_ty`) — or `None`.
    fn pinned_handle_entry(
        callee: &Function,
        sig: &FuncTy,
    ) -> Option<(&'static HandleRuntimePin, &'static HandleEntryPoint)> {
        let (pin, entry) = HandleRegistry::pinned().entry_for_symbol(&callee.name)?;
        (callee.calling_conv == pin.calling_conv && *sig == pin.func_ty(entry))
            .then_some((pin, entry))
    }
}

impl HostCalls for PinnedHandleHost {
    fn call(
        &self,
        callee: &Function,
        sig: &FuncTy,
        args: &[InterpretValue],
        host: &mut HostState,
    ) -> Option<InterpretResult<Vec<InterpretValue>>> {
        let (pin, entry) = Self::pinned_handle_entry(callee, sig)?;
        if !Self::models_handle_entry(pin, entry) {
            return None;
        }
        let handle_ty = pin.handle_identity();
        // WS3.22 (F-060): whether this call is a FREE is decided by the
        // one-place release table, never by the role string. The dead-marking
        // is the same step `semDealloc` performs; after it every use of the
        // handle, a second release included, is `UndefinedBehavior`.
        if let Some(release) = pinned_release_entry_for_symbol(&callee.name) {
            if release.subject != PinnedReleaseSubject::Handle(handle_ty.clone()) {
                return None;
            }
            return Some(
                host.release_handle(&args[0], &handle_ty, PinnedHandleHost::OWNER)
                    .map(|()| Vec::new()),
            );
        }
        Some(nat_call(entry.role, &handle_ty, args, host))
    }

    fn rc_op(&self, callee: &Function, sig: &FuncTy) -> Option<HostRcOp> {
        let (pin, entry) = rc_entry_for_symbol(&callee.name)?;
        if !Self::models_rc_entry(pin, entry)
            || callee.calling_conv != pin.calling_conv
            || *sig != entry.func_ty()
        {
            return None;
        }
        // WS3.22 (F-060): the RELEASE classification comes from the
        // one-place release table; the interpreter then performs its own
        // `Release`, which marks the cell dead at count zero (Lean's
        // `semRelease` -> `deallocARC`; never `semDealloc`, which is UB on a
        // reference-counted cell).
        // A `release`-role entry the table does not name is NOT served: fail
        // closed, never a count the interpreter would silently skip.
        let is_release = pinned_release_entry_for_symbol(&callee.name)
            .is_some_and(|release| release.subject == PinnedReleaseSubject::RcCell(pin.origin));
        let role = if is_release {
            HostRcRole::Release
        } else {
            match entry.role {
                "retain" => HostRcRole::Retain,
                "is_unique" => HostRcRole::IsUnique,
                _ => return None,
            }
        };
        Some(HostRcOp {
            role,
            origin: pin.origin,
        })
    }

    /// Every entry point this model serves or classifies is pinned at a fixed
    /// arity, so a variadic declaration of one at the pinned calling
    /// convention is a forged signature. The interpreter refuses it as
    /// `SignatureMismatch` instead of reporting "no host model" (WS2.15).
    fn models_fixed_arity(&self, callee: &Function) -> bool {
        if let Some((pin, entry)) = HandleRegistry::pinned().entry_for_symbol(&callee.name) {
            return Self::models_handle_entry(pin, entry)
                && callee.calling_conv == pin.calling_conv
                && !pin.func_ty(entry).is_vararg;
        }
        rc_entry_for_symbol(&callee.name).is_some_and(|(pin, entry)| {
            Self::models_rc_entry(pin, entry)
                && callee.calling_conv == pin.calling_conv
                && !entry.func_ty().is_vararg
        })
    }
}

/// One call to a `trust_bignum::Nat` entry point, by pinned role. The
/// interpreter has already checked `args` against the pinned signature, so
/// the arities and scalar types below hold; every handle is still resolved
/// through [`HostState`], which is where cross-model, use-after-release and
/// double-release refusals come from. The RELEASE (`drop`) has no arm here on
/// purpose: it is served by [`PinnedHandleHost::call`] from the one-place
/// release table (WS3.22), so a `drop` the table stopped naming reaches the
/// `other` arm and is refused, never treated as a no-op.
fn nat_call(
    role: &str,
    nat_ty: &HandleTy,
    args: &[InterpretValue],
    host: &mut HostState,
) -> InterpretResult<Vec<InterpretValue>> {
    let owner = PinnedHandleHost::OWNER;
    let read = |host: &HostState, index: usize| -> InterpretResult<Nat> {
        host.handle::<Nat>(&args[index], nat_ty, owner).cloned()
    };
    let mint = |host: &mut HostState, value: Nat| -> InterpretResult<Vec<InterpretValue>> {
        host.mint_handle(nat_ty.clone(), owner, value)
            .map(|handle| vec![handle])
    };
    let u64_arg = |index: usize| -> InterpretResult<u64> {
        match &args[index].kind {
            InterpretValueKind::Int(int) if int.bits == 64 && !int.signed => {
                Ok(int.as_unsigned() as u64)
            }
            other => Err(model_error(
                InterpretErrorCode::TypeError,
                format!("`{role}` expected a u64 argument, got {other:?}"),
            )),
        }
    };
    let bool_result = |value: bool| Ok(vec![InterpretValue::bool(value)]);
    match role {
        "from_u64" => {
            let value = Nat::from_u64(u64_arg(0)?);
            mint(host, value)
        }
        "add" => {
            let (a, b) = (read(host, 0)?, read(host, 1)?);
            mint(host, a.add(&b)?)
        }
        "sub" => {
            let (a, b) = (read(host, 0)?, read(host, 1)?);
            mint(host, a.sub(&b))
        }
        "is_zero" => bool_result(read(host, 0)?.is_zero()),
        "mul" => {
            let (a, b) = (read(host, 0)?, read(host, 1)?);
            mint(host, a.mul(&b)?)
        }
        "div" => {
            let (a, b) = (read(host, 0)?, read(host, 1)?);
            mint(host, a.div(&b))
        }
        "mod" => {
            let (a, b) = (read(host, 0)?, read(host, 1)?);
            mint(host, a.rem(&b))
        }
        "beq" => bool_result(read(host, 0)? == read(host, 1)?),
        "ble" => bool_result(read(host, 0)? <= read(host, 1)?),
        "fits_u64" => bool_result(read(host, 0)?.fits_u64()),
        "to_u64" => {
            let a = read(host, 0)?;
            let Some(value) = a.to_u64() else {
                // The pinned `to_u64` ABORTS on a value above `u64::MAX`
                // (never wraps): under panic=abort that is process
                // termination, which the interpreter spells `Panic`.
                return Err(model_error(
                    InterpretErrorCode::Panic,
                    "`to_u64` of a Nat above u64::MAX aborts (the pinned projection is checked, \
                     never wrapping)",
                ));
            };
            Ok(vec![InterpretValue::int(Ty::U64, i128::from(value))?])
        }
        "clone" => {
            let a = read(host, 0)?;
            mint(host, a)
        }
        "land" => {
            let (a, b) = (read(host, 0)?, read(host, 1)?);
            mint(host, a.land(&b))
        }
        "lor" => {
            let (a, b) = (read(host, 0)?, read(host, 1)?);
            mint(host, a.lor(&b))
        }
        "xor" => {
            let (a, b) = (read(host, 0)?, read(host, 1)?);
            mint(host, a.xor(&b))
        }
        "shift_left" => {
            let (a, b) = (read(host, 0)?, read(host, 1)?);
            mint(host, a.shift_left(&b)?)
        }
        "shift_right" => {
            let (a, b) = (read(host, 0)?, read(host, 1)?);
            mint(host, a.shift_right(&b))
        }
        "pow" => {
            let (a, b) = (read(host, 0)?, read(host, 1)?);
            mint(host, a.pow(&b)?)
        }
        other => Err(model_error(
            InterpretErrorCode::UnsupportedCall,
            format!("pinned role `{other}` has no arm in the reference Nat model"),
        )),
    }
}

fn model_error(code: InterpretErrorCode, message: impl Into<String>) -> InterpretError {
    InterpretError::new(code, format!("reference Nat model: {}", message.into()))
}

// ─────────────────────────── the Nat magnitude ───────────────────────────

/// The reference model's capacity, in bits, for one `Nat` value. The pinned
/// runtime is TOTAL (an allocation failure aborts the process); the model
/// instead refuses, as [`InterpretErrorCode::OutOfMemory`] — an incapacity,
/// never a verdict — any result that would exceed this bound, so a `pow` or
/// `shift_left` in a sampled program cannot exhaust the host. 2^24 bits is
/// 2 MiB per value: far above any value a test program computes, far below
/// what wedges a machine.
pub const MAX_NAT_BITS: u64 = 1 << 24;

/// An arbitrary-precision natural number: the reference model's value of a
/// `("Nat", "trust_bignum::Nat")` handle.
///
/// Representation: little-endian base-2^64 limbs with NO trailing zero limb
/// (zero is the empty vector), so structural equality is numeric equality.
/// Dependency-free by design (`trust-ir-build` must not pull a bignum crate
/// for a test-and-tooling model), and written from the pin table's documented
/// Lean semantics, not from `trust-bignum`'s code — that independence is what
/// makes a differential between the two informative.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct Nat {
    limbs: Vec<u64>,
}

impl Nat {
    pub fn zero() -> Self {
        Self::default()
    }

    pub fn from_u64(value: u64) -> Self {
        let mut nat = Self { limbs: vec![value] };
        nat.normalize();
        nat
    }

    /// From a `u128`, for tests and differentials.
    pub fn from_u128(value: u128) -> Self {
        let mut nat = Self {
            limbs: vec![value as u64, (value >> 64) as u64],
        };
        nat.normalize();
        nat
    }

    /// The value as a `u128`, when it fits.
    pub fn to_u128(&self) -> Option<u128> {
        match self.limbs.as_slice() {
            [] => Some(0),
            [lo] => Some(u128::from(*lo)),
            [lo, hi] => Some(u128::from(*lo) | (u128::from(*hi) << 64)),
            _ => None,
        }
    }

    /// The little-endian base-2^64 limbs (no trailing zero).
    pub fn limbs(&self) -> &[u64] {
        &self.limbs
    }

    fn normalize(&mut self) {
        while self.limbs.last() == Some(&0) {
            self.limbs.pop();
        }
    }

    pub fn is_zero(&self) -> bool {
        self.limbs.is_empty()
    }

    /// Number of significant bits (`0` for zero).
    pub fn bit_len(&self) -> u64 {
        match self.limbs.last() {
            None => 0,
            Some(top) => (self.limbs.len() as u64 - 1) * 64 + (64 - u64::from(top.leading_zeros())),
        }
    }

    /// `self < 2^64`.
    pub fn fits_u64(&self) -> bool {
        self.limbs.len() <= 1
    }

    /// The value when it fits a `u64`; `None` above `u64::MAX` (the pinned
    /// projection aborts there — this is the total half, `fits_u64`).
    pub fn to_u64(&self) -> Option<u64> {
        match self.limbs.as_slice() {
            [] => Some(0),
            [lo] => Some(*lo),
            _ => None,
        }
    }

    /// Refuse a result wider than [`MAX_NAT_BITS`] before computing it.
    fn check_capacity(bits: u64, op: &str) -> InterpretResult<()> {
        if bits > MAX_NAT_BITS {
            return Err(model_error(
                InterpretErrorCode::OutOfMemory,
                format!(
                    "`{op}` result would need {bits} bits, above the model's {MAX_NAT_BITS}-bit \
                     capacity (an incapacity of the model, not a verdict: the pinned runtime is \
                     total and aborts on allocation failure)"
                ),
            ));
        }
        Ok(())
    }

    pub fn add(&self, other: &Nat) -> InterpretResult<Nat> {
        Self::check_capacity(self.bit_len().max(other.bit_len()) + 1, "add")?;
        let (long, short) = if self.limbs.len() >= other.limbs.len() {
            (self, other)
        } else {
            (other, self)
        };
        let mut limbs = Vec::with_capacity(long.limbs.len() + 1);
        let mut carry = 0u64;
        for (index, &limb) in long.limbs.iter().enumerate() {
            let rhs = short.limbs.get(index).copied().unwrap_or(0);
            let (sum, carry_a) = limb.overflowing_add(rhs);
            let (sum, carry_b) = sum.overflowing_add(carry);
            limbs.push(sum);
            carry = u64::from(carry_a) + u64::from(carry_b);
        }
        if carry != 0 {
            limbs.push(carry);
        }
        let mut nat = Nat { limbs };
        nat.normalize();
        Ok(nat)
    }

    /// TRUNCATING subtraction, Lean's `Nat.sub`: `a - b = 0` whenever `b > a`.
    /// Never wraps, never traps — a wrapping implementation is exactly what a
    /// `sub(2, 5) == 0` check catches.
    pub fn sub(&self, other: &Nat) -> Nat {
        if self <= other {
            return Nat::zero();
        }
        let mut limbs = Vec::with_capacity(self.limbs.len());
        let mut borrow = 0u64;
        for (index, &limb) in self.limbs.iter().enumerate() {
            let rhs = other.limbs.get(index).copied().unwrap_or(0);
            let (diff, borrow_a) = limb.overflowing_sub(rhs);
            let (diff, borrow_b) = diff.overflowing_sub(borrow);
            limbs.push(diff);
            borrow = u64::from(borrow_a) + u64::from(borrow_b);
        }
        debug_assert_eq!(borrow, 0, "self > other, so no final borrow");
        let mut nat = Nat { limbs };
        nat.normalize();
        nat
    }

    pub fn mul(&self, other: &Nat) -> InterpretResult<Nat> {
        if self.is_zero() || other.is_zero() {
            return Ok(Nat::zero());
        }
        Self::check_capacity(self.bit_len() + other.bit_len(), "mul")?;
        let mut limbs = vec![0u64; self.limbs.len() + other.limbs.len()];
        for (i, &a) in self.limbs.iter().enumerate() {
            let mut carry = 0u128;
            for (j, &b) in other.limbs.iter().enumerate() {
                let cell = u128::from(limbs[i + j]) + u128::from(a) * u128::from(b) + carry;
                limbs[i + j] = cell as u64;
                carry = cell >> 64;
            }
            let mut k = i + other.limbs.len();
            while carry != 0 {
                let cell = u128::from(limbs[k]) + carry;
                limbs[k] = cell as u64;
                carry = cell >> 64;
                k += 1;
            }
        }
        let mut nat = Nat { limbs };
        nat.normalize();
        Ok(nat)
    }

    /// `(self / other, self % other)` with Lean's convention for zero:
    /// `n / 0 = 0` and `n % 0 = n`. Binary long division: a reference model
    /// optimised for being obviously right, not for speed.
    pub fn divmod(&self, other: &Nat) -> (Nat, Nat) {
        if other.is_zero() {
            return (Nat::zero(), self.clone());
        }
        if self < other {
            return (Nat::zero(), self.clone());
        }
        let mut quotient = vec![0u64; self.limbs.len()];
        let mut remainder = Nat::zero();
        for bit in (0..self.bit_len()).rev() {
            remainder = remainder.shl_bits(1);
            if self.bit(bit) {
                if remainder.limbs.is_empty() {
                    remainder.limbs.push(0);
                }
                remainder.limbs[0] |= 1;
            }
            if remainder >= *other {
                remainder = remainder.sub(other);
                quotient[(bit / 64) as usize] |= 1u64 << (bit % 64);
            }
        }
        let mut quotient = Nat { limbs: quotient };
        quotient.normalize();
        (quotient, remainder)
    }

    /// Lean `Nat.div`: `n / 0 = 0`.
    pub fn div(&self, other: &Nat) -> Nat {
        self.divmod(other).0
    }

    /// Lean `Nat.mod`: `n % 0 = n`.
    pub fn rem(&self, other: &Nat) -> Nat {
        self.divmod(other).1
    }

    fn bit(&self, index: u64) -> bool {
        self.limbs
            .get((index / 64) as usize)
            .is_some_and(|limb| limb & (1u64 << (index % 64)) != 0)
    }

    fn bitwise(&self, other: &Nat, op: impl Fn(u64, u64) -> u64) -> Nat {
        let len = self.limbs.len().max(other.limbs.len());
        let limbs = (0..len)
            .map(|index| {
                op(
                    self.limbs.get(index).copied().unwrap_or(0),
                    other.limbs.get(index).copied().unwrap_or(0),
                )
            })
            .collect();
        let mut nat = Nat { limbs };
        nat.normalize();
        nat
    }

    pub fn land(&self, other: &Nat) -> Nat {
        self.bitwise(other, |a, b| a & b)
    }

    pub fn lor(&self, other: &Nat) -> Nat {
        self.bitwise(other, |a, b| a | b)
    }

    pub fn xor(&self, other: &Nat) -> Nat {
        self.bitwise(other, |a, b| a ^ b)
    }

    /// `self << bits` (unchecked capacity; callers check).
    fn shl_bits(&self, bits: u64) -> Nat {
        if self.is_zero() {
            return Nat::zero();
        }
        let limb_shift = (bits / 64) as usize;
        let bit_shift = bits % 64;
        let mut limbs = vec![0u64; limb_shift];
        if bit_shift == 0 {
            limbs.extend_from_slice(&self.limbs);
        } else {
            let mut carry = 0u64;
            for &limb in &self.limbs {
                limbs.push((limb << bit_shift) | carry);
                carry = limb >> (64 - bit_shift);
            }
            if carry != 0 {
                limbs.push(carry);
            }
        }
        let mut nat = Nat { limbs };
        nat.normalize();
        nat
    }

    /// Lean `Nat.shiftLeft`: `self * 2^other`. Total in the runtime; here a
    /// result past [`MAX_NAT_BITS`] is the model's `OutOfMemory` incapacity.
    pub fn shift_left(&self, other: &Nat) -> InterpretResult<Nat> {
        if self.is_zero() {
            return Ok(Nat::zero());
        }
        let bits = other.to_u64().unwrap_or(u64::MAX);
        Self::check_capacity(self.bit_len().saturating_add(bits), "shift_left")?;
        Ok(self.shl_bits(bits))
    }

    /// Lean `Nat.shiftRight`: `self / 2^other`, zero once every bit is gone.
    pub fn shift_right(&self, other: &Nat) -> Nat {
        let Some(bits) = other.to_u64() else {
            return Nat::zero();
        };
        if bits >= self.bit_len() {
            return Nat::zero();
        }
        let limb_shift = (bits / 64) as usize;
        let bit_shift = bits % 64;
        let source = &self.limbs[limb_shift..];
        let limbs = if bit_shift == 0 {
            source.to_vec()
        } else {
            source
                .iter()
                .enumerate()
                .map(|(index, &limb)| {
                    let high = source.get(index + 1).copied().unwrap_or(0);
                    (limb >> bit_shift) | (high << (64 - bit_shift))
                })
                .collect()
        };
        let mut nat = Nat { limbs };
        nat.normalize();
        nat
    }

    /// Lean `Nat.pow`: `b^0 = 1` (so `0^0 = 1`), `0^e = 0` for `e > 0`.
    /// Square-and-multiply; a result past [`MAX_NAT_BITS`] is refused before
    /// any limb is allocated.
    pub fn pow(&self, exponent: &Nat) -> InterpretResult<Nat> {
        if exponent.is_zero() {
            return Ok(Nat::from_u64(1));
        }
        if self.is_zero() {
            return Ok(Nat::zero());
        }
        if self.limbs == [1] {
            return Ok(Nat::from_u64(1));
        }
        // Base >= 2: the result has at least `exponent` bits, so an exponent
        // beyond u64 (or one that overflows the estimate) is beyond capacity.
        let Some(e) = exponent.to_u64() else {
            return Err(model_error(
                InterpretErrorCode::OutOfMemory,
                "`pow` exponent above u64::MAX exceeds the model's capacity (an incapacity of \
                 the model, not a verdict)",
            ));
        };
        // Upper bound on the result width: bit_len(base) * e.
        let estimate = self.bit_len().saturating_mul(e);
        Self::check_capacity(estimate, "pow")?;
        let mut result = Nat::from_u64(1);
        let mut base = self.clone();
        let mut e = e;
        while e > 0 {
            if e & 1 == 1 {
                result = result.mul(&base)?;
            }
            e >>= 1;
            if e > 0 {
                base = base.mul(&base)?;
            }
        }
        Ok(result)
    }
}

impl PartialOrd for Nat {
    fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Nat {
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        self.limbs
            .len()
            .cmp(&other.limbs.len())
            .then_with(|| self.limbs.iter().rev().cmp(other.limbs.iter().rev()))
    }
}

/// Every pinned entry point is modelled — checked at the type level of the
/// tables, and re-checked by execution in `interpret_host_models.rs`.
#[cfg(test)]
mod tests {
    use super::*;
    use crate::validate::{
        TRUSTED_HANDLE_RUNTIMES, TRUSTED_RC_RUNTIMES, pinned_release_entry_points,
    };
    use trust_ir::CallingConv;

    /// A pin row added without a model arm fails here (roadmap WS2.13).
    #[test]
    fn every_pinned_entry_point_has_a_host_model() {
        let mut unmodelled = Vec::new();
        for pin in TRUSTED_HANDLE_RUNTIMES {
            for entry in pin.entry_points {
                if !PinnedHandleHost::models_handle_entry(pin, entry) {
                    unmodelled.push(format!("{} ({})", entry.symbol, pin.runtime));
                }
            }
        }
        for pin in TRUSTED_RC_RUNTIMES {
            for entry in pin.entry_points {
                if !PinnedHandleHost::models_rc_entry(pin, entry) {
                    unmodelled.push(format!("{} ({})", entry.symbol, pin.runtime));
                }
            }
        }
        assert!(
            unmodelled.is_empty(),
            "pinned entry points without a reference host model: {unmodelled:?}"
        );
        // And the model claims no role the table does not pin (a stale arm
        // would be a model of nothing).
        let nat = TRUSTED_HANDLE_RUNTIMES
            .iter()
            .find(|pin| pin.runtime == NAT_RUNTIME)
            .expect("the Nat row is pinned");
        for role in NAT_ROLES {
            assert!(
                nat.entry_points.iter().any(|entry| entry.role == *role),
                "model role `{role}` is not pinned"
            );
        }
        let rc = TRUSTED_RC_RUNTIMES
            .iter()
            .find(|pin| pin.runtime == CLEAN_RC_RUNTIME)
            .expect("the Clean RC row is pinned");
        for role in RC_ROLES {
            assert!(
                rc.entry_points.iter().any(|entry| entry.role == *role),
                "model RC role `{role}` is not pinned"
            );
        }
        // The model's calling convention is the pinned one.
        assert_eq!(nat.calling_conv, CallingConv::C);
        assert_eq!(rc.calling_conv, CallingConv::C);
    }

    /// WS3.22 (F-060): every row of the one-place release table is an entry
    /// point this model serves, and every `drop`/`release` role the model
    /// serves is named by that table — the release keying cannot drift from
    /// the model in either direction.
    #[test]
    fn every_pinned_release_entry_point_is_modelled_as_a_release() {
        let table = pinned_release_entry_points();
        assert!(!table.is_empty(), "v1 pins two release entry points");
        for release in table {
            let modelled = match &release.subject {
                PinnedReleaseSubject::Handle(handle) => HandleRegistry::pinned()
                    .entry_for_symbol(release.symbol)
                    .is_some_and(|(pin, entry)| {
                        pin.handle_identity() == *handle
                            && PinnedHandleHost::models_handle_entry(pin, entry)
                    }),
                PinnedReleaseSubject::RcCell(origin) => rc_entry_for_symbol(release.symbol)
                    .is_some_and(|(pin, entry)| {
                        pin.origin == *origin && PinnedHandleHost::models_rc_entry(pin, entry)
                    }),
            };
            assert!(
                modelled,
                "release entry point {} ({}) has no reference host model",
                release.symbol, release.runtime
            );
        }
        // The other direction: the release of each row the model serves is a
        // row of the table (the end-to-end keying — a double `drop` faults, a
        // no-op mutant does not — is `tests/release_entry_points.rs`).
        let nat = TRUSTED_HANDLE_RUNTIMES
            .iter()
            .find(|pin| pin.runtime == NAT_RUNTIME)
            .expect("the Nat row is pinned");
        let drop = nat.release_entry().expect("the Nat row pins a release");
        assert_eq!(drop.role, "drop");
        assert!(
            pinned_release_entry_for_symbol(drop.symbol).is_some(),
            "the Nat row's release `{}` is not in the one-place table",
            drop.symbol
        );
        let rc = TRUSTED_RC_RUNTIMES
            .iter()
            .find(|pin| pin.runtime == CLEAN_RC_RUNTIME)
            .expect("the Clean RC row is pinned");
        let release = rc.release_entry().expect("the Clean row pins a release");
        assert!(
            pinned_release_entry_for_symbol(release.symbol).is_some(),
            "the Clean row's release `{}` is not in the one-place table",
            release.symbol
        );
    }

    fn n(value: u128) -> Nat {
        Nat::from_u128(value)
    }

    #[test]
    fn representation_is_normalized_and_ordered() {
        assert_eq!(Nat::from_u64(0), Nat::zero());
        assert!(Nat::from_u64(0).limbs().is_empty());
        assert_eq!(n(1 << 64).limbs(), &[0, 1]);
        assert_eq!(n(1 << 64).bit_len(), 65);
        assert_eq!(n(u64::MAX as u128).bit_len(), 64);
        assert!(n(1 << 64) > n(u64::MAX as u128));
        assert!(n(5) < n(7));
        assert_eq!(n(7).cmp(&n(7)), core::cmp::Ordering::Equal);
    }

    #[test]
    fn add_carries_across_limbs() {
        let sum = n(u64::MAX as u128).add(&n(1)).unwrap();
        assert_eq!(sum, n(1 << 64));
        assert_eq!(n(u128::MAX).add(&n(1)).unwrap().bit_len(), 129);
        assert_eq!(n(0).add(&n(0)).unwrap(), Nat::zero());
    }

    /// The mutation control the roadmap names: a wrapping implementation
    /// returns `2^64 - 3`; the pinned semantics return zero.
    #[test]
    fn sub_truncates_at_zero_like_lean_nat_sub() {
        assert_eq!(n(2).sub(&n(5)), Nat::zero());
        assert_eq!(n(5).sub(&n(2)), n(3));
        assert_eq!(n(5).sub(&n(5)), Nat::zero());
        assert_eq!(n(1 << 64).sub(&n(1)), n(u64::MAX as u128));
        assert_eq!(
            n(u128::MAX).sub(&n(u64::MAX as u128)),
            n(u128::MAX - u64::MAX as u128)
        );
    }

    #[test]
    fn mul_is_schoolbook_exact() {
        assert_eq!(n(6).mul(&n(7)).unwrap(), n(42));
        assert_eq!(
            n(u64::MAX as u128).mul(&n(u64::MAX as u128)).unwrap(),
            n((u64::MAX as u128) * (u64::MAX as u128))
        );
        assert_eq!(n(0).mul(&n(u64::MAX as u128)).unwrap(), Nat::zero());
        // 2^128 * 2^128 = 2^256: three limb boundaries crossed.
        let two_128 = n(1u128 << 127).mul(&n(2)).unwrap();
        assert_eq!(two_128.bit_len(), 129);
        assert_eq!(two_128.mul(&two_128).unwrap().bit_len(), 257);
    }

    #[test]
    fn div_and_mod_follow_lean_zero_conventions() {
        assert_eq!(n(7).div(&n(0)), Nat::zero());
        assert_eq!(n(7).rem(&n(0)), n(7));
        assert_eq!(n(7).div(&n(2)), n(3));
        assert_eq!(n(7).rem(&n(2)), n(1));
        assert_eq!(n(3).div(&n(7)), Nat::zero());
        assert_eq!(n(3).rem(&n(7)), n(3));
        let big = n(u128::MAX);
        assert_eq!(
            big.div(&n(u64::MAX as u128)),
            n(u128::MAX / u64::MAX as u128)
        );
        assert_eq!(
            big.rem(&n(u64::MAX as u128)),
            n(u128::MAX % u64::MAX as u128)
        );
        assert_eq!(big.div(&n(1)), big);
        assert_eq!(big.div(&big), n(1));
        assert_eq!(big.rem(&big), Nat::zero());
    }

    #[test]
    fn bitwise_and_shifts() {
        assert_eq!(n(0b1100).land(&n(0b1010)), n(0b1000));
        assert_eq!(n(0b1100).lor(&n(0b1010)), n(0b1110));
        assert_eq!(n(0b1100).xor(&n(0b1010)), n(0b0110));
        assert_eq!(n(u128::MAX).xor(&n(u128::MAX)), Nat::zero());
        assert_eq!(n(1).shift_left(&n(64)).unwrap(), n(1 << 64));
        assert_eq!(n(1).shift_left(&n(127)).unwrap(), n(1 << 127));
        assert_eq!(n(3).shift_left(&n(63)).unwrap(), n(3 << 63));
        assert_eq!(n(0).shift_left(&n(u64::MAX as u128)).unwrap(), Nat::zero());
        assert_eq!(n(1 << 64).shift_right(&n(64)), n(1));
        assert_eq!(n(1 << 64).shift_right(&n(65)), Nat::zero());
        assert_eq!(n(3 << 63).shift_right(&n(63)), n(3));
        assert_eq!(n(7).shift_right(&n(u64::MAX as u128)), Nat::zero());
        assert_eq!(n(7).shift_right(&n(1 << 64)), Nat::zero());
        assert_eq!(n(7).shift_right(&n(0)), n(7));
        let refused = n(1).shift_left(&n(1 << 64)).unwrap_err();
        assert_eq!(refused.code, InterpretErrorCode::OutOfMemory);
        let refused = n(1).shift_left(&n(MAX_NAT_BITS as u128)).unwrap_err();
        assert_eq!(refused.code, InterpretErrorCode::OutOfMemory);
        assert_eq!(
            n(1).shift_left(&n(MAX_NAT_BITS as u128 - 1))
                .unwrap()
                .bit_len(),
            MAX_NAT_BITS
        );
    }

    #[test]
    fn pow_follows_lean_nat_pow() {
        assert_eq!(n(0).pow(&n(0)).unwrap(), n(1));
        assert_eq!(n(0).pow(&n(5)).unwrap(), Nat::zero());
        assert_eq!(n(1).pow(&n(u128::MAX)).unwrap(), n(1));
        assert_eq!(n(2).pow(&n(10)).unwrap(), n(1024));
        assert_eq!(n(3).pow(&n(40)).unwrap(), n(3u128.pow(40)));
        assert_eq!(n(2).pow(&n(127)).unwrap(), n(1 << 127));
        let refused = n(2).pow(&n(u64::MAX as u128)).unwrap_err();
        assert_eq!(refused.code, InterpretErrorCode::OutOfMemory);
        let refused = n(2).pow(&n(1 << 64)).unwrap_err();
        assert_eq!(refused.code, InterpretErrorCode::OutOfMemory);
    }

    #[test]
    fn u64_projections() {
        assert!(n(u64::MAX as u128).fits_u64());
        assert!(!n(1 << 64).fits_u64());
        assert_eq!(n(u64::MAX as u128).to_u64(), Some(u64::MAX));
        assert_eq!(n(0).to_u64(), Some(0));
        assert_eq!(n(1 << 64).to_u64(), None);
        assert_eq!(n(u128::MAX).to_u128(), Some(u128::MAX));
        assert_eq!(n(1).shift_left(&n(128)).unwrap().to_u128(), None);
    }
}

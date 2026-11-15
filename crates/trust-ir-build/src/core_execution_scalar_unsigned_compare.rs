// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0

//! Pending unsigned comparisons of canonical full64 integer bit patterns.
//!
//! These adapters derive the exact Boolean observer and actual evaluator
//! equality from input bounds alone. They install/check nothing, create no
//! locals/cache, and execute no fetched instruction. Closed independent kernel
//! replay with the opt-in comparison vocabulary is mandatory. Typed operands,
//! result fit, fetched state, source meaning and native authority stay separate.

use super::*;
use trust_ir::ICmpOp;

#[cfg(test)]
#[path = "core_execution_scalar_unsigned_compare_tests.rs"]
mod tests;

#[derive(Clone, Copy)]
enum UnsignedComparisonCarrier {
    Unsigned,
    Signed,
}

impl Assembler<'_> {
    /// Derive actual U64 Ult/Ule/Ugt/Uge from canonical input bounds only.
    ///
    /// Both premises must state exactly `Nat.lt operand (ir_nat_pow2 64)`.
    /// The pair contains the derived `IRScalar.bool_` and its pending actual
    /// `ir_icmp_eval` equality; no truth value or answer proof is an input.
    /// One operation is charged before every opcode/shape check. Every other
    /// comparison opcode is refused, with no new locals or cached vocabulary.
    pub fn byte_unsigned_compare_u64_canonical(
        &mut self,
        op: ICmpOp,
        a: Expr,
        b: Expr,
        a_bound: PendingProof,
        b_bound: PendingProof,
    ) -> Result<(Expr, PendingEquality)> {
        self.byte_unsigned_compare_canonical(
            op,
            [a, b],
            [a_bound, b_bound],
            UnsignedComparisonCarrier::Unsigned,
        )
    }

    /// Derive actual I64 unsigned comparison over canonical full64 bit patterns.
    ///
    /// The nominal signed operand carrier is preserved. Ult/Ule/Ugt/Uge still
    /// compare unsigned encodings, including encodings of negative integers;
    /// this is not signed comparison or a TLC32 source-semantic rule. Exact
    /// input bounds, charging, supported opcodes and pending status match U64.
    pub fn byte_unsigned_compare_i64_canonical(
        &mut self,
        op: ICmpOp,
        a: Expr,
        b: Expr,
        a_bound: PendingProof,
        b_bound: PendingProof,
    ) -> Result<(Expr, PendingEquality)> {
        self.byte_unsigned_compare_canonical(
            op,
            [a, b],
            [a_bound, b_bound],
            UnsignedComparisonCarrier::Signed,
        )
    }

    fn byte_unsigned_compare_canonical(
        &mut self,
        op: ICmpOp,
        words: [Expr; 2],
        bounds: [PendingProof; 2],
        carrier: UnsignedComparisonCarrier,
    ) -> Result<(Expr, PendingEquality)> {
        self.charge()?;
        let (opcode, observer, reverse, unsigned_law, signed_law) = match op {
            ICmpOp::Ult => (
                "IRICmpOp.ult",
                "ir_nat_ltb",
                false,
                "ir_byte_icmp_uint_ult_canonical_v1",
                "ir_byte_icmp_int_ult_canonical_v1",
            ),
            ICmpOp::Ule => (
                "IRICmpOp.ule",
                "ir_nat_leb",
                false,
                "ir_byte_icmp_uint_ule_canonical_v1",
                "ir_byte_icmp_int_ule_canonical_v1",
            ),
            ICmpOp::Ugt => (
                "IRICmpOp.ugt",
                "ir_nat_ltb",
                true,
                "ir_byte_icmp_uint_ugt_canonical_v1",
                "ir_byte_icmp_int_ugt_canonical_v1",
            ),
            ICmpOp::Uge => (
                "IRICmpOp.uge",
                "ir_nat_leb",
                true,
                "ir_byte_icmp_uint_uge_canonical_v1",
                "ir_byte_icmp_int_uge_canonical_v1",
            ),
            ICmpOp::Eq | ICmpOp::Ne | ICmpOp::Slt | ICmpOp::Sle | ICmpOp::Sgt | ICmpOp::Sge => {
                return Err("unsigned comparison requires Ult, Ule, Ugt or Uge".into());
            }
        };
        let [a, b] = words;
        let [a_bound, b_bound] = bounds;
        let limit = app("ir_nat_pow2", [nat(64)]);
        require_same(
            a_bound.proposition(),
            &app("Nat.lt", [a.clone(), limit.clone()]),
            "unsigned compare lhs canonical word bound",
        )?;
        require_same(
            b_bound.proposition(),
            &app("Nat.lt", [b.clone(), limit]),
            "unsigned compare rhs canonical word bound",
        )?;
        let operands = if reverse {
            [b.clone(), a.clone()]
        } else {
            [a.clone(), b.clone()]
        };
        let value = app("IRScalar.bool_", [app(observer, operands)]);
        let (ty, law) = match carrier {
            UnsignedComparisonCarrier::Unsigned => ("IRTy.uint_", unsigned_law),
            UnsignedComparisonCarrier::Signed => ("IRTy.int_", signed_law),
        };
        let equality = PendingEquality::candidate(
            constant("IRStepResult"),
            app(
                "ir_icmp_eval",
                [
                    constant(opcode),
                    app(ty, [nat(64)]),
                    app("IRScalar.int_", [a.clone()]),
                    app("IRScalar.int_", [b.clone()]),
                ],
            ),
            app("IRStepResult.value", [value.clone()]),
            app(
                law,
                [
                    nat(64),
                    a,
                    b,
                    a_bound.term().clone(),
                    b_bound.term().clone(),
                ],
            ),
        );
        Ok((value, equality))
    }
}

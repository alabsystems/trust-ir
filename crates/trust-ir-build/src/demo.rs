// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! # Demonstration / fixture SIMD emitters — NOT the frontend emission surface
//!
//! This module quarantines the SIMD and portable-vector-dialect convenience
//! emitters that used to sit directly on [`FunctionBuilder`]. They exist to
//! keep tests, conformance fixtures, and demos terse; they are **not** part of
//! the general-purpose frontend emission API
//! (`docs/roadmap/integration-frontend-emission.md`, "builder de-pollution").
//!
//! Everything here is a thin veneer over the general builder surface
//! (`binop` / `icmp` / `select` / `dialect_op`): the emitted IR is identical
//! to what the core methods produce, so moving a call site between the two
//! spellings is a no-op at the IR level.
//!
//! To use the helpers, bring the extension trait into scope:
//!
//! ```rust
//! use trust_ir::Ty;
//! use trust_ir_build::{demo::VectorDemoExt, ModuleBuilder};
//!
//! let mut module = ModuleBuilder::new("vector-demo");
//! let signature =
//!     module.add_func_type(vec![Ty::v4_i32(), Ty::v4_i32()], vec![Ty::v4_i32()]);
//! let mut function = module.function("add", signature);
//! let entry = function.create_block();
//! let lhs = function.add_block_param(entry, Ty::v4_i32());
//! let rhs = function.add_block_param(entry, Ty::v4_i32());
//! function.switch_to_block(entry);
//! let sum = function.v4_i32_add(lhs, rhs);
//! function.ret(vec![sum]);
//! function.build();
//! let _module = module.build()?;
//! # Ok::<(), trust_ir_build::BuildError>(())
//! ```

use trust_ir::constant::Constant;
use trust_ir::dialect::vector;
use trust_ir::inst::{BinOp, ICmpOp, Inst};
use trust_ir::ty::Ty;
use trust_ir::value::ValueId;

use crate::builder::FunctionBuilder;

/// Extension trait carrying the SIMD / vector-dialect demonstration emitters.
///
/// Implemented for [`FunctionBuilder`]; import the trait to use the helpers.
/// The fixed-width `v4_i32_*` / `v2_i64_*` shorthands target the canonical
/// CHC x86 vector shapes; the `vector_*` methods emit the portable
/// `vector.*` dialect ops (validated via `vector::decode` before emission).
pub trait VectorDemoExt {
    // --- Fixed-width lane-wise arithmetic ---

    /// Emit lane-wise fixed-width add over the canonical CHC x86 vector type,
    /// `<4 x i32>`.
    fn v4_i32_add(&mut self, lhs: ValueId, rhs: ValueId) -> ValueId;

    /// Emit lane-wise fixed-width add over the canonical CHC x86 vector type,
    /// `<2 x i64>`.
    fn v2_i64_add(&mut self, lhs: ValueId, rhs: ValueId) -> ValueId;

    /// Emit lane-wise fixed-width sub over the canonical CHC x86 vector type,
    /// `<4 x i32>`.
    fn v4_i32_sub(&mut self, lhs: ValueId, rhs: ValueId) -> ValueId;

    /// Emit lane-wise fixed-width sub over the canonical CHC x86 vector type,
    /// `<2 x i64>`.
    fn v2_i64_sub(&mut self, lhs: ValueId, rhs: ValueId) -> ValueId;

    /// Emit lane-wise wrapping multiply over `<4 x i32>`.
    ///
    /// Native x86 lowering is guarded by SSE4.1 `pmulld` or an explicit
    /// scalar fallback; the source TrustIr operation remains `BinOp::Mul`.
    fn v4_i32_mul(&mut self, lhs: ValueId, rhs: ValueId) -> ValueId;

    // --- Fixed-width lane-wise comparisons ---

    /// Emit lane-wise equality over `<2 x i64>`, producing `<2 x bool>`.
    fn v2_i64_icmp_eq(&mut self, lhs: ValueId, rhs: ValueId) -> ValueId;

    /// Emit lane-wise inequality over `<2 x i64>`, producing `<2 x bool>`.
    fn v2_i64_icmp_ne(&mut self, lhs: ValueId, rhs: ValueId) -> ValueId;

    /// Emit lane-wise signed less-than over `<2 x i64>`, producing
    /// `<2 x bool>`.
    fn v2_i64_icmp_slt(&mut self, lhs: ValueId, rhs: ValueId) -> ValueId;

    /// Emit lane-wise signed less-than-or-equal over `<2 x i64>`, producing
    /// `<2 x bool>`.
    fn v2_i64_icmp_sle(&mut self, lhs: ValueId, rhs: ValueId) -> ValueId;

    /// Emit lane-wise signed greater-than over `<2 x i64>`, producing
    /// `<2 x bool>`.
    fn v2_i64_icmp_sgt(&mut self, lhs: ValueId, rhs: ValueId) -> ValueId;

    /// Emit lane-wise signed greater-than-or-equal over `<2 x i64>`, producing
    /// `<2 x bool>`.
    fn v2_i64_icmp_sge(&mut self, lhs: ValueId, rhs: ValueId) -> ValueId;

    /// Emit lane-wise signed less-than over `<4 x i32>`, producing
    /// `<4 x bool>`.
    fn v4_i32_icmp_slt(&mut self, lhs: ValueId, rhs: ValueId) -> ValueId;

    /// Emit lane-wise signed less-than-or-equal over `<4 x i32>`, producing
    /// `<4 x bool>`.
    fn v4_i32_icmp_sle(&mut self, lhs: ValueId, rhs: ValueId) -> ValueId;

    /// Emit lane-wise signed greater-than over `<4 x i32>`, producing
    /// `<4 x bool>`.
    fn v4_i32_icmp_sgt(&mut self, lhs: ValueId, rhs: ValueId) -> ValueId;

    /// Emit lane-wise signed greater-than-or-equal over `<4 x i32>`, producing
    /// `<4 x bool>`.
    fn v4_i32_icmp_sge(&mut self, lhs: ValueId, rhs: ValueId) -> ValueId;

    // --- Fixed-width vector constants ---

    /// Emit a `<4 x i32>` constant.
    fn v4_i32_const(&mut self, values: [i32; 4]) -> ValueId;

    /// Emit a `<2 x i64>` constant.
    fn v2_i64_const(&mut self, values: [i64; 2]) -> ValueId;

    /// Emit the physical x86-style zero mask carrier, `<2 x i64>`.
    ///
    /// This is data, not a legal `select` condition. Compare it to another
    /// `<2 x i64>` value to obtain the logical `<2 x bool>` mask.
    fn v2_i64_zero_mask_const(&mut self) -> ValueId;

    /// Emit the physical x86-style all-ones mask carrier, `<2 x i64>`.
    ///
    /// This is data, not a legal `select` condition. Compare it to zero to
    /// obtain the logical `<2 x bool>` mask.
    fn v2_i64_all_ones_mask_const(&mut self) -> ValueId;

    /// Emit the physical x86-style zero mask carrier, `<4 x i32>`.
    ///
    /// This is data, not a legal `select` condition. Compare it to another
    /// `<4 x i32>` value to obtain the logical `<4 x bool>` mask.
    fn v4_i32_zero_mask_const(&mut self) -> ValueId;

    /// Emit the physical x86-style all-ones mask carrier, `<4 x i32>`.
    ///
    /// This is data, not a legal `select` condition. Compare it to zero to
    /// obtain the logical `<4 x bool>` mask.
    fn v4_i32_all_ones_mask_const(&mut self) -> ValueId;

    // --- Fixed-width masked select ---

    /// Emit lane-wise select over `<4 x i32>` using a logical `<4 x bool>`
    /// condition.
    fn v4_i32_mask_select(
        &mut self,
        cond: ValueId,
        then_val: ValueId,
        else_val: ValueId,
    ) -> ValueId;

    /// Emit lane-wise select over `<2 x i64>` using a logical `<2 x bool>`
    /// condition.
    fn v2_i64_mask_select(
        &mut self,
        cond: ValueId,
        then_val: ValueId,
        else_val: ValueId,
    ) -> ValueId;

    // --- Portable vector dialect ops ---

    /// Emit the canonical repeated-lane `vector.pack_lanes` spelling for a
    /// `<4 x i32>` splat.
    fn v4_i32_splat_lane(&mut self, lane: ValueId) -> Result<ValueId, String>;

    /// Emit the canonical repeated-lane `vector.pack_lanes` spelling for a
    /// `<2 x i64>` splat.
    fn v2_i64_splat_lane(&mut self, lane: ValueId) -> Result<ValueId, String>;

    /// Emit `vector.pack_lanes`, producing one fixed-width vector from scalar
    /// lane values.
    fn vector_pack_lanes(
        &mut self,
        vector_ty: Ty,
        lanes: impl IntoIterator<Item = ValueId>,
    ) -> Result<ValueId, String>;

    /// Emit `vector.extract_lane` for a constant lane index.
    fn vector_extract_lane(
        &mut self,
        vector_ty: Ty,
        vector: ValueId,
        lane: u32,
    ) -> Result<ValueId, String>;

    /// Emit `vector.insert_lane` for a constant lane index.
    fn vector_insert_lane(
        &mut self,
        vector_ty: Ty,
        vector: ValueId,
        lane: u32,
        value: ValueId,
    ) -> Result<ValueId, String>;

    /// Emit `vector.mask_to_bits`, compacting a logical vector mask with lane
    /// 0 in the least-significant output bit.
    fn vector_mask_to_bits(
        &mut self,
        mask_ty: Ty,
        mask: ValueId,
        result_ty: Ty,
    ) -> Result<ValueId, String>;

    /// Emit `vector.reduce`, folding an integer lane vector to one scalar of the
    /// element type with an associative `kind` fold.
    fn vector_reduce(
        &mut self,
        vector_ty: Ty,
        vector_val: ValueId,
        kind: vector::ReduceKind,
    ) -> Result<ValueId, String>;

    /// Emit `vector.shuffle`, permuting source lanes by the static `indices`
    /// mask (`indices[j]` is the source lane copied into result lane `j`).
    fn vector_shuffle(
        &mut self,
        vector_ty: Ty,
        vector_val: ValueId,
        indices: impl Into<Vec<u8>>,
    ) -> Result<ValueId, String>;

    /// Emit `vector.fma`, computing per-lane fused multiply-add `a * b + c`
    /// over a float lane vector.
    fn vector_fma(
        &mut self,
        vector_ty: Ty,
        a: ValueId,
        b: ValueId,
        c: ValueId,
    ) -> Result<ValueId, String>;

    // --- Fixed-width wrappers over the dialect ops ---

    fn v4_i32_pack_lanes(&mut self, lanes: [ValueId; 4]) -> Result<ValueId, String>;

    fn v2_i64_pack_lanes(&mut self, lanes: [ValueId; 2]) -> Result<ValueId, String>;

    fn v4_i32_extract_lane(&mut self, vector: ValueId, lane: u32) -> Result<ValueId, String>;

    fn v2_i64_extract_lane(&mut self, vector: ValueId, lane: u32) -> Result<ValueId, String>;

    fn v4_i32_insert_lane(
        &mut self,
        vector: ValueId,
        lane: u32,
        value: ValueId,
    ) -> Result<ValueId, String>;

    fn v2_i64_insert_lane(
        &mut self,
        vector: ValueId,
        lane: u32,
        value: ValueId,
    ) -> Result<ValueId, String>;

    fn v4_bool_mask_to_i32_bits(&mut self, mask: ValueId) -> Result<ValueId, String>;

    fn v8_bool_mask_to_i32_bits(&mut self, mask: ValueId) -> Result<ValueId, String>;

    fn v16_bool_mask_to_i32_bits(&mut self, mask: ValueId) -> Result<ValueId, String>;

    fn v2_bool_mask_to_i32_bits(&mut self, mask: ValueId) -> Result<ValueId, String>;

    fn v2_bool_mask_to_i64_bits(&mut self, mask: ValueId) -> Result<ValueId, String>;
}

impl VectorDemoExt for FunctionBuilder<'_> {
    fn v4_i32_add(&mut self, lhs: ValueId, rhs: ValueId) -> ValueId {
        self.add(Ty::v4_i32(), lhs, rhs)
    }

    fn v2_i64_add(&mut self, lhs: ValueId, rhs: ValueId) -> ValueId {
        self.add(Ty::v2_i64(), lhs, rhs)
    }

    fn v4_i32_sub(&mut self, lhs: ValueId, rhs: ValueId) -> ValueId {
        self.sub(Ty::v4_i32(), lhs, rhs)
    }

    fn v2_i64_sub(&mut self, lhs: ValueId, rhs: ValueId) -> ValueId {
        self.sub(Ty::v2_i64(), lhs, rhs)
    }

    fn v4_i32_mul(&mut self, lhs: ValueId, rhs: ValueId) -> ValueId {
        self.binop(BinOp::Mul, Ty::v4_i32(), lhs, rhs)
    }

    fn v2_i64_icmp_eq(&mut self, lhs: ValueId, rhs: ValueId) -> ValueId {
        self.icmp(ICmpOp::Eq, Ty::v2_i64(), lhs, rhs)
    }

    fn v2_i64_icmp_ne(&mut self, lhs: ValueId, rhs: ValueId) -> ValueId {
        self.icmp(ICmpOp::Ne, Ty::v2_i64(), lhs, rhs)
    }

    fn v2_i64_icmp_slt(&mut self, lhs: ValueId, rhs: ValueId) -> ValueId {
        self.icmp(ICmpOp::Slt, Ty::v2_i64(), lhs, rhs)
    }

    fn v2_i64_icmp_sle(&mut self, lhs: ValueId, rhs: ValueId) -> ValueId {
        self.icmp(ICmpOp::Sle, Ty::v2_i64(), lhs, rhs)
    }

    fn v2_i64_icmp_sgt(&mut self, lhs: ValueId, rhs: ValueId) -> ValueId {
        self.icmp(ICmpOp::Sgt, Ty::v2_i64(), lhs, rhs)
    }

    fn v2_i64_icmp_sge(&mut self, lhs: ValueId, rhs: ValueId) -> ValueId {
        self.icmp(ICmpOp::Sge, Ty::v2_i64(), lhs, rhs)
    }

    fn v4_i32_icmp_slt(&mut self, lhs: ValueId, rhs: ValueId) -> ValueId {
        self.icmp(ICmpOp::Slt, Ty::v4_i32(), lhs, rhs)
    }

    fn v4_i32_icmp_sle(&mut self, lhs: ValueId, rhs: ValueId) -> ValueId {
        self.icmp(ICmpOp::Sle, Ty::v4_i32(), lhs, rhs)
    }

    fn v4_i32_icmp_sgt(&mut self, lhs: ValueId, rhs: ValueId) -> ValueId {
        self.icmp(ICmpOp::Sgt, Ty::v4_i32(), lhs, rhs)
    }

    fn v4_i32_icmp_sge(&mut self, lhs: ValueId, rhs: ValueId) -> ValueId {
        self.icmp(ICmpOp::Sge, Ty::v4_i32(), lhs, rhs)
    }

    fn v4_i32_const(&mut self, values: [i32; 4]) -> ValueId {
        self.emit(Inst::Const {
            ty: Ty::v4_i32(),
            value: Constant::v4_i32(values),
        })
    }

    fn v2_i64_const(&mut self, values: [i64; 2]) -> ValueId {
        self.emit(Inst::Const {
            ty: Ty::v2_i64(),
            value: Constant::v2_i64(values),
        })
    }

    fn v2_i64_zero_mask_const(&mut self) -> ValueId {
        self.emit(Inst::Const {
            ty: Ty::v2_i64(),
            value: Constant::v2_i64_zero_mask(),
        })
    }

    fn v2_i64_all_ones_mask_const(&mut self) -> ValueId {
        self.emit(Inst::Const {
            ty: Ty::v2_i64(),
            value: Constant::v2_i64_all_ones_mask(),
        })
    }

    fn v4_i32_zero_mask_const(&mut self) -> ValueId {
        self.emit(Inst::Const {
            ty: Ty::v4_i32(),
            value: Constant::v4_i32_zero_mask(),
        })
    }

    fn v4_i32_all_ones_mask_const(&mut self) -> ValueId {
        self.emit(Inst::Const {
            ty: Ty::v4_i32(),
            value: Constant::v4_i32_all_ones_mask(),
        })
    }

    fn v4_i32_mask_select(
        &mut self,
        cond: ValueId,
        then_val: ValueId,
        else_val: ValueId,
    ) -> ValueId {
        self.select(Ty::v4_i32(), cond, then_val, else_val)
    }

    fn v2_i64_mask_select(
        &mut self,
        cond: ValueId,
        then_val: ValueId,
        else_val: ValueId,
    ) -> ValueId {
        self.select(Ty::v2_i64(), cond, then_val, else_val)
    }

    fn v4_i32_splat_lane(&mut self, lane: ValueId) -> Result<ValueId, String> {
        vector_dialect_op_one_result(self, vector::v4_i32_splat_lane(lane)?)
    }

    fn v2_i64_splat_lane(&mut self, lane: ValueId) -> Result<ValueId, String> {
        vector_dialect_op_one_result(self, vector::v2_i64_splat_lane(lane)?)
    }

    fn vector_pack_lanes(
        &mut self,
        vector_ty: Ty,
        lanes: impl IntoIterator<Item = ValueId>,
    ) -> Result<ValueId, String> {
        vector_dialect_op_one_result(self, vector::pack_lanes(vector_ty, lanes))
    }

    fn vector_extract_lane(
        &mut self,
        vector_ty: Ty,
        vector: ValueId,
        lane: u32,
    ) -> Result<ValueId, String> {
        vector_dialect_op_one_result(self, vector::extract_lane(vector_ty, vector, lane))
    }

    fn vector_insert_lane(
        &mut self,
        vector_ty: Ty,
        vector: ValueId,
        lane: u32,
        value: ValueId,
    ) -> Result<ValueId, String> {
        vector_dialect_op_one_result(self, vector::insert_lane(vector_ty, vector, lane, value))
    }

    fn vector_mask_to_bits(
        &mut self,
        mask_ty: Ty,
        mask: ValueId,
        result_ty: Ty,
    ) -> Result<ValueId, String> {
        vector_dialect_op_one_result(self, vector::mask_to_bits(mask_ty, mask, result_ty))
    }

    fn vector_reduce(
        &mut self,
        vector_ty: Ty,
        vector_val: ValueId,
        kind: vector::ReduceKind,
    ) -> Result<ValueId, String> {
        vector_dialect_op_one_result(self, vector::reduce(vector_ty, vector_val, kind))
    }

    fn vector_shuffle(
        &mut self,
        vector_ty: Ty,
        vector_val: ValueId,
        indices: impl Into<Vec<u8>>,
    ) -> Result<ValueId, String> {
        vector_dialect_op_one_result(self, vector::shuffle(vector_ty, vector_val, indices))
    }

    fn vector_fma(
        &mut self,
        vector_ty: Ty,
        a: ValueId,
        b: ValueId,
        c: ValueId,
    ) -> Result<ValueId, String> {
        vector_dialect_op_one_result(self, vector::fma(vector_ty, a, b, c))
    }

    fn v4_i32_pack_lanes(&mut self, lanes: [ValueId; 4]) -> Result<ValueId, String> {
        self.vector_pack_lanes(Ty::v4_i32(), lanes)
    }

    fn v2_i64_pack_lanes(&mut self, lanes: [ValueId; 2]) -> Result<ValueId, String> {
        self.vector_pack_lanes(Ty::v2_i64(), lanes)
    }

    fn v4_i32_extract_lane(&mut self, vector: ValueId, lane: u32) -> Result<ValueId, String> {
        self.vector_extract_lane(Ty::v4_i32(), vector, lane)
    }

    fn v2_i64_extract_lane(&mut self, vector: ValueId, lane: u32) -> Result<ValueId, String> {
        self.vector_extract_lane(Ty::v2_i64(), vector, lane)
    }

    fn v4_i32_insert_lane(
        &mut self,
        vector: ValueId,
        lane: u32,
        value: ValueId,
    ) -> Result<ValueId, String> {
        self.vector_insert_lane(Ty::v4_i32(), vector, lane, value)
    }

    fn v2_i64_insert_lane(
        &mut self,
        vector: ValueId,
        lane: u32,
        value: ValueId,
    ) -> Result<ValueId, String> {
        self.vector_insert_lane(Ty::v2_i64(), vector, lane, value)
    }

    fn v4_bool_mask_to_i32_bits(&mut self, mask: ValueId) -> Result<ValueId, String> {
        self.vector_mask_to_bits(Ty::v4_bool(), mask, Ty::I32)
    }

    fn v8_bool_mask_to_i32_bits(&mut self, mask: ValueId) -> Result<ValueId, String> {
        self.vector_mask_to_bits(Ty::v8_bool(), mask, Ty::I32)
    }

    fn v16_bool_mask_to_i32_bits(&mut self, mask: ValueId) -> Result<ValueId, String> {
        self.vector_mask_to_bits(Ty::v16_bool(), mask, Ty::I32)
    }

    fn v2_bool_mask_to_i32_bits(&mut self, mask: ValueId) -> Result<ValueId, String> {
        self.vector_mask_to_bits(Ty::v2_bool(), mask, Ty::I32)
    }

    fn v2_bool_mask_to_i64_bits(&mut self, mask: ValueId) -> Result<ValueId, String> {
        self.vector_mask_to_bits(Ty::v2_bool(), mask, Ty::I64)
    }
}

/// Emit a decoded-and-validated portable `vector.*` dialect op with exactly
/// one result (the shared plumbing behind the `vector_*` trait methods).
fn vector_dialect_op_one_result(
    fb: &mut FunctionBuilder<'_>,
    op: trust_ir::dialect::DialectInst,
) -> Result<ValueId, String> {
    vector::decode(&op)?;
    fb.dialect_op_one_result(op)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::builder::ModuleBuilder;
    use trust_ir::dialect;

    /// The demo helpers are veneers: the IR they emit is exactly what the
    /// general-purpose builder methods produce.
    #[test]
    fn demo_helpers_emit_identical_ir_to_core_methods() {
        let build_with_demo = || {
            let mut mb = ModuleBuilder::new("m");
            let ft = mb.add_func_type(vec![Ty::v4_i32(), Ty::v4_i32()], vec![Ty::v4_i32()]);
            let mut fb = mb.function("f", ft);
            let entry = fb.create_block();
            let a = fb.add_block_param(entry, Ty::v4_i32());
            let b = fb.add_block_param(entry, Ty::v4_i32());
            fb.switch_to_block(entry);
            let sum = fb.v4_i32_add(a, b);
            let mask = fb.v4_i32_icmp_slt(a, b);
            let sel = fb.v4_i32_mask_select(mask, sum, a);
            fb.ret(vec![sel]);
            fb.build();
            mb.build().expect("ModuleBuilder::build: test fixture")
        };
        let build_with_core = || {
            let mut mb = ModuleBuilder::new("m");
            let ft = mb.add_func_type(vec![Ty::v4_i32(), Ty::v4_i32()], vec![Ty::v4_i32()]);
            let mut fb = mb.function("f", ft);
            let entry = fb.create_block();
            let a = fb.add_block_param(entry, Ty::v4_i32());
            let b = fb.add_block_param(entry, Ty::v4_i32());
            fb.switch_to_block(entry);
            let sum = fb.add(Ty::v4_i32(), a, b);
            let mask = fb.icmp(ICmpOp::Slt, Ty::v4_i32(), a, b);
            let sel = fb.select(Ty::v4_i32(), mask, sum, a);
            fb.ret(vec![sel]);
            fb.build();
            mb.build().expect("ModuleBuilder::build: test fixture")
        };
        assert_eq!(build_with_demo(), build_with_core());
    }

    /// The vector dialect emitters still validate payloads before emission.
    #[test]
    fn demo_vector_dialect_emitters_still_decode_check() {
        let mut mb = ModuleBuilder::new("m");
        let ft = mb.add_func_type(vec![Ty::I32], vec![Ty::v4_i32()]);
        let mut fb = mb.function("f", ft);
        let entry = fb.create_block();
        let lane = fb.add_block_param(entry, Ty::I32);
        fb.switch_to_block(entry);
        let splat = fb.v4_i32_splat_lane(lane).expect("canonical splat decodes");
        // Out-of-range lane index is rejected by vector::decode, not emitted.
        assert!(fb.vector_extract_lane(Ty::v4_i32(), splat, 4).is_err());
        fb.ret(vec![splat]);
        fb.build();
        let module = mb.build().expect("ModuleBuilder::build: test fixture");
        let ops: Vec<_> = module.functions[0].blocks[0]
            .body
            .iter()
            .filter(|n| {
                matches!(&n.inst, Inst::DialectOp(op) if op.dialect == dialect::vector::DIALECT)
            })
            .collect();
        assert_eq!(ops.len(), 1, "only the valid dialect op was emitted");
    }
}

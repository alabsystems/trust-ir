-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import SemRUnsignedRemainder

namespace SemR.CanonicalUnsignedRemainder.Controls

theorem u8_max :
    SemR.evalBinop 64 .urem (.int .u8) (.int .u8 255) (.int .u8 2) =
      .ok (.int .u8 1) ∧
    TrustIr.semBinOpValues .URem .U8 (.int 8 255) (.int 8 2) = .ok (.int 8 1) := by
  constructor <;> rfl

theorem u32_max :
    SemR.evalBinop 64 .urem (.int .u32) (.int .u32 4294967295) (.int .u32 2) =
      .ok (.int .u32 1) ∧
    TrustIr.semBinOpValues .URem .U32 (.int 32 4294967295) (.int 32 2) =
      .ok (.int 32 1) := by
  constructor <;> rfl

theorem u64_max :
    SemR.evalBinop 64 .urem (.int .u64)
      (.int .u64 18446744073709551615) (.int .u64 2) = .ok (.int .u64 1) ∧
    TrustIr.semBinOpValues .URem .U64 (.int 64 18446744073709551615) (.int 64 2) =
      .ok (.int 64 1) := by
  constructor <;> rfl

theorem larger_divisor_retains_dividend :
    SemR.intBin .urem 8 3 4 = .ok 3 ∧
    TrustIr.semIntBinOp .URem 8 3 4 = .ok 3 := by
  constructor <;> rfl

theorem exact_multiple_has_zero_remainder :
    SemR.intBin .urem 8 18 3 = .ok 0 ∧
    TrustIr.semIntBinOp .URem 8 18 3 = .ok 0 := by
  constructor <;> rfl

theorem discard_zero_is_not_success :
    ¬ (∃ returned, SemR.intBin .urem 64 17 0 = .ok returned) ∧
    ¬ (∃ returned, TrustIr.semIntBinOp .URem 64 17 0 = .ok returned) := by
  simp [SemR.intBin, TrustIr.semIntBinOp]

theorem source_wrong_remainder : SemR.intBin .urem 8 255 2 ≠ .ok 127 := by
  simp [SemR.intBin]

theorem target_wrong_remainder : TrustIr.semIntBinOp .URem 8 255 2 ≠ .ok 127 := by
  simp [TrustIr.semIntBinOp]

theorem false_post_stays_false :
    ¬ (∃ returned, SemR.intBin .urem 8 255 2 = .ok returned ∧ returned = 2) ∧
    ¬ (∃ returned, TrustIr.semIntBinOp .URem 8 255 2 = .ok returned ∧ returned = 2) := by
  simp [SemR.intBin, TrustIr.semIntBinOp]

end SemR.CanonicalUnsignedRemainder.Controls

-- Copyright 2026 Andrew Yates
-- Licensed under the Apache License, Version 2.0
import SemRUnsignedDivision

namespace SemR.CanonicalUnsignedDivision.Controls

theorem u8_max :
    SemR.evalBinop 64 .udiv (.int .u8) (.int .u8 255) (.int .u8 2) =
      .ok (.int .u8 127) ∧
    TrustIr.semBinOpValues .UDiv .U8 (.int 8 255) (.int 8 2) = .ok (.int 8 127) := by
  constructor <;> rfl

theorem u32_max :
    SemR.evalBinop 64 .udiv (.int .u32) (.int .u32 4294967295) (.int .u32 2) =
      .ok (.int .u32 2147483647) ∧
    TrustIr.semBinOpValues .UDiv .U32 (.int 32 4294967295) (.int 32 2) =
      .ok (.int 32 2147483647) := by
  constructor <;> rfl

theorem u64_max :
    SemR.evalBinop 64 .udiv (.int .u64)
      (.int .u64 18446744073709551615) (.int .u64 2) =
      .ok (.int .u64 9223372036854775807) ∧
    TrustIr.semBinOpValues .UDiv .U64 (.int 64 18446744073709551615) (.int 64 2) =
      .ok (.int 64 9223372036854775807) := by
  constructor <;> rfl

theorem discard_zero_is_not_success :
    ¬ (∃ returned, SemR.intBin .udiv 64 17 0 = .ok returned) := by
  simp [SemR.intBin]

theorem source_wrong_quotient : SemR.intBin .udiv 8 255 2 ≠ .ok 128 := by
  simp [SemR.intBin]

theorem target_wrong_quotient : TrustIr.semIntBinOp .UDiv 8 255 2 ≠ .ok 128 := by
  simp [TrustIr.semIntBinOp]

theorem false_post_stays_false :
    ¬ (∃ returned, SemR.intBin .udiv 8 255 2 = .ok returned ∧ returned = 128) ∧
    ¬ (∃ returned, TrustIr.semIntBinOp .UDiv 8 255 2 = .ok returned ∧ returned = 128) := by
  simp [SemR.intBin, TrustIr.semIntBinOp]

end SemR.CanonicalUnsignedDivision.Controls

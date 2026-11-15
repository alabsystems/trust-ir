/- Copyright 2026 Andrew Yates. Apache-2.0.
   Exact shared-lowered original source capture. Kernel evaluation of these
   bytes is not a MIR-to-IR simulation theorem or source certification. -/
import SemREntryBody
namespace SemR.SourceBodyCheck
open SemR
set_option maxRecDepth 20000
set_option maxHeartbeats 0
def originalBytes : List Nat := [84, 82, 85, 83, 84, 95, 73, 82, 38, 0, 0, 0, 3, 27, 112, 114, 111, 111, 102, 95, 114, 101, 102, 95, 107, 105, 110, 100, 95, 105, 115, 95, 97, 109, 98, 105, 103, 117, 111, 117, 115, 49, 116, 114, 117, 115, 116, 95, 105, 114, 58, 58, 112, 114, 111, 111, 102, 58, 58, 111, 98, 108, 105, 103, 97, 116, 105, 111, 110, 115, 58, 58, 79, 98, 108, 105, 103, 97, 116, 105, 111, 110, 75, 105, 110, 100, 83, 104, 97, 112, 101, 5, 95, 95, 116, 97, 103, 0, 1, 1, 16, 0, 1, 12, 0, 1, 0, 1, 1, 2, 3, 0, 0, 0, 0, 0, 0, 0, 0, 1, 5, 1, 0, 0, 0, 0, 11, 0, 1, 0, 16, 0, 3, 8, 12, 0, 0, 1, 4, 0, 0, 0, 0, 21, 3, 0, 0, 1, 5, 0, 0, 0, 0, 17, 5, 9, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 0, 0, 9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 1, 0, 4, 25, 12, 2, 1, 1, 6, 0, 0, 0, 0, 31, 12, 6, 1, 7, 0, 0, 0, 0, 7, 12, 4, 7, 0, 0, 0, 0, 0, 0, 0, 15, 10, 0, 0, 0, 0, 0, 0, 2, 0, 4, 25, 12, 2, 1, 1, 8, 0, 0, 0, 0, 31, 12, 8, 1, 9, 0, 0, 0, 0, 7, 12, 4, 9, 0, 0, 0, 0, 0, 0, 0, 15, 10, 0, 0, 0, 0, 0, 0, 3, 0, 4, 25, 12, 2, 1, 1, 10, 0, 0, 0, 0, 31, 12, 10, 1, 11, 0, 0, 0, 0, 7, 12, 4, 11, 0, 0, 0, 0, 0, 0, 0, 15, 10, 0, 0, 0, 0, 0, 0, 4, 0, 4, 25, 12, 2, 1, 1, 12, 0, 0, 0, 0, 31, 12, 12, 1, 13, 0, 0, 0, 0, 7, 12, 4, 13, 0, 0, 0, 0, 0, 0, 0, 15, 10, 0, 0, 0, 0, 0, 0, 5, 0, 4, 25, 12, 2, 1, 1, 14, 0, 0, 0, 0, 31, 12, 14, 1, 15, 0, 0, 0, 0, 7, 12, 4, 15, 0, 0, 0, 0, 0, 0, 0, 15, 10, 0, 0, 0, 0, 0, 0, 6, 0, 4, 25, 12, 2, 1, 1, 16, 0, 0, 0, 0, 31, 12, 16, 1, 17, 0, 0, 0, 0, 7, 12, 4, 17, 0, 0, 0, 0, 0, 0, 0, 15, 10, 0, 0, 0, 0, 0, 0, 7, 0, 4, 25, 12, 2, 1, 1, 18, 0, 0, 0, 0, 31, 12, 18, 1, 19, 0, 0, 0, 0, 7, 12, 4, 19, 0, 0, 0, 0, 0, 0, 0, 15, 10, 0, 0, 0, 0, 0, 0, 8, 0, 4, 25, 12, 2, 1, 1, 20, 0, 0, 0, 0, 31, 12, 20, 1, 21, 0, 0, 0, 0, 7, 12, 4, 21, 0, 0, 0, 0, 0, 0, 0, 15, 10, 0, 0, 0, 0, 0, 0, 9, 0, 4, 25, 12, 2, 0, 1, 22, 0, 0, 0, 0, 31, 12, 22, 1, 23, 0, 0, 0, 0, 7, 12, 4, 23, 0, 0, 0, 0, 0, 0, 0, 15, 10, 0, 0, 0, 0, 0, 0, 10, 0, 3, 6, 12, 4, 0, 0, 1, 24, 0, 0, 0, 0, 31, 12, 24, 1, 25, 0, 0, 0, 0, 20, 1, 25, 0, 0, 0, 0, 0, 1, 10, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def mutantBytes : List Nat := [84, 82, 85, 83, 84, 95, 73, 82, 38, 0, 0, 0, 3, 27, 112, 114, 111, 111, 102, 95, 114, 101, 102, 95, 107, 105, 110, 100, 95, 105, 115, 95, 97, 109, 98, 105, 103, 117, 111, 117, 115, 49, 116, 114, 117, 115, 116, 95, 105, 114, 58, 58, 112, 114, 111, 111, 102, 58, 58, 111, 98, 108, 105, 103, 97, 116, 105, 111, 110, 115, 58, 58, 79, 98, 108, 105, 103, 97, 116, 105, 111, 110, 75, 105, 110, 100, 83, 104, 97, 112, 101, 5, 95, 95, 116, 97, 103, 0, 1, 1, 16, 0, 1, 12, 0, 1, 0, 1, 1, 2, 3, 0, 0, 0, 0, 0, 0, 0, 0, 1, 5, 1, 0, 0, 0, 0, 11, 0, 1, 0, 16, 0, 3, 8, 12, 0, 0, 1, 4, 0, 0, 0, 0, 21, 3, 0, 0, 1, 5, 0, 0, 0, 0, 17, 5, 9, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 0, 0, 9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 1, 0, 4, 25, 12, 2, 0, 1, 6, 0, 0, 0, 0, 31, 12, 6, 1, 7, 0, 0, 0, 0, 7, 12, 4, 7, 0, 0, 0, 0, 0, 0, 0, 15, 10, 0, 0, 0, 0, 0, 0, 2, 0, 4, 25, 12, 2, 1, 1, 8, 0, 0, 0, 0, 31, 12, 8, 1, 9, 0, 0, 0, 0, 7, 12, 4, 9, 0, 0, 0, 0, 0, 0, 0, 15, 10, 0, 0, 0, 0, 0, 0, 3, 0, 4, 25, 12, 2, 1, 1, 10, 0, 0, 0, 0, 31, 12, 10, 1, 11, 0, 0, 0, 0, 7, 12, 4, 11, 0, 0, 0, 0, 0, 0, 0, 15, 10, 0, 0, 0, 0, 0, 0, 4, 0, 4, 25, 12, 2, 1, 1, 12, 0, 0, 0, 0, 31, 12, 12, 1, 13, 0, 0, 0, 0, 7, 12, 4, 13, 0, 0, 0, 0, 0, 0, 0, 15, 10, 0, 0, 0, 0, 0, 0, 5, 0, 4, 25, 12, 2, 1, 1, 14, 0, 0, 0, 0, 31, 12, 14, 1, 15, 0, 0, 0, 0, 7, 12, 4, 15, 0, 0, 0, 0, 0, 0, 0, 15, 10, 0, 0, 0, 0, 0, 0, 6, 0, 4, 25, 12, 2, 1, 1, 16, 0, 0, 0, 0, 31, 12, 16, 1, 17, 0, 0, 0, 0, 7, 12, 4, 17, 0, 0, 0, 0, 0, 0, 0, 15, 10, 0, 0, 0, 0, 0, 0, 7, 0, 4, 25, 12, 2, 1, 1, 18, 0, 0, 0, 0, 31, 12, 18, 1, 19, 0, 0, 0, 0, 7, 12, 4, 19, 0, 0, 0, 0, 0, 0, 0, 15, 10, 0, 0, 0, 0, 0, 0, 8, 0, 4, 25, 12, 2, 1, 1, 20, 0, 0, 0, 0, 31, 12, 20, 1, 21, 0, 0, 0, 0, 7, 12, 4, 21, 0, 0, 0, 0, 0, 0, 0, 15, 10, 0, 0, 0, 0, 0, 0, 9, 0, 4, 25, 12, 2, 0, 1, 22, 0, 0, 0, 0, 31, 12, 22, 1, 23, 0, 0, 0, 0, 7, 12, 4, 23, 0, 0, 0, 0, 0, 0, 0, 15, 10, 0, 0, 0, 0, 0, 0, 10, 0, 3, 6, 12, 4, 0, 0, 1, 24, 0, 0, 0, 0, 31, 12, 24, 1, 25, 0, 0, 0, 0, 20, 1, 25, 0, 0, 0, 0, 0, 1, 10, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def original : Module := match decode originalBytes with
  | .ok m => m
  | .error _ => {funcTys := [], enums := [], functions := []}
def mutant : Module := match decode mutantBytes with
  | .ok m => m
  | .error _ => {funcTys := [], enums := [], functions := []}
theorem original_decodes : decode originalBytes = .ok original := rfl
theorem mutant_decodes : decode mutantBytes = .ok mutant := rfl
/-- Exact captured formal: one nominal struct lane, no callee declarations. -/
theorem original_custody :
    original.funcTys = [{params := [.struct 0], returns := [.bool], vararg := false}] ∧
    original.structs = [{id := 0, fields := [.int .i64]}] ∧
    original.functions.length = 1 := by exact ⟨rfl, rfl, rfl⟩
def execute (m : Module) (tag : Nat) : Out :=
  runFunction m 0 [.struct 0 [.int .i64 tag]] 40 4
/-- The existing checked entry/body contract applies to the actually read
    integer, without identifying a source enum with this legacy struct. -/
theorem original_read_word_bound {raw : Nat}
    (h : evalExtract original (.int .i64) (.struct 0 [.int .i64 raw]) 0 =
      .ok (.int .i64 raw)) : raw < modulus 64 := by
  have checked : expectTy original.pointerBits (.int .i64 raw) (.int .i64) = .ok () := by
    change (expectTy original.pointerBits (.int .i64 raw) (.int .i64) >>= fun _ =>
      R.ok (Val.int .i64 raw)) = R.ok (Val.int .i64 raw) at h
    cases hc : expectTy original.pointerBits (.int .i64 raw) (.int .i64) with
    | stop out =>
      rw [hc] at h
      change R.stop out = R.ok (Val.int .i64 raw) at h
      cases h
    | ok u => cases u; rfl
  exact SemR.EntryDomain.checked_integer_raw_bound checked
/-- All sixteen captured fieldless discriminants, in original metadata order.
    This finite table makes no claim about source validity or arbitrary inputs. -/
theorem original_discriminants :
    (List.range 16).map (execute original) =
      [.ret [.bool true], .ret [.bool true], .ret [.bool true], .ret [.bool true],
       .ret [.bool true], .ret [.bool true], .ret [.bool false], .ret [.bool false],
       .ret [.bool true], .ret [.bool true], .ret [.bool false], .ret [.bool false],
       .ret [.bool false], .ret [.bool false], .ret [.bool false], .ret [.bool false]] := rfl
/-- The first original true assignment changed to false by the ordinary producer. -/
theorem original_body_change_observed : execute mutant 0 = .ret [.bool false] := rfl
theorem body_change_not_original : execute mutant 0 ≠ execute original 0 := by
  intro h; cases h
/-- Untouched arm retains its actual outcome; the mutation is not a global flag. -/
theorem untouched_body_arm : execute mutant 1 = .ret [.bool true] := rfl
theorem wrong_formal_identity :
    runFunction original 0 [.struct 1 [.int .i64 0]] 40 4 =
      .typeError "SignatureMismatch: type mismatch" := rfl
theorem missing_actual_lane :
    runFunction original 0 [.struct 0 []] 40 4 =
      .typeError "TypeError: struct lane arity" := rfl
theorem budget_is_not_erased :
    runFunction original 0 [.struct 0 [.int .i64 0]] 1 4 = .outOfFuel := rfl
theorem missing_callee_refuses :
    runFunction original 1 [.struct 0 [.int .i64 0]] 40 4 =
      .typeError "MissingFunction: function not found" := rfl
/-- The decoder admits only logical flat scalar declarations. -/
theorem flat_scalar_decode :
    flatStructDef 38 #[[]] [0,0,1,0,3,0,0,0,0] =
      .ok {id := 0, fields := [.int .i64]} [] := rfl
theorem layout_offset_refuses :
    flatStructDef 38 #[[]] [0,0,1,0,3,1] =
      .err (.unsupported "struct.field_offset") := rfl
theorem pointer_field_refuses :
    flatStructDef 38 #[[]] [0,0,1,0,13,0,0,0,0] =
      .err (.unsupported "struct.field_type") := rfl
theorem tuple_stays_refused : ty 38 #[] [18,0] =
    .err (.unsupported "ty.compound") := rfl
theorem invalid_field_tag :
    flatStructDef 38 #[[]] [0,0,1,0,254,0,0,0,0] =
      .err (.malformed "invalid Ty tag") := rfl
theorem explicit_size_refuses :
    flatStructDef 38 #[[]] [0,0,0,1] = .err (.unsupported "struct.size") := rfl
theorem explicit_align_refuses :
    flatStructDef 38 #[[]] [0,0,0,0,1] = .err (.unsupported "struct.align") := rfl
theorem c_layout_refuses :
    flatStructDef 38 #[[]] [0,0,0,0,0,1] = .err (.unsupported "struct.repr") := rfl
theorem nominal_origin_refuses :
    flatStructDef 58 #[[]] [0,0,0,0,0,0,1] = .err (.unsupported "struct.origin") := rfl
theorem field_count_refuses_before_fields :
    flatStructDef 38 #[[]] ([0,0,129,1] ++ List.replicate 129 0) =
      .err (.unsupported "struct.field_count") := rfl
theorem malformed_presence_refuses :
    flatStructDef 38 #[[]] [0,0,1,0,3,2] = .err (.malformed "invalid tag") := rfl
theorem nested_struct_refuses :
    flatStructDef 38 #[[]] [0,0,1,0,16,0,0,0,0,0] =
      .err (.unsupported "struct.field_type") := rfl
end SemR.SourceBodyCheck

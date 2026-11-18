/-
  Candidate operational controls, not certificates for a source report.
  The callee below is quoted from the original 1116-row report's native bundle
  a4b3e7673ae64ffcfbe84105d0d276abad4fd2a6c20fc9e6fea521594db98b64:
  trust_ir::proof::obligations::ObligationKindShape::is_assert_class.
  Only Alloca/Load/Store are explicitly abstracted to typed private cells.
  Its caller's old Undef Struct seed is tested as a refusal, never repaired by
  zero/havoc substitution. The separate Uninit seed controls the canonical
  supported aggregate-construction operation, not the old source snapshot.
-/
import SemR

namespace PanicRelationCheck
open SemR

def actualCallee : Func :=
  { id := 1, ty := 1, entry := 0, blocks := [
    { id := 0, params := [(0, .struct 0)], body := [
      ⟨.allocaCell .bool, [3]⟩,
      ⟨.extractField (.int .i64) 0 0, [4]⟩,
      ⟨.switch 4 1 [] [(.int 10, 2, []), (.int 11, 2, [])], []⟩] },
    { id := 1, params := [], body := [
      ⟨.const .bool (.bool false), [5]⟩,
      ⟨.copy .bool 5, [6]⟩,
      ⟨.storeCell .bool 3 6, []⟩,
      ⟨.br 3 [], []⟩] },
    { id := 2, params := [], body := [
      ⟨.const .bool (.bool true), [7]⟩,
      ⟨.copy .bool 7, [8]⟩,
      ⟨.storeCell .bool 3 8, []⟩,
      ⟨.br 3 [], []⟩] },
    { id := 3, params := [], body := [
      ⟨.loadCell .bool 3, [9]⟩,
      ⟨.ret [9], []⟩] }] }

def actualModule : Module :=
  { funcTys := [⟨[], [.bool], false⟩, ⟨[.struct 0], [.bool], false⟩],
    enums := [], functions := [actualCallee],
    target := some ⟨[97,97,114,99,104,54,52,45,97,112,112,108,101,45,100,97,114,119,105,110],
      8, false, none, 0⟩,
    structs := [{ id := 0, fields := [.int .i64] }] }

def actualRun (tag : Nat) : Out :=
  runFunction actualModule 1 [.struct 0 [.int .i64 tag]] 40 8

theorem actual_case_10 : actualRun 10 = .ret [.bool true] := by rfl
theorem actual_case_11 : actualRun 11 = .ret [.bool true] := by rfl
theorem actual_default : actualRun 9 = .ret [.bool false] := by rfl
theorem actual_unbounded_default : actualRun 18446744073709551615 = .ret [.bool false] := by rfl
theorem actual_wrong_result : actualRun 10 ≠ .ret [.bool false] := by intro h; cases h

/-- Uninhabited goals offered the honest proof by the independent native
    checker. These are not axioms or premises of any theorem. -/
def WrongResult : Prop := actualRun 10 = .ret [.bool false]

def changedCallee : Func :=
  { actualCallee with blocks := [
    ⟨0, [(0, .struct 0)], [⟨.const .bool (.bool false), [1]⟩, ⟨.ret [1], []⟩]⟩] }
def WrongBody : Prop := runFunction { actualModule with functions := [changedCallee] }
  1 [.struct 0 [.int .i64 10]] 40 8 = .ret [.bool true]

/-- The general theorem consumes THIS returned body execution; no solver
    verdict or row's free Boolean is a premise. Instruction budget 40 is only
    the witness: the conclusion excludes all finite bad reachable prefixes. -/
theorem actual_no_bad (initial : Core)
    (started : start actualModule 1 [.struct 0 [.int .i64 10]] 8 = .ok initial) :
    ¬ BodyViolation actualModule initial := by
  apply returned_excludes_body_violation actualModule initial 40 [.bool true]
  have execution := actual_case_10
  simp only [actualRun, runFunction, started] at execution
  exact execution

def oneBlock (params : List (Nat × Ty)) (body : List Node) : Module :=
  { funcTys := [⟨params.map Prod.snd, [.bool], false⟩], enums := [],
    functions := [⟨0, 0, 0, [⟨0, params, body⟩], []⟩] }

def aliasModule : Module := oneBlock [(0, .bool)] [
  ⟨.allocaCell .bool, [1]⟩,
  ⟨.copy .ptr 1, [2]⟩,
  ⟨.storeCell .bool 2 0, []⟩,
  ⟨.loadCell .bool 1, [3]⟩,
  ⟨.ret [3], []⟩]

theorem alias_parameter (b : Bool) :
    runFunction aliasModule 0 [.bool b] 10 8 = .ret [.bool b] := by cases b <;> rfl

def mutatingCallee : Func := ⟨1, 1, 0, [⟨0, [(0, .ptr), (1, .bool)], [
  ⟨.storeCell .bool 0 1, []⟩, ⟨.ret [], []⟩]⟩], []⟩

def sharedCallModule : Module :=
  { funcTys := [⟨[.bool], [.bool], false⟩, ⟨[.ptr, .bool], [], false⟩], enums := [],
    functions := [⟨0, 0, 0, [⟨0, [(0, .bool)], [
      ⟨.allocaCell .bool, [1]⟩, ⟨.call 1 [1, 0], []⟩,
      ⟨.loadCell .bool 1, [2]⟩, ⟨.ret [2], []⟩]⟩], []⟩, mutatingCallee] }

theorem callee_mutates_shared_cell (b : Bool) :
    runFunction sharedCallModule 0 [.bool b] 12 8 = .ret [.bool b] := by cases b <;> rfl

def sharedCallTarget (is32 : Bool) : Module :=
  { sharedCallModule with target := some ⟨
      ((if is32 then "wasm32-unknown-unknown" else "aarch64-apple-darwin").toList.map Char.toNat),
      (if is32 then 4 else 8), false, none, 2⟩ }

theorem callee_mutates_shared_cell_at_both_widths (is32 b : Bool) :
    runFunction (sharedCallTarget is32) 0 [.bool b] 12 8 = .ret [.bool b] := by
  cases is32 <;> cases b <;> rfl

def wrongCallResultModule : Module :=
  { sharedCallModule with funcTys := [⟨[.bool], [.bool], false⟩,
      ⟨[.ptr, .bool], [.bool], false⟩] }

def WrongCallResult : Prop :=
  runFunction wrongCallResultModule 0 [.bool true] 12 8 = .ret [.bool true]

theorem wrong_call_result_refuses :
    runFunction wrongCallResultModule 0 [.bool true] 12 8 =
      .typeError "SignatureMismatch: arity mismatch" := by rfl

def uninitialized : Module := oneBlock [] [
  ⟨.allocaCell .bool, [0]⟩, ⟨.loadCell .bool 0, [1]⟩, ⟨.ret [1], []⟩]

theorem uninitialized_return_refuses : runFunction uninitialized 0 [] 10 8 =
    .ub "signature boundary: use of an uninitialized value (poison)" := by rfl

def disjoint : Module := oneBlock [(0, .bool)] [
  ⟨.allocaCell .bool, [1]⟩, ⟨.allocaCell .bool, [2]⟩,
  ⟨.storeCell .bool 2 0, []⟩, ⟨.loadCell .bool 1, [3]⟩, ⟨.ret [3], []⟩]

theorem distinct_cells_do_not_alias : runFunction disjoint 0 [.bool true] 10 8 =
    .ub "signature boundary: use of an uninitialized value (poison)" := by rfl

def wrongCellType : Module := oneBlock [] [
  ⟨.allocaCell .bool, [0]⟩, ⟨.loadCell (.int .u32) 0, [1]⟩, ⟨.ret [1], []⟩]

theorem wrong_cell_type_refuses : runFunction wrongCellType 0 [] 10 8 =
    .typeError "TypeError: private cell access type mismatch" := by rfl

def forgedCell : Module := oneBlock [(0, .ptr)] [
  ⟨.loadCell .bool 0, [1]⟩, ⟨.ret [1], []⟩]

theorem missing_cell_refuses : runFunction forgedCell 0 [.cellPtr 0] 10 8 =
    .ub "private cell address has no allocation" := by rfl

theorem frame_is_not_cell : runFunction forgedCell 0 [.frame 0 []] 10 8 =
    .typeError "TypeError: expected a private cell address" := by rfl

def assumeFalse : Module := oneBlock [(0, .bool)] [⟨.assume 0, []⟩, ⟨.ret [0], []⟩]
theorem false_assumption_refuses : runFunction assumeFalse 0 [.bool false] 10 8 =
    .ub "assume condition evaluated to false: the input lies outside the assumed domain" := by rfl

theorem original_aggregate_undef_refuses : undefVal (.struct 0) =
    .stop (.ub "undef of non-scalar type is not executable (aggregate poison unmodelled)") := by rfl

def uninitSeed : Const := .aggregate [.uninit]
theorem supported_uninit_seed : constVal actualModule 8 (.struct 0) uninitSeed =
    .ok (.struct 0 [.unwritten (.int .i64)]) := by rfl

theorem unwritten_read_refuses :
    evalExtract actualModule (.int .i64) (.struct 0 [.unwritten (.int .i64)]) 0 =
      .stop (.ub "extract_field: read of an unwritten aggregate lane (uninit)") := by rfl

theorem insertion_initializes_only_its_lane :
    evalInsert actualModule (.struct 0) (.struct 0 [.unwritten (.int .i64)]) 0 (.int .i64 10) =
      .ok (.struct 0 [.int .i64 10]) := by rfl

theorem scalar_uninit_refuses : constVal actualModule 8 (.int .i64) .uninit =
    .stop (.unsupported "constant.shape") := by rfl

def nestedModule : Module := { actualModule with
  structs := [{ id := 0, fields := [.struct 1] }, { id := 1, fields := [.int .i64] }] }
theorem nested_uninit_refuses : constVal nestedModule 8 (.struct 0) (.aggregate [uninitSeed]) =
    .stop (.typeError "TypeError: misplaced uninit constant") := by rfl

theorem exhausted_is_not_returned : runFunction aliasModule 0 [.bool true] 1 8 ≠
    .ret [.bool true] := by intro h; cases h

theorem wrong_target_refuses :
    runFunction { actualModule with target := some ⟨[120], 8, false, none, 0⟩ }
      1 [.struct 0 [.int .i64 10]] 40 8 = .unsupported "target.byte_model" := by rfl

end PanicRelationCheck

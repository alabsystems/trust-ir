/- Universal initialized-integer selection plus adversarial operational controls.
   These are checked over the existing SemR, never an alternative interpreter. -/
import SemRUnsignedSelect

namespace SemRUnsignedSelectCheck
open SemR SemRUnsignedSelect

def model : Module := { funcTys := [], enums := [], functions := [] }

def state (env : List (Nat × Val)) (nodes : List Node := [])
    (returns : List Ty := []) : Core :=
  { fn := { id := 0, ty := 0, entry := 0, blocks := [], name := [] },
    sig := { params := [], returns := returns, vararg := false },
    block := { id := 0, params := [], body := nodes },
    pc := 0, env := env, depth := 0, stack := [], openFrames := [],
    nextFrame := 0, mem := Mem.empty }

/-- Arbitrary original symbolic operands and Boolean guard, not bounded samples.
    The exact original values remain visible in the postcondition. -/
theorem symbolic_select (m : Module) (t : IntTy) (c : Bool) (a b : Nat)
    (ha : a < modulus (t.bits m.pointerBits))
    (hb : b < modulus (t.bits m.pointerBits)) :
    let k := state [(0, .bool c), (1, .int t a), (2, .int t b)] [selectUInt 3 0 1 2 t]
    ∃ k', Step m k (.cont k') ∧ k'.block = k.block ∧ k'.pc = k.pc + 1 ∧
      getV k' 3 = .ok (.int t (if c then a else b)) := by
  let k := state [(0, .bool c), (1, .int t a), (2, .int t b)] [selectUInt 3 0 1 2 t]
  apply selectUInt_wp_step m k 3 0 1 2 t _ (by rfl)
  refine ⟨c, a, b, rfl, rfl, rfl, ha, hb, ?_, ?_⟩
  · intro hc
    cases c <;> simp_all [writeUInt, next, getV, lookupEnv]
  · intro hc
    cases c <;> simp_all [writeUInt, next, getV, lookupEnv]

theorem u64_max_is_in_the_original_domain :
    18446744073709551615 < modulus (IntTy.u64.bits 64) := by decide

theorem u64_max_const_exact :
    execNode model (state []) (constUInt 3 .u64 18446744073709551615) =
      .cont (writeUInt (state []) 3 .u64 18446744073709551615) := rfl

theorem u64_max_select_exact (c : Bool) :
    execNode model
      (state [(0, .bool c), (1, .int .u64 0), (2, .int .u64 18446744073709551615)])
      (selectUInt 3 0 1 2 .u64) =
    .cont (writeUInt
      (state [(0, .bool c), (1, .int .u64 0), (2, .int .u64 18446744073709551615)])
      3 .u64 (if c then 0 else 18446744073709551615)) :=
  selectUInt_step model _ 3 0 1 2 .u64 c 0 18446744073709551615
    rfl rfl rfl (by decide) (by decide)

theorem u64_max_compare_zero_is_false :
    execNode model
      (state [(1, .int .u64 18446744073709551615), (2, .int .u64 0)])
      (icmpEqUInt 3 1 2 .u64) =
    .cont (writeBoolResult
      (state [(1, .int .u64 18446744073709551615), (2, .int .u64 0)]) 3 false) := rfl

theorem u64_max_return_exact :
    execNode model (state [(1, .int .u64 18446744073709551615)] [] [.int .u64])
      (returnUInt 1) = .done (.ret [.int .u64 18446744073709551615]) := rfl

/-- Eagerness: the invalid arm cannot be hidden behind a true condition. -/
theorem unselected_out_of_range_refuses :
    execNode model (state [(0, .bool true), (1, .int .u8 0), (2, .int .u8 256)])
      (selectUInt 3 0 1 2 .u8) =
    .done (.typeError "TypeError: integer value is out of range for the target width") := rfl

theorem unselected_wrong_width_refuses :
    execNode model (state [(0, .bool true), (1, .int .u8 0), (2, .int .u64 0)])
      (selectUInt 3 0 1 2 .u8) =
    .done (.typeError "TypeError: value does not have the expected type") := rfl

theorem unselected_missing_value_refuses :
    execNode model (state [(0, .bool true), (1, .int .u8 0)]) (selectUInt 3 0 1 2 .u8) =
      .done (.typeError "MissingValue: value is not defined") := rfl

theorem integer_condition_refuses :
    execNode model (state [(0, .int .u8 1), (1, .int .u8 0), (2, .int .u8 1)])
      (selectUInt 3 0 1 2 .u8) =
    .done (.typeError "TypeError: select requires a bool condition") := rfl

theorem poisoned_condition_is_ub :
    execNode model (state [(0, .poison .bool), (1, .int .u8 0), (2, .int .u8 1)])
      (selectUInt 3 0 1 2 .u8) =
    .done (.ub "select: use of an uninitialized value (poison)") := rfl

theorem missing_result_refuses :
    execNode model (state [(0, .bool true), (1, .int .u8 0), (2, .int .u8 1)])
      { inst := .select (.int .u8) 0 1 2, results := [] } =
    .done (.typeError "MalformedInstruction: instruction result arity mismatch") := rfl

theorem different_actual_instruction_cannot_supply_select_pc :
    let k := state [(0, .bool true), (1, .int .u8 0), (2, .int .u8 255)]
      [copyUInt 3 1 .u8]
    nth? k.block.body k.pc ≠ some (selectUInt 3 0 1 2 .u8) := by
  change some (copyUInt 3 1 .u8) ≠ some (selectUInt 3 0 1 2 .u8)
  intro wrong
  cases wrong

theorem swapped_arms_are_not_the_original_result :
    execNode model (state [(0, .bool true), (1, .int .u8 0), (2, .int .u8 255)])
      (selectUInt 3 0 2 1 .u8) ≠
    .cont (writeUInt (state [(0, .bool true), (1, .int .u8 0), (2, .int .u8 255)])
      3 .u8 0) := by
  intro wrong
  cases wrong

/-- A typed poison can be MOVED by SemR selection, but never be inspected or
    returned as an initialized integer. Do not claim a poison-rejecting Select
    semantics merely because the initialized WP fragment excludes it. -/
theorem unselected_typed_poison_can_be_moved :
    execNode model (state [(0, .bool true), (1, .int .u8 0), (2, .poison (.int .u8))])
      (selectUInt 3 0 1 2 .u8) =
    .cont (writeUInt (state [(0, .bool true), (1, .int .u8 0), (2, .poison (.int .u8))])
      3 .u8 0) := rfl

theorem selected_poison_return_is_ub :
    execNode model (state [(3, .poison (.int .u8))] [] [.int .u8]) (returnUInt 3) =
      .done (.ub "signature boundary: use of an uninitialized value (poison)") := rfl

end SemRUnsignedSelectCheck

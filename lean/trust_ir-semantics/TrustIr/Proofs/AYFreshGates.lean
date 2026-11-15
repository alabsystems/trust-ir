-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import TrustIr.Proofs.AYAdderCNF

namespace TrustIr.AYGateCNF

def Gate.inputs : Gate → List Nat
  | .xor2 _ a b => [a, b]
  | .and2 _ a b => [a, b]
  | .or2 _ a b => [a, b]
  | .xor3 _ a b c => [a, b, c]
  | .fullAdderCarry _ a b c => [a, b, c]
  | .not _ a => [a]
  | .constTrue _ => []
  | .constFalse _ => []
  | .xnorEq _ a b => [a, b]

/-- Gate semantics depends exactly on its recorded input ids. -/
theorem Gate.eval_congr (gate : Gate) (left right : Assignment)
    (agree : ∀ id ∈ gate.inputs, left id = right id) : gate.eval left = gate.eval right := by
  cases gate <;> simp_all [Gate.inputs, Gate.eval]

/-- Define one output without changing any other variable. -/
def Gate.apply (gate : Gate) (env : Assignment) : Assignment :=
  fun id => if id = gate.output then gate.eval env else env id

/-- A gate's output is fresh and its inputs were already allocated. -/
inductive Valid : Nat → List Gate → Prop where
  | nil (next : Nat) : Valid next []
  | cons {next : Nat} {gate : Gate} {tail : List Gate}
      (output : gate.output = next) (inputs : ∀ id ∈ gate.inputs, id < next)
      (rest : Valid (next + 1) tail) : Valid next (gate :: tail)

/-- Validate exact sequential output ids and strictly earlier inputs. -/
private def checkProgramSpec (next : Nat) (gates : List Gate) : Bool :=
  gates.foldr (fun gate rest next =>
    (gate.output == next) && gate.inputs.all (fun id => decide (id < next)) && rest (next + 1))
    (fun _ => true) next

/-- Validate sequential outputs and earlier inputs with constant call-stack depth. -/
def checkProgram (next : Nat) (gates : List Gate) : Bool :=
  (gates.foldl (fun (state : Nat × Bool) gate =>
    (state.1 + 1, state.2 && ((gate.output == state.1) &&
      gate.inputs.all (fun id => decide (id < state.1))))) (next, true)).2

private theorem checkProgram_fold (gates : List Gate) (next : Nat) (accepted : Bool) :
    (gates.foldl (fun (state : Nat × Bool) gate =>
      (state.1 + 1, state.2 && ((gate.output == state.1) &&
        gate.inputs.all (fun id => decide (id < state.1))))) (next, accepted)).2 =
      (accepted && checkProgramSpec next gates) := by
  induction gates generalizing next accepted with
  | nil => simp [checkProgramSpec]
  | cons gate rest ih =>
    simp only [List.foldl]
    rw [ih]
    exact Bool.and_assoc _ _ _

theorem checkProgram_eq_spec (next : Nat) (gates : List Gate) :
    checkProgram next gates = gates.foldr (fun gate rest next =>
      (gate.output == next) && gate.inputs.all (fun id => decide (id < next)) && rest (next + 1))
      (fun _ => true) next := by
  change _ = checkProgramSpec next gates
  rw [checkProgram, checkProgram_fold]
  rfl

/-- Evaluate a validated program by extending the input assignment. -/
@[macro_inline] def run (gates : List Gate) (env : Assignment) : Assignment :=
  (gates.foldl (fun (current : Assignment × Unit) gate =>
    let value := gate.eval current.1
    ((fun id => if id = gate.output then value else current.1 id), ())) (env, ())).1

theorem checkProgram_iff (next : Nat) (gates : List Gate) :
    checkProgram next gates = true ↔ Valid next gates := by
  rw [checkProgram_eq_spec]
  change checkProgramSpec next gates = true ↔ Valid next gates
  induction gates generalizing next with
  | nil => exact ⟨fun _ => .nil next, fun _ => rfl⟩
  | cons gate tail ih =>
    change ((gate.output == next) && gate.inputs.all (fun id => decide (id < next)) &&
      checkProgramSpec (next + 1) tail) = true ↔ _
    simp only [Bool.and_eq_true, beq_iff_eq]
    constructor
    · rintro ⟨⟨output, inputs⟩, rest⟩
      apply Valid.cons output ?_ ((ih (next + 1)).mp rest)
      simpa using inputs
    · intro valid
      cases valid with
      | cons output inputs rest =>
        exact ⟨⟨output, by simpa using inputs⟩, (ih (next + 1)).mpr rest⟩

/-- Every fresh gate program has a model for EVERY original assignment.
Earlier variables survive, and all gate equations hold in the final model. -/
theorem Valid.run_correct {next : Nat} {gates : List Gate} (valid : Valid next gates)
    (env : Assignment) :
    (∀ id, id < next → run gates env id = env id) ∧
      (∀ gate ∈ gates, run gates env gate.output = gate.eval (run gates env)) := by
  induction valid generalizing env with
  | nil next => exact ⟨fun _ _ => rfl, fun _ member => nomatch member⟩
  | @cons next gate tail output inputs _rest ih =>
    obtain ⟨preserved, equations⟩ := ih (gate.apply env)
    have unchanged : gate.eval (gate.apply env) = gate.eval env := by
      apply gate.eval_congr
      intro id member
      have before := inputs id member
      simp [Gate.apply, output, show id ≠ next by omega]
    have headCorrect : gate.apply env gate.output = gate.eval (gate.apply env) := by
      calc
        gate.apply env gate.output = gate.eval env := by simp [Gate.apply]
        _ = gate.eval (gate.apply env) := unchanged.symm
    have outputPreserved := preserved gate.output (by omega)
    have inputsPreserved : gate.eval (run tail (gate.apply env)) = gate.eval (gate.apply env) := by
      apply gate.eval_congr
      intro id member
      exact preserved id (by have h := inputs id member; omega)
    constructor
    · intro id before
      change run tail (gate.apply env) id = env id
      rw [preserved id (by omega)]
      simp [Gate.apply, output, show id ≠ next by omega]
    · intro item member
      cases member with
      | head =>
        change run tail (gate.apply env) gate.output = gate.eval (run tail (gate.apply env))
        exact outputPreserved.trans (headCorrect.trans inputsPreserved.symm)
      | tail _ member => exact equations item member

/-- Executable acceptance constructs a CNF model and preserves all input ids. -/
theorem checkProgram_model (next : Nat) (gates : List Gate)
    (checked : checkProgram next gates = true) (env : Assignment) :
    CNF.eval (run gates env) (encode gates) = true ∧
      (∀ id, id < next → run gates env id = env id) := by
  obtain ⟨preserved, equations⟩ := ((checkProgram_iff next gates).mp checked).run_correct env
  exact ⟨(encode_correct _ _).mpr equations, preserved⟩

/-- Every CNF model extending the same inputs agrees with execution on every
allocated id. Model values outside the allocated range are irrelevant. -/
theorem Valid.model_agree {next : Nat} {gates : List Gate} (valid : Valid next gates)
    (env model : Assignment)
    (equations : ∀ gate ∈ gates, model gate.output = gate.eval model)
    (agree : ∀ id, id < next → model id = env id) :
    ∀ id, id < next + gates.length → model id = run gates env id := by
  induction valid generalizing env model with
  | nil next => simpa [run] using agree
  | @cons next gate tail output inputs _rest ih =>
    have gateEq := equations gate (List.Mem.head _)
    have evalEq : gate.eval model = gate.eval env := by
      apply gate.eval_congr
      intro id member
      exact agree id (inputs id member)
    have freshAgree : ∀ id, id < next + 1 → model id = gate.apply env id := by
      intro id bound
      by_cases before : id < next
      · simpa [Gate.apply, output, show id ≠ next by omega] using agree id before
      · have same : id = next := by omega
        subst id
        rw [output] at gateEq
        simpa [Gate.apply, output] using gateEq.trans evalEq
    have tailEquations : ∀ item ∈ tail, model item.output = item.eval model := by
      intro item member
      exact equations item (List.Mem.tail _ member)
    intro id bound
    change model id = run tail (gate.apply env) id
    apply ih (gate.apply env) model tailEquations freshAgree id
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using bound

/-- Exact asserted-CNF semantics under fixed input values. Existence is
constructed by execution; the converse uses uniqueness of allocated values. -/
theorem Valid.asserted_iff {next : Nat} {gates : List Gate} (valid : Valid next gates)
    (env : Assignment) (output : Nat) (bound : output < next + gates.length) :
    (∃ model : Assignment, (∀ id, id < next → model id = env id) ∧
      CNF.eval model (assertOutput gates output) = true) ↔ run gates env output = true := by
  constructor
  · rintro ⟨model, agree, clauses⟩
    obtain ⟨equations, accepted⟩ := (assertOutput_correct gates output model).mp clauses
    have same := valid.model_agree env model equations agree output bound
    rw [← same]
    exact accepted
  · intro accepted
    obtain ⟨preserved, equations⟩ := valid.run_correct env
    exact ⟨run gates env, preserved, (assertOutput_correct gates output _).mpr ⟨equations, accepted⟩⟩

/-- Checked fresh programs admit asserted models exactly when execution accepts. -/
theorem checkProgram_asserted_iff (next : Nat) (gates : List Gate)
    (checked : checkProgram next gates = true) (env : Assignment) (output : Nat)
    (bound : output < next + gates.length) :
    (∃ model : Assignment, (∀ id, id < next → model id = env id) ∧
      CNF.eval model (assertOutput gates output) = true) ↔ run gates env output = true :=
  ((checkProgram_iff next gates).mp checked).asserted_iff env output bound

/-- The adder's input words and incoming carry occupy the original input range. -/
def Adder.checkInputs (adder : Adder) (next : Nat) : Bool :=
  decide (adder.inputCarry < next) &&
    adder.cells.all (fun cell => decide (cell.left < next) && decide (cell.right < next))

theorem Adder.checkInputs_iff (adder : Adder) (next : Nat) :
    adder.checkInputs next = true ↔ adder.inputCarry < next ∧
      ∀ cell ∈ adder.cells, cell.left < next ∧ cell.right < next := by
  simp [Adder.checkInputs]

private theorem fold_value_congr (cells : List AdderCell) (wire : AdderCell → Nat)
    (left right : Assignment) (agree : ∀ cell ∈ cells, left (wire cell) = right (wire cell)) :
    cells.foldr (fun cell rest => (left (wire cell)).toNat + 2 * rest) 0 =
      cells.foldr (fun cell rest => (right (wire cell)).toNat + 2 * rest) 0 := by
  induction cells with
  | nil => rfl
  | cons cell rest ih =>
    simp only [List.foldr]
    rw [agree cell (List.Mem.head _), ih (fun item member => agree item (List.Mem.tail _ member))]

/-- Full numeric addition with outgoing carry under constructed execution. -/
theorem Adder.run_numeric (adder : Adder) (next : Nat)
    (checked : checkProgram next adder.gates = true)
    (inputCheck : adder.checkInputs next = true) (env : Assignment) :
    adder.leftValue env + adder.rightValue env + (env adder.inputCarry).toNat =
      adder.sumValue (run adder.gates env) +
        2 ^ adder.width * (run adder.gates env adder.outputCarry).toNat := by
  obtain ⟨model, preserved⟩ := checkProgram_model next adder.gates checked env
  obtain ⟨carryBound, inputBounds⟩ := (adder.checkInputs_iff next).mp inputCheck
  have leftSame : adder.leftValue (run adder.gates env) = adder.leftValue env := by
    apply fold_value_congr
    intro cell member
    exact preserved cell.left (inputBounds cell member).1
  have rightSame : adder.rightValue (run adder.gates env) = adder.rightValue env := by
    apply fold_value_congr
    intro cell member
    exact preserved cell.right (inputBounds cell member).2
  have carrySame := preserved adder.inputCarry carryBound
  simpa only [leftSame, rightSame, carrySame] using
    adder.encode_numeric (run adder.gates env) model


/-- Execution of a checked fresh adder computes native core addition for every
input assignment. The model is constructed, never assumed. -/
theorem Adder.run_native_add (adder : Adder) (next : Nat)
    (checked : checkProgram next adder.gates = true)
    (inputCheck : adder.checkInputs next = true) (env : Assignment) :
    (BitVec.ofNat adder.width (adder.leftValue env) +
      BitVec.ofNat adder.width (adder.rightValue env)) +
      BitVec.ofNat adder.width (env adder.inputCarry).toNat =
      BitVec.ofNat adder.width (adder.sumValue (run adder.gates env)) := by
  obtain ⟨model, preserved⟩ := checkProgram_model next adder.gates checked env
  obtain ⟨carryBound, inputBounds⟩ := (adder.checkInputs_iff next).mp inputCheck
  have leftSame : adder.leftValue (run adder.gates env) = adder.leftValue env := by
    apply fold_value_congr
    intro cell member
    exact preserved cell.left (inputBounds cell member).1
  have rightSame : adder.rightValue (run adder.gates env) = adder.rightValue env := by
    apply fold_value_congr
    intro cell member
    exact preserved cell.right (inputBounds cell member).2
  have carrySame := preserved adder.inputCarry carryBound
  simpa only [leftSame, rightSame, carrySame] using
    adder.encode_native_add (run adder.gates env) model

/-- The checked circuit's generated sum implements the actual typed target's
addition node when its input wires encode the operands and carry-in is zero. -/
theorem Adder.run_target_add (adder : Adder) (next bits : Nat)
    (width : adder.width = bits)
    (checked : checkProgram next adder.gates = true)
    (inputCheck : adder.checkInputs next = true) (env : Assignment)
    (left right : TrustIrExpr.SMTTerm (.bv bits)) (target : SMTEnv)
    (leftInput : BitVec.ofNat bits (adder.leftValue env) = left.eval target)
    (rightInput : BitVec.ofNat bits (adder.rightValue env) = right.eval target)
    (carryZero : env adder.inputCarry = false) :
    BitVec.ofNat bits (adder.sumValue (run adder.gates env)) =
      (TrustIrExpr.SMTTerm.binary (.bvAdd bits) left right).eval target := by
  have result := adder.run_native_add next checked inputCheck env
  rw [width, leftInput, rightInput, carryZero] at result
  simpa [TrustIrExpr.SMTTerm.eval, TrustIrExpr.SMTBinary.eval] using result.symm

/-- Construct a ripple adder with two fresh outputs per input pair. Core list
folds keep allocation total without custom partial runtime workers. -/
def buildAdder (inputs : List (Nat × Nat)) (next carry : Nat) : Adder :=
  inputs.foldr (fun pair rest next carry =>
    Adder.cons pair.1 pair.2 next carry (rest (next + 2) (next + 1)))
    (fun _ carry => Adder.nil carry) next carry

theorem buildAdder_inputCarry (inputs : List (Nat × Nat)) (next carry : Nat) :
    (buildAdder inputs next carry).inputCarry = carry := by
  cases inputs <;> rfl

theorem buildAdder_width (inputs : List (Nat × Nat)) (next carry : Nat) :
    (buildAdder inputs next carry).width = inputs.length := by
  induction inputs generalizing next carry with
  | nil => rfl
  | cons _pair tail ih =>
    change (buildAdder tail (next + 2) (next + 1)).width + 1 = tail.length + 1
    rw [ih]

/-- The builder's actual allocated outputs are fresh and every input is earlier. -/
theorem buildAdder_valid (inputs : List (Nat × Nat)) (next carry : Nat)
    (bounds : ∀ pair ∈ inputs, pair.1 < next ∧ pair.2 < next)
    (carryBound : carry < next) : Valid next (buildAdder inputs next carry).gates := by
  induction inputs generalizing next carry with
  | nil => exact .nil next
  | cons pair tail ih =>
    have pairBounds := bounds pair (List.Mem.head _)
    have tailValid : Valid (next + 2) (buildAdder tail (next + 2) (next + 1)).gates := by
      apply ih
      · intro item member
        have before := bounds item (List.Mem.tail _ member)
        constructor <;> omega
      · omega
    change Valid next (.xor3 next pair.1 pair.2 carry ::
      .fullAdderCarry (buildAdder tail (next + 2) (next + 1)).inputCarry pair.1 pair.2 carry ::
        (buildAdder tail (next + 2) (next + 1)).gates)
    rw [buildAdder_inputCarry]
    apply Valid.cons (next := next) (gate := .xor3 next pair.1 pair.2 carry) rfl
    · simpa [Gate.inputs] using ⟨pairBounds.1, pairBounds.2, carryBound⟩
    · apply Valid.cons (next := next + 1) (gate := .fullAdderCarry (next + 1) pair.1 pair.2 carry) rfl
      · have leftBound : pair.1 < next + 1 := by omega
        have rightBound : pair.2 < next + 1 := by omega
        have oldCarryBound : carry < next + 1 := by omega
        simpa [Gate.inputs] using ⟨leftBound, rightBound, oldCarryBound⟩
      · simpa [Nat.add_assoc] using tailValid

private theorem buildAdder_cell_bounds (inputs : List (Nat × Nat)) (next carry limit : Nat)
    (bounds : ∀ pair ∈ inputs, pair.1 < limit ∧ pair.2 < limit) :
    ∀ cell ∈ (buildAdder inputs next carry).cells, cell.left < limit ∧ cell.right < limit := by
  induction inputs generalizing next carry with
  | nil => intro cell member; cases member
  | cons pair tail ih =>
    intro cell member
    change cell ∈ AdderCell.mk pair.1 pair.2 next
      (buildAdder tail (next + 2) (next + 1)).inputCarry ::
      (buildAdder tail (next + 2) (next + 1)).cells at member
    cases member with
    | head => exact bounds pair (List.Mem.head _)
    | tail _ member =>
      exact ih (next + 2) (next + 1) (fun item mem => bounds item (List.Mem.tail _ mem)) cell member

/-- No per-instance checked-layout premise is needed for canonical construction. -/
theorem buildAdder_checks (inputs : List (Nat × Nat)) (next carry : Nat)
    (bounds : ∀ pair ∈ inputs, pair.1 < next ∧ pair.2 < next)
    (carryBound : carry < next) :
    checkProgram next (buildAdder inputs next carry).gates = true ∧
      (buildAdder inputs next carry).checkInputs next = true := by
  refine ⟨(checkProgram_iff _ _).mpr (buildAdder_valid inputs next carry bounds carryBound), ?_⟩
  apply (Adder.checkInputs_iff _ _).mpr
  exact ⟨by simpa [buildAdder_inputCarry] using carryBound,
    buildAdder_cell_bounds inputs next carry next bounds⟩

/-- A constructed fresh ripple graph computes native addition for all inputs
and widths, with its CNF model supplied by actual execution. -/
theorem buildAdder_run_native_add (inputs : List (Nat × Nat)) (next carry : Nat)
    (bounds : ∀ pair ∈ inputs, pair.1 < next ∧ pair.2 < next)
    (carryBound : carry < next) (env : Assignment) :
    let adder := buildAdder inputs next carry
    (BitVec.ofNat adder.width (adder.leftValue env) +
      BitVec.ofNat adder.width (adder.rightValue env)) +
      BitVec.ofNat adder.width (env carry).toNat =
      BitVec.ofNat adder.width (adder.sumValue (run adder.gates env)) := by
  obtain ⟨checked, inputCheck⟩ := buildAdder_checks inputs next carry bounds carryBound
  simpa only [buildAdder_inputCarry] using
    (buildAdder inputs next carry).run_native_add next checked inputCheck env

end TrustIr.AYGateCNF

#trustIrAxiomsExact TrustIr.AYGateCNF.Gate.eval_congr == [Quot.sound, propext]

#trustIrAxiomsExact TrustIr.AYGateCNF.checkProgram_iff == [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.AYGateCNF.Valid.run_correct == [Quot.sound, propext, Classical.choice] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.AYGateCNF.checkProgram_model == [Quot.sound, propext, Classical.choice] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.AYGateCNF.Valid.model_agree == [Quot.sound, propext, Classical.choice] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.AYGateCNF.Valid.asserted_iff == [propext, Quot.sound, Classical.choice] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.AYGateCNF.checkProgram_asserted_iff == [propext, Quot.sound, Classical.choice] modern [propext, Quot.sound]

#trustIrAxiomsExact TrustIr.AYGateCNF.Adder.checkInputs_iff == [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.AYGateCNF.Adder.run_native_add == [Quot.sound, propext, Classical.choice] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.AYGateCNF.Adder.run_target_add == [propext, Quot.sound, Classical.choice] modern [propext, Quot.sound]

/-- info: 'TrustIr.AYGateCNF.buildAdder_inputCarry' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.AYGateCNF.buildAdder_inputCarry

/-- info: 'TrustIr.AYGateCNF.buildAdder_width' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.AYGateCNF.buildAdder_width

#trustIrAxiomsPinned TrustIr.AYGateCNF.buildAdder_valid == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.AYGateCNF.buildAdder_checks == [propext, Quot.sound, Classical.choice] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.AYGateCNF.buildAdder_run_native_add == [propext, Quot.sound, Classical.choice] modern [propext, Quot.sound]

#trustIrAxiomsExact TrustIr.AYGateCNF.checkProgram_eq_spec == [propext]

#trustIrAxiomsPinned TrustIr.AYGateCNF.Adder.run_numeric == [Quot.sound, propext, Classical.choice] modern [propext, Quot.sound]

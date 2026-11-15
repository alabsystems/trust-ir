-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import TrustIr.Proofs.AYZeroCountInstruction
import TrustIr.Proofs.AYPopulationGates
import TrustIr.Proofs.AYWordIte

namespace TrustIr.AYGateCNF

/-- Retain the previous scan once, allocate the literal branch, then select
its result using an ORIGINAL input bit. No equality gate is needed for bv1. -/
def WordCode.chooseConstant {bits : Nat} (prior : WordCode bits) (value : Nat) (cond next : Nat) : WordCode bits :=
  let literal := WordCode.constant (BitVec.ofNat bits value) (next+prior.gates.length)
  let both := WordCode.append prior literal
  WordCode.append both (WordCode.ite cond literal.bits prior.bits (next+both.gates.length))

theorem WordCode.chooseConstant_check {bits : Nat} (prior : WordCode bits) (value : Nat) (cond next : Nat)
    (checked : prior.check next = true) (input : cond < next) :
    (prior.chooseConstant value cond next).check next = true := by
  let literal := WordCode.constant (BitVec.ofNat bits value) (next+prior.gates.length)
  have lc : literal.check (next+prior.gates.length) = true := WordCode.constant_check _ _
  have both := WordCode.append_check prior literal next checked lc
  obtain ⟨pb,lb⟩ := WordCode.append_operand_bounds next prior literal checked lc
  apply WordCode.append_check _ _ next both
  apply WordCode.ite_check _ _ _ _ (by dsimp [WordCode.append]; omega) lb pb

theorem WordCode.chooseConstant_value {bits : Nat} (prior : WordCode bits) (value : Nat) (cond next : Nat)
    (checked : prior.check next = true) (input : cond < next) (env : Assignment) :
    (prior.chooseConstant value cond next).value env =
      if env cond then BitVec.ofNat bits value else prior.value env := by
  let literal := WordCode.constant (BitVec.ofNat bits value) (next+prior.gates.length)
  let both := WordCode.append prior literal
  have lc : literal.check (next+prior.gates.length) = true := WordCode.constant_check _ _
  have bc : both.check next = true := WordCode.append_check prior literal next checked lc
  obtain ⟨pb,lb⟩ := WordCode.append_operand_bounds next prior literal checked lc
  have condition := (((WordCode.check_iff _ _).mp bc).1.run_correct env).1 cond input
  have previous : wordValue prior.bits (run both.gates env) = prior.value env := by
    apply wordValue_congr
    intro i
    exact ((WordCode.check_iff _ _).mp lc).1.append_preserves env _
      (((WordCode.check_iff _ _).mp checked).2 i)
  have constant : wordValue literal.bits (run both.gates env) = BitVec.ofNat bits value := by
    change wordValue literal.bits (run (prior.gates++literal.gates) env) = _
    rw [run_append]
    exact WordCode.constant_value _ _ _
  change (WordCode.append both (WordCode.ite cond literal.bits prior.bits (next+both.gates.length))).value env = _
  rw [WordCode.append_value, WordCode.ite_value _ _ _ _ (by dsimp [both,WordCode.append]; omega) lb pb,
    condition, constant, previous]

theorem WordCode.chooseConstant_length {bits : Nat} (prior : WordCode bits) (value : Nat) (cond next : Nat) :
    (prior.chooseConstant value cond next).gates.length = prior.gates.length + 4*bits+1 := by
  simp only [WordCode.chooseConstant, WordCode.append, List.length_append, WordCode.ite_length,
    WordCode.constant, tabulate_length]
  omega

end TrustIr.AYGateCNF

namespace TrustIr.TrustIrExpr
open AYGateCNF

/-- The exact source scan order with counts represented at their proven
minimal shared width. Recursion is on actual iterations, not chosen fuel. -/
def ZeroCountDirection.scanCode {width : Nat} (direction : ZeroCountDirection) (input : Fin width → Nat) :
    (count : Nat) → count ≤ width → Nat → WordCode (populationBits width) :=
  Nat.rec (motive := fun count => count ≤ width → Nat → WordCode (populationBits width))
    (fun _ next => WordCode.constant (BitVec.ofNat (populationBits width) width) next)
    (fun i previous bound next =>
      let prior := previous (by omega) next
      let index : Fin width := ⟨direction.index width i, direction.index_lt width i (by omega)⟩
      prior.chooseConstant (width-1-i) (input index) next)

theorem ZeroCountDirection.scanCode_check {width : Nat} (direction : ZeroCountDirection) (input : Fin width → Nat)
    (count : Nat) (bound : count ≤ width) (next : Nat) (inputs : ∀ i, input i < next) :
    (direction.scanCode input count bound next).check next = true := by
  induction count with
  | zero => exact WordCode.constant_check _ _
  | succ i ih => exact WordCode.chooseConstant_check _ _ _ _ (ih (by omega)) (inputs _)

theorem ZeroCountDirection.scanCode_toNat {width : Nat} (direction : ZeroCountDirection) (input : Fin width → Nat)
    (count : Nat) (bound : count ≤ width) (next : Nat) (inputs : ∀ i, input i < next) (env : Assignment) :
    ((direction.scanCode input count bound next).value env).toNat = zeroScan direction width (wordValue input env).toNat count := by
  induction count with
  | zero =>
    rw [show direction.scanCode input 0 bound next = WordCode.constant (BitVec.ofNat (populationBits width) width) next from rfl,
      WordCode.constant_value, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (populationBits_capacity width)]
    rfl
  | succ i ih =>
    let index : Fin width := ⟨direction.index width i,direction.index_lt width i (by omega)⟩
    have bit : env (input index) = ((wordValue input env).toNat/2^(direction.index width i)%2 == 1) := by
      rw [← wordValue_bit input env index]
      trustIrCompilerProof {
        simp [BitVec.getLsb, Nat.testBit_to_div_mod]
        apply Bool.eq_iff_iff.mpr
        simp
      } {
        simp only [BitVec.getLsbD, Nat.testBit_eq_decide_div_mod_eq]
        apply Bool.eq_iff_iff.mpr
        simp [index]
      }
    change (BitVec.toNat ((direction.scanCode input i (by omega) next).chooseConstant (width-1-i) (input index) next |>.value env)) = _
    rw [WordCode.chooseConstant_value _ _ _ _ (direction.scanCode_check input i (by omega) next inputs) (inputs index),bit]
    change (BitVec.toNat (if (wordValue input env).toNat/2^(direction.index width i)%2 == 1 then _ else _)) =
      (if (wordValue input env).toNat/2^(direction.index width i)%2 == 1 then width-1-i else zeroScan direction width (wordValue input env).toNat i)
    split
    · exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (by omega) (populationBits_capacity width))
    · exact ih (by omega)

theorem ZeroCountDirection.scanCode_length {width : Nat} (direction : ZeroCountDirection) (input : Fin width → Nat)
    (count : Nat) (bound : count ≤ width) (next : Nat) :
    (direction.scanCode input count bound next).gates.length = populationBits width + count*(4*populationBits width+1) := by
  induction count with
  | zero =>
    change (WordCode.constant _ next).gates.length = _
    simp only [WordCode.constant, tabulate_length, Nat.zero_mul, Nat.add_zero]
  | succ i ih =>
    change ((direction.scanCode input i (by omega) next).chooseConstant _ _ next).gates.length = _
    rw [WordCode.chooseConstant_length, ih, Nat.succ_mul i (4*populationBits width+1)]
    omega

end TrustIr.TrustIrExpr

namespace TrustIr
open TrustIrExpr AYGateCNF

def ZeroCountSubject.code {model : ByteModel} (subject : ZeroCountSubject model)
    (base next : Nat) : WordCode subject.width :=
  let counted := subject.direction.scanCode (fun i : Fin subject.width => base+i.val)
    subject.width (Nat.le_refl _) next
  counted.populationExtend subject.width next (populationBits_le _ subject.positive)

theorem ZeroCountSubject.code_check {model : ByteModel} (subject : ZeroCountSubject model)
    (base next : Nat) (bound : base+subject.width ≤ next) : (subject.code base next).check next = true := by
  unfold ZeroCountSubject.code
  apply WordCode.populationExtend_check _ _ _ (populationBits_le _ subject.positive)
  apply ZeroCountDirection.scanCode_check
  intro i; have before := i.isLt; omega

theorem ZeroCountSubject.code_toNat {model : ByteModel} (subject : ZeroCountSubject model)
    (base next : Nat) (bound : base+subject.width ≤ next) (word : BitVec subject.width) (env : Assignment) :
    ((subject.code base next).value (bindWord base word env)).toNat = subject.direction.number word.toNat subject.width := by
  have inputs : ∀ i : Fin subject.width, base+i.val < next := by intro i; have before := i.isLt; omega
  unfold ZeroCountSubject.code
  rw [WordCode.populationExtend_toNat _ _ _ _ (ZeroCountDirection.scanCode_check _ _ _ _ _ inputs),
    ZeroCountDirection.scanCode_toNat _ _ _ _ _ inputs, zeroScan_complete]
  have same := WordCode.input_value subject.width base word env
  change wordValue (fun i : Fin subject.width => base+i.val) (bindWord base word env) = word at same
  rw [same]

/-- Refuse an unavailable original input slice before constructing any gate
program. The returned value is from actual checked execution, not a count oracle. -/
def ZeroCountSubject.checkedCode {model : ByteModel} (subject : ZeroCountSubject model)
    (base next : Nat) (word : BitVec subject.width) (env : Assignment) : Option (BitVec subject.width) :=
  if base+subject.width ≤ next then (subject.code base next).checkedEval next (bindWord base word env)
  else none

theorem ZeroCountSubject.checkedCode_eq_some {model : ByteModel} (subject : ZeroCountSubject model)
    (base next : Nat) (word : BitVec subject.width) (env : Assignment) (result : BitVec subject.width) :
    subject.checkedCode base next word env = some result ↔
      base+subject.width ≤ next ∧ (subject.code base next).value (bindWord base word env) = result := by
  by_cases bound : base+subject.width ≤ next
  · simp [ZeroCountSubject.checkedCode, bound, WordCode.checkedEval_eq_some, subject.code_check base next bound]
  · simp [ZeroCountSubject.checkedCode, bound]

theorem ZeroCountSubject.checkedCode_number {model : ByteModel} (subject : ZeroCountSubject model)
    (base next : Nat) (word : BitVec subject.width) (env : Assignment) (result : BitVec subject.width)
    (executed : subject.checkedCode base next word env = some result) :
    result.toNat = subject.direction.number word.toNat subject.width := by
  have actual := (subject.checkedCode_eq_some base next word env result).mp executed
  rw [← actual.2]
  exact subject.code_toNat base next actual.1 word env

/-- Actual checked gates and the actual source-indexed returned request agree.
The only symbolic premise maps their original input, not their output. -/
theorem ZeroCountSite.gate_request_value {model : ByteModel} {original : Inst}
    (site : ZeroCountSite model original) (arg : SMTCheckedTerm (.bv site.subject.width))
    (request : SMTTypedRequest (.bv site.subject.width)) (built : site.toRequest arg = .ok request)
    (operand : Int) (target : SMTEnv) (source : arg.term.eval target = BitVec.ofInt site.subject.width operand)
    (base next : Nat) (env : Assignment) (result : BitVec site.subject.width)
    (executed : site.subject.checkedCode base next (BitVec.ofInt site.subject.width operand) env = some result) :
    result = request.target.eval target := by
  apply BitVec.eq_of_toNat_eq
  rw [site.subject.checkedCode_number base next _ env result executed,
    (site.subject.request_target arg request built target).2, source]

theorem ZeroCountSite.gate_outcome (ctx : EvalContext) (original : Inst)
    (site : ZeroCountSite ctx.byteModel original) (base next : Nat) (env : Assignment)
    (state : MachineState) (operand : Int) (result : BitVec site.subject.width)
    (lookup : state.lookupValue site.operand = some (.int site.subject.width operand))
    (executed : site.subject.checkedCode base next (BitVec.ofInt site.subject.width operand) env = some result) :
    Sem.run (stepInstWithContext ctx original) state =
      bindEncodedValue state (.ok (.int site.subject.width (Int.ofNat result.toNat))) := by
  have computed : semIntUnOp site.subject.direction.irOp site.subject.width operand = .ok (Int.ofNat result.toNat) := by
    rw [site.subject.checkedCode_number base next _ env result executed]
    cases direction : site.subject.direction <;> simp [direction, ZeroCountDirection.irOp, ZeroCountDirection.number, semIntUnOp, BitVec.toNat_ofInt, Int.natCast_pow, Int.add_emod, Int.emod_emod]
  have identity := congrArg (fun inst => Sem.run (stepInstWithContext ctx inst) state) site.origin
  apply identity.trans
  exact int_unop_step_result site.subject.direction.irOp site.subject.ty site.subject.width site.operand state ctx.byteModel operand _ lookup computed

end TrustIr

-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import TrustIr.Proofs.AYPopulationInstruction

namespace TrustIr.AYGateCNF
open TrustIrExpr

/-- Extend a computed subtotal once, retaining its existing gates and sharing
one zero wire. Equal widths retain the code verbatim. -/
def WordCode.populationExtend {bits : Nat} (target : Nat) (code : WordCode bits)
    (next : Nat) (wide : bits ≤ target) : WordCode target :=
  if same : bits = target then code.castWidth same
  else WordCode.append code (WordCode.resize target code.bits (next+code.gates.length))

theorem WordCode.populationExtend_check {bits : Nat} (target : Nat) (code : WordCode bits)
    (next : Nat) (wide : bits ≤ target) (checked : code.check next = true) :
    (code.populationExtend target next wide).check next = true := by
  unfold WordCode.populationExtend
  split
  · rw [WordCode.castWidth_check]; exact checked
  · exact WordCode.append_check code _ next checked
      (WordCode.resize_check _ _ _ ((WordCode.check_iff _ _).mp checked).2)

theorem WordCode.populationExtend_toNat {bits : Nat} (target : Nat) (code : WordCode bits)
    (next : Nat) (wide : bits ≤ target) (checked : code.check next = true) (env : Assignment) :
    ((code.populationExtend target next wide).value env).toNat = (code.value env).toNat := by
  unfold WordCode.populationExtend
  split
  · rw [WordCode.castWidth_value, BitVec.toNat_cast]
  · rw [WordCode.append_value, WordCode.resize_value _ _ _ ((WordCode.check_iff _ _).mp checked).2,
      trustIrWidthLemma BitVec.toNat_zeroExtend BitVec.toNat_setWidth]
    apply Nat.mod_eq_of_lt
    exact Nat.lt_of_lt_of_le (code.value env).isLt ((trustIrWidthLemma Nat.pow_le_pow_of_le_right Nat.pow_le_pow_right) (by decide) wide)

/-- A leaf is an original source bit, without allocation or fake constants. -/
def WordCode.populationLeaf {source : Nat} (input : Fin source → Nat) (start : Nat)
    (bound : start+1 ≤ source) : WordCode 1 :=
  WordCode.rewire input (fun i => ⟨start+i.val, by have h := i.isLt; omega⟩)

theorem WordCode.populationLeaf_check {source : Nat} (input : Fin source → Nat) (start : Nat)
    (bound : start+1 ≤ source) (next : Nat) (inputs : ∀ i, input i < next) :
    (WordCode.populationLeaf input start bound).check next = true :=
  WordCode.rewire_check _ _ _ inputs

theorem WordCode.populationLeaf_value {source : Nat} (input : Fin source → Nat) (start : Nat)
    (bound : start+1 ≤ source) (env : Assignment) :
    (WordCode.populationLeaf input start bound).value env = (wordValue input env).extractLsb' start 1 := by
  apply trustIrWordExt
  intro i
  rw [WordCode.populationLeaf, WordCode.rewire_bit]
  have position : start+i.val < source := by have h := i.isLt; omega
  rw [← wordValue_bit input env ⟨start+i.val,position⟩]
  trustIrCompilerProof {
    simp only [BitVec.extractLsb', BitVec.getLsb, BitVec.toNat_ofNat, Nat.testBit_mod_two_pow,
      Nat.testBit_shiftRight, i.isLt, Bool.true_and]
  } {
    simp only [BitVec.extractLsb', BitVec.getLsbD, BitVec.toNat_ofNat, Nat.testBit_mod_two_pow,
      Nat.testBit_shiftRight, i.isLt, Bool.true_and]
  }
  rfl

end TrustIr.AYGateCNF

namespace TrustIr.TrustIrExpr
open AYGateCNF

/-- Compile the same intrinsic balanced plan as the target encoder. A child
program is allocated only once; the right child starts after the complete left
subtotal, and the parent adder follows both children. -/
def PopulationPlan.code {length : Nat} (plan : PopulationPlan length) {source : Nat}
    (input : Fin source → Nat) (start : Nat) (bound : start+length ≤ source) (next : Nat) :
    WordCode (populationBits length) :=
  match plan with
  | .bit => (WordCode.populationLeaf input start bound).castWidth (by decide)
  | .split (length := length) large leftPlan rightPlan =>
    let left := leftPlan.code input start (by have h := Nat.div_le_self length 2; omega) next
    let leftWide := left.populationExtend (populationBits length) next
      (populationBits_mono _ _ (by omega) (Nat.div_le_self _ _))
    let afterLeft := next+leftWide.gates.length
    let right := rightPlan.code input (start+length/2) (by have h := Nat.div_le_self length 2; omega) afterLeft
    let rightWide := right.populationExtend (populationBits length) afterLeft
      (populationBits_mono _ _ (by omega) (Nat.sub_le _ _))
    WordCode.composeAdd next leftWide rightWide

theorem PopulationPlan.code_check {length : Nat} (plan : PopulationPlan length) {source : Nat}
    (input : Fin source → Nat) (start : Nat) (bound : start+length ≤ source) (next : Nat)
    (inputs : ∀ i, input i < next) : (plan.code input start bound next).check next = true := by
  induction plan generalizing start next with
  | bit =>
    rw [PopulationPlan.code, WordCode.castWidth_check]
    exact WordCode.populationLeaf_check input start bound next inputs
  | @split length large left right leftIH rightIH =>
    unfold PopulationPlan.code
    apply WordCode.composeAdd_check
    · apply WordCode.populationExtend_check
      exact leftIH _ _ next inputs
    · apply WordCode.populationExtend_check
      apply rightIH
      intro i; have before := inputs i; omega

theorem PopulationPlan.code_toNat {length : Nat} (plan : PopulationPlan length) {source : Nat}
    (input : Fin source → Nat) (start : Nat) (bound : start+length ≤ source) (next : Nat)
    (inputs : ∀ i, input i < next) (env : Assignment) :
    ((plan.code input start bound next).value env).toNat = populationSlice (wordValue input env).toNat start length := by
  induction plan generalizing start next env with
  | bit =>
    rw [PopulationPlan.code, WordCode.castWidth_value, BitVec.toNat_cast, WordCode.populationLeaf_value]
    simp [BitVec.extractLsb_toNat, Nat.shiftRight_eq_div_pow, populationSlice_succ]
  | @split length large left right leftIH rightIH =>
    let l := left.code input start (by have h := Nat.div_le_self length 2; omega) next
    let lw := l.populationExtend (populationBits length) next
      (populationBits_mono _ _ (by omega) (Nat.div_le_self _ _))
    let afterLeft := next+lw.gates.length
    let r := right.code input (start+length/2) (by have h := Nat.div_le_self length 2; omega) afterLeft
    have lc : l.check next = true := left.code_check input _ _ next inputs
    have lwc : lw.check next = true := WordCode.populationExtend_check _ _ _ _ lc
    have later : ∀ i, input i < afterLeft := by intro i; have before := inputs i; dsimp [afterLeft]; omega
    have rc : r.check afterLeft = true := right.code_check input _ _ afterLeft later
    have same : wordValue input (run lw.gates env) = wordValue input env := by
      apply wordValue_congr
      intro i
      exact (((WordCode.check_iff _ _).mp lwc).1.run_correct env).1 _ (inputs i)
    change ((WordCode.composeAdd next lw (r.populationExtend (populationBits length) afterLeft _)).value env).toNat = _
    rw [WordCode.composeAdd_value _ _ _ lwc (WordCode.populationExtend_check _ _ _ _ rc),
      BitVec.toNat_add, WordCode.populationExtend_toNat _ l _ _ lc,
      WordCode.populationExtend_toNat _ r _ _ rc, leftIH _ _ next inputs,
      rightIH _ _ afterLeft later, same]
    have halves : length/2+(length-length/2) = length := by have h := Nat.div_le_self length 2; omega
    have sum := populationSlice_append (wordValue input env).toNat start (length/2) (length-length/2)
    rw [halves] at sum
    rw [← sum]
    apply Nat.mod_eq_of_lt
    exact Nat.lt_of_le_of_lt (populationSlice_bound _ _ _) (populationBits_capacity length)

end TrustIr.TrustIrExpr

namespace TrustIr
open TrustIrExpr AYGateCNF

def PopulationSubject.code {model : ByteModel} (subject : PopulationSubject model)
    (base next : Nat) : WordCode subject.width :=
  let counted := (PopulationPlan.balanced subject.width subject.positive).code
    (fun i : Fin subject.width => base+i.val) 0 (by omega) next
  counted.populationExtend subject.width next (populationBits_le _ subject.positive)

theorem PopulationSubject.code_check {model : ByteModel} (subject : PopulationSubject model)
    (base next : Nat) (bound : base+subject.width ≤ next) : (subject.code base next).check next = true := by
  unfold PopulationSubject.code
  apply WordCode.populationExtend_check _ _ _ (populationBits_le _ subject.positive)
  apply PopulationPlan.code_check
  intro i; have before := i.isLt; omega

theorem PopulationSubject.code_toNat {model : ByteModel} (subject : PopulationSubject model)
    (base next : Nat) (bound : base+subject.width ≤ next) (word : BitVec subject.width) (env : Assignment) :
    ((subject.code base next).value (bindWord base word env)).toNat = popCountWidth word.toNat subject.width := by
  have inputs : ∀ i : Fin subject.width, base+i.val < next := by intro i; have before := i.isLt; omega
  unfold PopulationSubject.code
  rw [WordCode.populationExtend_toNat _ _ _ _ (PopulationPlan.code_check _ _ _ _ _ inputs),
    PopulationPlan.code_toNat _ _ _ _ _ inputs, populationSlice_semantics]
  have same := WordCode.input_value subject.width base word env
  change wordValue (fun i : Fin subject.width => base+i.val) (bindWord base word env) = word at same
  rw [same]

/-- Refuse an unavailable original input slice before constructing any gate
program. The returned value is from actual checked execution, not a count oracle. -/
def PopulationSubject.checkedCode {model : ByteModel} (subject : PopulationSubject model)
    (base next : Nat) (word : BitVec subject.width) (env : Assignment) : Option (BitVec subject.width) :=
  if base+subject.width ≤ next then (subject.code base next).checkedEval next (bindWord base word env)
  else none

theorem PopulationSubject.checkedCode_eq_some {model : ByteModel} (subject : PopulationSubject model)
    (base next : Nat) (word : BitVec subject.width) (env : Assignment) (result : BitVec subject.width) :
    subject.checkedCode base next word env = some result ↔
      base+subject.width ≤ next ∧ (subject.code base next).value (bindWord base word env) = result := by
  by_cases bound : base+subject.width ≤ next
  · simp [PopulationSubject.checkedCode, bound, WordCode.checkedEval_eq_some, subject.code_check base next bound]
  · simp [PopulationSubject.checkedCode, bound]

theorem PopulationSubject.checkedCode_number {model : ByteModel} (subject : PopulationSubject model)
    (base next : Nat) (word : BitVec subject.width) (env : Assignment) (result : BitVec subject.width)
    (executed : subject.checkedCode base next word env = some result) :
    result.toNat = popCountWidth word.toNat subject.width := by
  have actual := (subject.checkedCode_eq_some base next word env result).mp executed
  rw [← actual.2]
  exact subject.code_toNat base next actual.1 word env

/-- Actual checked gates and the actual source-indexed returned request agree.
The only symbolic premise maps their original input, not their output. -/
theorem PopulationSite.gate_request_value {model : ByteModel} {original : Inst}
    (site : PopulationSite model original) (arg : SMTCheckedTerm (.bv site.subject.width))
    (request : SMTTypedRequest (.bv site.subject.width)) (built : site.toRequest arg = .ok request)
    (operand : Int) (target : SMTEnv) (source : arg.term.eval target = BitVec.ofInt site.subject.width operand)
    (base next : Nat) (env : Assignment) (result : BitVec site.subject.width)
    (executed : site.subject.checkedCode base next (BitVec.ofInt site.subject.width operand) env = some result) :
    result = request.target.eval target := by
  apply BitVec.eq_of_toNat_eq
  rw [site.subject.checkedCode_number base next _ env result executed,
    (site.subject.request_target arg request built target).2, source]

theorem PopulationSite.gate_outcome (ctx : EvalContext) (original : Inst)
    (site : PopulationSite ctx.byteModel original) (base next : Nat) (env : Assignment)
    (state : MachineState) (operand : Int) (result : BitVec site.subject.width)
    (lookup : state.lookupValue site.operand = some (.int site.subject.width operand))
    (executed : site.subject.checkedCode base next (BitVec.ofInt site.subject.width operand) env = some result) :
    Sem.run (stepInstWithContext ctx original) state =
      bindEncodedValue state (.ok (.int site.subject.width (Int.ofNat result.toNat))) := by
  have computed : semIntUnOp .CtPop site.subject.width operand = .ok (Int.ofNat result.toNat) := by
    rw [site.subject.checkedCode_number base next _ env result executed]
    simp [semIntUnOp, BitVec.toNat_ofInt, Int.natCast_pow, Int.add_emod, Int.emod_emod]
  have identity := congrArg (fun inst => Sem.run (stepInstWithContext ctx inst) state) site.origin
  apply identity.trans
  exact int_unop_step_result .CtPop site.subject.ty site.subject.width site.operand state ctx.byteModel operand _ lookup computed

end TrustIr

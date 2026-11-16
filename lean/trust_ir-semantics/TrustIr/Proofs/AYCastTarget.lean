-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import TrustIr.Proofs.AYSourceInput
import TrustIr.Proofs.AYTargetInstruction

/-- Select the actual least-significant-bit API without restricting the word. -/
macro "trustIrCastBit" : term => do
  if Lean.versionString == "4.8.0" then `(BitVec.getLsb)
  else if Lean.versionString == "4.30.0-rc2" then `(BitVec.getLsbD)
  else Lean.Macro.throwError "unsupported compiler for cast bit access"

namespace TrustIr
open TrustIrExpr

theorem cast_word_residue (width : Nat) (value : Int) :
    Int.ofNat (BitVec.ofInt width value).toNat = truncateUnsigned value width := by
  trustIrCompilerProof {
    change Int.ofNat (value % ((2^width : Nat) : Int)).toNat = value % (2 : Int)^width
    rw [Int.natCast_pow]
    have positive := Int.ofNat_pos.mpr (Nat.two_pow_pos width)
    have nonzero : (2 : Int)^width ≠ 0 := by
      have cast : ((2^width : Nat) : Int) = (2 : Int)^width := Int.natCast_pow 2 width
      rw [cast] at positive
      omega
    exact Int.toNat_of_nonneg (Int.emod_nonneg _ nonzero)
  } {
    change Int.ofNat (value % ((2^width : Nat) : Int)).toNat = value % (2 : Int)^width
    rw [Int.natCast_pow]
    have positive := Int.natCast_pos.mpr (Nat.two_pow_pos width)
    have nonzero : (2 : Int)^width ≠ 0 := by
      have cast : ((2^width : Nat) : Int) = (2 : Int)^width := Int.natCast_pow 2 width
      rw [cast] at positive
      omega
    exact Int.toNat_of_nonneg (Int.emod_nonneg _ nonzero)
  }

theorem cast_resize_residue {source : Nat} (target : Nat) (word : BitVec source) :
    Int.ofNat (word.zeroExtend target).toNat = truncateUnsigned (Int.ofNat word.toNat) target := by
  trustIrCompilerProof {
    rw [BitVec.toNat_zeroExtend]
    unfold truncateUnsigned
    change ((word.toNat % 2^target : Nat) : Int) = (word.toNat : Int) % (2 : Int)^target
    rw [Int.ofNat_emod]
    exact congrArg (fun modulus => (word.toNat : Int) % modulus) (Int.natCast_pow 2 target)
  } {
    rw [BitVec.toNat_setWidth]
    unfold truncateUnsigned
    change ((word.toNat % 2^target : Nat) : Int) = (word.toNat : Int) % (2 : Int)^target
    rfl
  }

theorem cast_word_signed {source : Nat} (positive : 0 < source) (word : BitVec source) :
    toSigned (Int.ofNat word.toNat) source = word.toInt := by
  have valid := SMTSort.fromCore_valid (.bv source) word
  have same := SMTSort.toCore_fromCore (.bv source) word
  change BitVec.ofInt source (Int.ofNat word.toNat) = word at same
  have signed := bitvec_ofInt_toSigned source positive (Int.ofNat word.toNat) valid.1 valid.2
  rw [same] at signed
  exact signed.symm

theorem cast_sign_residue {source : Nat} (target : Nat) (positive : 0 < source) (word : BitVec source) :
    Int.ofNat (word.signExtend target).toNat = truncateUnsigned (toSigned (Int.ofNat word.toNat) source) target := by
  rw [cast_word_signed positive]
  exact cast_word_residue _ _

/-- Strict width directions match the actual AY cast encoder. Bool truncation
and extension remain distinct typed cases, including the signed true=-1 rule. -/
inductive IntegerCastTarget : CastOp → SMTSort → SMTSort → Type where
  | trunc (source high : Nat) (narrow : high+1 < source) :
      IntegerCastTarget .Trunc (.bv source) (.bv (high+1))
  | zext (source extra : Nat) (positive : 0 < source) (widen : 0 < extra) :
      IntegerCastTarget .ZExt (.bv source) (.bv (source+extra))
  | sext (source extra : Nat) (positive : 0 < source) (widen : 0 < extra) :
      IntegerCastTarget .SExt (.bv source) (.bv (source+extra))
  | truncBool (source : Nat) (narrow : 1 < source) : IntegerCastTarget .Trunc (.bv source) .bool
  | zextBool (target : Nat) (widen : 1 < target) : IntegerCastTarget .ZExt .bool (.bv target)
  | sextBool (target : Nat) (widen : 1 < target) : IntegerCastTarget .SExt .bool (.bv target)

def IntegerCastTarget.emit {op : CastOp} {input output : SMTSort} (plan : IntegerCastTarget op input output)
    (arg : SMTCheckedTerm input) : SMTCheckedTerm output :=
  match plan with
  | .trunc source high narrow => arg.unary (.bvExtract source high 0 (Nat.zero_le _) (Nat.lt_trans (Nat.lt_succ_self high) narrow))
  | .zext source extra _ _ => arg.unary (.bvZeroExtend source extra)
  | .sext source extra _ _ => arg.unary (.bvSignExtend source extra)
  | .truncBool source narrow =>
      let low := arg.unary (.bvExtract source 0 0 (Nat.zero_le _) (Nat.lt_trans (by decide : 0 < 1) narrow))
      low.binary (.eq (.bv 1)) ⟨.bvConst 1 1, [], by change 0 < 1; decide, rfl, [], rfl⟩
  | .zextBool target widen => arg.ite ⟨.bvConst target 1, [], Nat.lt_trans (by decide : 0 < 1) widen, rfl, [], rfl⟩ ⟨.bvConst target 0, [], Nat.lt_trans (by decide : 0 < 1) widen, rfl, [], rfl⟩
  | .sextBool target widen => arg.ite ⟨.bvConst target (-1), [], Nat.lt_trans (by decide : 0 < 1) widen, rfl, [], rfl⟩ ⟨.bvConst target 0, [], Nat.lt_trans (by decide : 0 < 1) widen, rfl, [], rfl⟩

def IntegerCastTarget.eval {op : CastOp} {input output : SMTSort} (plan : IntegerCastTarget op input output) :
    input.CoreValue → output.CoreValue :=
  match plan with
  | .trunc _ high _ => fun word => word.zeroExtend (high+1)
  | .zext source extra _ _ => fun word => word.zeroExtend (source+extra)
  | .sext source extra _ _ => fun word => word.signExtend (source+extra)
  | .truncBool _ _ => fun word => trustIrCastBit word 0
  | .zextBool target _ => fun value => BitVec.ofInt target (if value then 1 else 0)
  | .sextBool target _ => fun value => BitVec.ofInt target (if value then -1 else 0)

theorem IntegerCastTarget.emit_eval {op : CastOp} {input output : SMTSort}
    (plan : IntegerCastTarget op input output) (arg : SMTCheckedTerm input) (env : SMTEnv) :
    (plan.emit arg).term.eval env = plan.eval (arg.term.eval env) := by
  trustIrCompilerProof {
    cases plan with
    | trunc source high narrow =>
      apply BitVec.eq_of_toNat_eq
      simp [emit, SMTCheckedTerm.unary, SMTTerm.eval, SMTUnary.eval, eval, BitVec.extractLsb, BitVec.extractLsb']
    | zext source extra positive widen => rfl
    | sext source extra positive widen => rfl
    | truncBool source narrow =>
      apply Bool.eq_iff_iff.mpr
      simp [emit, SMTCheckedTerm.unary, SMTCheckedTerm.binary, SMTTerm.eval, SMTUnary.eval,
        SMTBinary.eval, SMTSort.coreEq, eval, BitVec.toNat_eq, BitVec.extractLsb, BitVec.extractLsb', BitVec.getLsb]
      rw [BitVec.toNat_eq]
      simp
    | zextBool target widen => cases h : arg.term.eval env <;> simp [emit, SMTCheckedTerm.ite, SMTTerm.eval, eval, h]
    | sextBool target widen => cases h : arg.term.eval env <;> simp [emit, SMTCheckedTerm.ite, SMTTerm.eval, eval, h]
  } {
    cases plan with
    | trunc source high narrow =>
      apply BitVec.eq_of_toNat_eq
      simp [emit, SMTCheckedTerm.unary, SMTTerm.eval, SMTUnary.eval, eval, BitVec.extractLsb, BitVec.extractLsb']
    | zext source extra positive widen => rfl
    | sext source extra positive widen => rfl
    | truncBool source narrow =>
      apply Bool.eq_iff_iff.mpr
      simp [emit, SMTCheckedTerm.unary, SMTCheckedTerm.binary, SMTTerm.eval, SMTUnary.eval,
        SMTBinary.eval, SMTSort.coreEq, eval, BitVec.toNat_eq, BitVec.extractLsb, BitVec.extractLsb', BitVec.getLsbD]
    | zextBool target widen => cases h : arg.term.eval env <;> simp [emit, SMTCheckedTerm.ite, SMTTerm.eval, eval, h]
    | sextBool target widen => cases h : arg.term.eval env <;> simp [emit, SMTCheckedTerm.ite, SMTTerm.eval, eval, h]
  }

def TrustIrExpr.SMTSort.CastType (model : ByteModel) : SMTSort → Ty → Prop
  | .bool, ty => ty = .Bool
  | .bv bits, ty => ty.isInteger = true ∧ getTyWidth ty model = .ok bits

theorem integer_type_not_bool (ty : Ty) (integer : ty.isInteger = true) : ty.isBool = false := by
  cases ty <;> simp_all [Ty.isInteger, Ty.isBool]

def integerCastResidue (signed : Bool) (source target : Nat) (value : Int) : Int :=
  truncateUnsigned (if signed then toSigned value source else value) target

theorem cast_integer_step (op : CastOp) (srcTy dstTy : Ty) (source target : Nat)
    (operand : ValueId) (state : MachineState) (model : ByteModel) (value : Int)
    (supported : op = .Trunc ∨ op = .ZExt ∨ op = .SExt)
    (destination : getTyWidth dstTy model = .ok target) (notBool : dstTy.isBool = false)
    (lookup : state.lookupValue operand = some (.int source value)) :
    Sem.run (stepInst (.Cast op srcTy dstTy operand) model) state =
      bindEncodedValue state (.ok (.int target (integerCastResidue (op == .SExt) source target value))) := by
  rcases supported with rfl | rfl | rfl <;>
    simp [stepInst, semCast, Sem.lookupValue, lookup, Sem.rejectPartial, destination, notBool,
      Sem.run, Sem.getState, Sem.setState, Sem.bindFresh, StateT.run, StateT.bind, StateT.get,
      StateT.set, StateT.pure, StateT.lift, bindEncodedValue, bind, pure, throw, throwThe,
      MonadExceptOf.throw, Except.bind, Except.pure, integerCastResidue, truncateUnsigned, Int.add_emod]

theorem cast_trunc_bool_step (srcTy : Ty) (source : Nat) (operand : ValueId) (state : MachineState)
    (model : ByteModel) (value : Int) (lookup : state.lookupValue operand = some (.int source value)) :
    Sem.run (stepInst (.Cast .Trunc srcTy .Bool operand) model) state =
      bindEncodedValue state (.ok (.bool (truncateUnsigned value 1 == 1))) := by
  simp [stepInst, semCast, Ty.isBool, Sem.lookupValue, lookup, Sem.rejectPartial,
    Sem.run, Sem.getState, Sem.setState, Sem.bindFresh, StateT.run, StateT.bind, StateT.get,
    StateT.set, StateT.pure, StateT.lift, bindEncodedValue, bind, pure, throw, throwThe,
    MonadExceptOf.throw, Except.bind, Except.pure]

theorem cast_bool_step (op : CastOp) (dstTy : Ty) (target : Nat) (operand : ValueId)
    (state : MachineState) (model : ByteModel) (value : Bool) (supported : op = .ZExt ∨ op = .SExt)
    (destination : getTyWidth dstTy model = .ok target)
    (lookup : state.lookupValue operand = some (.bool value)) :
    Sem.run (stepInst (.Cast op .Bool dstTy operand) model) state =
      bindEncodedValue state (.ok (.int target
        (if op == .SExt then truncateUnsigned (if value then -1 else 0) target else if value then 1 else 0))) := by
  rcases supported with rfl | rfl <;>
    simp [stepInst, semCast, Sem.lookupValue, lookup, Sem.rejectPartial, destination,
      Sem.run, Sem.getState, Sem.setState, Sem.bindFresh, StateT.run, StateT.bind, StateT.get,
      StateT.set, StateT.pure, StateT.lift, bindEncodedValue, bind, pure, throw, throwThe,
      MonadExceptOf.throw, Except.bind, Except.pure, truncateUnsigned, Int.add_emod]

theorem cast_low_bit {source : Nat} (word : BitVec source) :
    (truncateUnsigned (Int.ofNat word.toNat) 1 == 1) = trustIrCastBit word 0 := by
  trustIrCompilerProof {
    apply Bool.eq_iff_iff.mpr
    simp only [truncateUnsigned, BitVec.getLsb, Nat.testBit_zero, decide_eq_true_eq, beq_iff_eq]
    change ((word.toNat : Int) % ((2 : Nat) : Int) = (1 : Int)) ↔ word.toNat % 2 = 1
    rw [← Int.ofNat_emod]
    exact Int.ofNat_inj
  } {
    apply Bool.eq_iff_iff.mpr
    simp only [truncateUnsigned, BitVec.getLsbD, Nat.testBit_zero, decide_eq_true_eq, beq_iff_eq]
    change ((word.toNat : Int) % ((2 : Nat) : Int) = (1 : Int)) ↔ word.toNat % 2 = 1
    exact Int.ofNat_inj
  }

theorem cast_bool_value (target : Nat) (positive : 0 < target) (value : Bool) :
    Int.ofNat (BitVec.ofInt target (if value then 1 else 0)).toNat = if value then 1 else 0 := by
  have oneBound : (1 : Int) < 2^target := by
    have bound := Int.ofNat_lt.mpr (Nat.one_lt_two_pow (show target ≠ 0 by omega))
    simpa only [Int.natCast_pow] using bound
  cases value with
  | false => exact bitvec_ofInt_toNat target 0 (by decide) (by omega)
  | true => exact bitvec_ofInt_toNat target 1 (by decide) oneBound

/-- The actual original Cast instruction reaches the decoded actual target
value and the original fresh binding, retaining the entire machine state. -/
theorem IntegerCastTarget.step_outcome {op : CastOp} {input output : SMTSort}
    (plan : IntegerCastTarget op input output) (srcTy dstTy : Ty) (model : ByteModel)
    (sourceType : input.CastType model srcTy) (destinationType : output.CastType model dstTy)
    (arg : SMTCheckedTerm input) (env : SMTEnv) (operand : ValueId) (state : MachineState)
    (lookup : state.lookupValue operand = some (input.irValue (arg.term.eval env))) :
    Sem.run (stepInst (.Cast op srcTy dstTy operand) model) state =
      bindEncodedValue state (.ok (output.irValue ((plan.emit arg).term.eval env))) := by
  rw [plan.emit_eval]
  cases plan with
  | trunc source high narrow =>
    rw [cast_integer_step .Trunc srcTy dstTy source (high+1) operand state model _
      (Or.inl rfl) destinationType.2 (integer_type_not_bool _ destinationType.1) lookup]
    dsimp only [SMTSort.irValue, eval]
    rw [cast_resize_residue]
    simp [integerCastResidue]
  | zext source extra positive widen =>
    rw [cast_integer_step .ZExt srcTy dstTy source (source+extra) operand state model _
      (Or.inr (Or.inl rfl)) destinationType.2 (integer_type_not_bool _ destinationType.1) lookup]
    dsimp only [SMTSort.irValue, eval]
    rw [cast_resize_residue]
    simp [integerCastResidue]
  | sext source extra positive widen =>
    rw [cast_integer_step .SExt srcTy dstTy source (source+extra) operand state model _
      (Or.inr (Or.inr rfl)) destinationType.2 (integer_type_not_bool _ destinationType.1) lookup]
    dsimp only [SMTSort.irValue, eval]
    rw [cast_sign_residue _ positive]
    simp [integerCastResidue]
  | truncBool source narrow =>
    change dstTy = .Bool at destinationType
    subst dstTy
    rw [cast_trunc_bool_step srcTy source operand state model _ lookup]
    dsimp only [SMTSort.irValue, eval]
    rw [cast_low_bit]
  | zextBool target widen =>
    change srcTy = .Bool at sourceType
    subst srcTy
    rw [cast_bool_step .ZExt dstTy target operand state model _ (Or.inl rfl) destinationType.2 lookup]
    dsimp only [SMTSort.irValue, eval]
    rw [cast_bool_value _ (show 0 < target by omega)]
    rfl
  | sextBool target widen =>
    change srcTy = .Bool at sourceType
    subst srcTy
    rw [cast_bool_step .SExt dstTy target operand state model _ (Or.inr rfl) destinationType.2 lookup]
    dsimp only [SMTSort.irValue, eval]
    rw [cast_word_residue]
    rfl

theorem IntegerCastTarget.context_outcome {op : CastOp} {input output : SMTSort}
    (plan : IntegerCastTarget op input output) (srcTy dstTy : Ty) (ctx : EvalContext)
    (sourceType : input.CastType ctx.byteModel srcTy) (destinationType : output.CastType ctx.byteModel dstTy)
    (arg : SMTCheckedTerm input) (env : SMTEnv) (operand : ValueId) (state : MachineState)
    (lookup : state.lookupValue operand = some (input.irValue (arg.term.eval env))) :
    Sem.run (stepInstWithContext ctx (.Cast op srcTy dstTy operand)) state =
      bindEncodedValue state (.ok (output.irValue ((plan.emit arg).term.eval env))) := by
  have actual := plan.step_outcome srcTy dstTy ctx.byteModel sourceType destinationType arg env operand state lookup
  cases plan <;> simpa only [stepInstWithContext] using actual

/-- A source-bound semantic subject, not a module-validation or body license.
The original operation, types and byte model constrain the target construction. -/
structure IntegerCastSubject (model : ByteModel) where
  op : CastOp
  sourceType : Ty
  destinationType : Ty
  input : SMTSort
  output : SMTSort
  plan : IntegerCastTarget op input output
  sourceTyped : input.CastType model sourceType
  destinationTyped : output.CastType model destinationType

def IntegerCastSubject.instruction {model : ByteModel} (subject : IntegerCastSubject model) (operand : ValueId) : Inst :=
  .Cast subject.op subject.sourceType subject.destinationType operand

def IntegerCastSubject.toRequest {model : ByteModel} (subject : IntegerCastSubject model)
    (arg : SMTCheckedTerm subject.input) : Except String (SMTTypedRequest subject.output) :=
  (subject.plan.emit arg).toTypedRequest

theorem IntegerCastSubject.request_outcome (ctx : EvalContext) (subject : IntegerCastSubject ctx.byteModel)
    (arg : SMTCheckedTerm subject.input) (request : SMTTypedRequest subject.output)
    (built : subject.toRequest arg = .ok request) (env : SMTEnv) (operand : ValueId) (state : MachineState)
    (lookup : state.lookupValue operand = some (subject.input.irValue (arg.term.eval env))) :
    Sem.run (stepInstWithContext ctx (subject.instruction operand)) state =
      bindEncodedValue state (.ok (subject.output.irValue (request.target.eval env))) := by
  have actual := ((subject.plan.emit arg).toTypedRequest_admitted request built).1
  rw [actual]
  exact subject.plan.context_outcome _ _ ctx subject.sourceTyped subject.destinationTyped arg env operand state lookup

theorem IntegerCastSubject.original_request_outcome (ctx : EvalContext) (subject : IntegerCastSubject ctx.byteModel)
    (original : Inst) (operand : ValueId) (same : original = subject.instruction operand)
    (arg : SMTCheckedTerm subject.input) (request : SMTTypedRequest subject.output)
    (built : subject.toRequest arg = .ok request) (env : SMTEnv) (state : MachineState)
    (lookup : state.lookupValue operand = some (subject.input.irValue (arg.term.eval env))) :
    Sem.run (stepInstWithContext ctx original) state =
      bindEncodedValue state (.ok (subject.output.irValue (request.target.eval env))) := by
  rw [same]
  exact subject.request_outcome ctx arg request built env operand state lookup

end TrustIr

#trustIrAxiomsPinned TrustIr.cast_word_residue == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsExact TrustIr.cast_resize_residue == [propext]

#trustIrAxiomsPinned TrustIr.cast_word_signed == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.cast_sign_residue == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsExact TrustIr.IntegerCastTarget.emit_eval == [propext, Quot.sound]

#trustIrAxiomsExact TrustIr.integer_type_not_bool == [propext]

#trustIrAxiomsExact TrustIr.cast_integer_step == [propext, Classical.choice, Quot.sound]

#trustIrAxiomsExact TrustIr.cast_trunc_bool_step == [propext, Quot.sound, Classical.choice]

#trustIrAxiomsExact TrustIr.cast_bool_step == [propext, Classical.choice, Quot.sound]

#trustIrAxiomsExact TrustIr.cast_low_bit == [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.cast_bool_value == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsExact TrustIr.IntegerCastTarget.step_outcome == [propext, Classical.choice, Quot.sound]

#trustIrAxiomsExact TrustIr.IntegerCastTarget.context_outcome == [propext, Classical.choice, Quot.sound]

#trustIrAxiomsExact TrustIr.IntegerCastSubject.request_outcome == [propext, Classical.choice, Quot.sound]

#trustIrAxiomsExact TrustIr.IntegerCastSubject.original_request_outcome == [propext, Classical.choice, Quot.sound]

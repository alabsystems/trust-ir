-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import TrustIr.Proofs.AYPermutationTarget
import TrustIr.Proofs.AYTargetInstruction
import TrustIr.Proofs.AYSubCarry

namespace TrustIr
open TrustIrExpr AYGateCNF

inductive IntegerPermutationOp where
  | bitReverse | byteSwap
  deriving Repr, DecidableEq

def IntegerPermutationOp.irOp : IntegerPermutationOp → UnOp
  | .bitReverse => .BitReverse
  | .byteSwap => .BSwap

def IntegerPermutationOp.number (op : IntegerPermutationOp) (width input : Nat) : Nat :=
  match op with
  | .bitReverse => bitReverseWidth input width
  | .byteSwap => bswapWidth input width

def IntegerPermutationOp.emit {width : Nat} (op : IntegerPermutationOp)
    (arg : SMTCheckedTerm (.bv width)) : Except String (SMTCheckedTerm (.bv width)) :=
  match op with
  | .bitReverse => arg.bitReverse
  | .byteSwap => arg.byteSwap

theorem IntegerPermutationOp.emit_toNat {width : Nat} (op : IntegerPermutationOp)
    (arg result : SMTCheckedTerm (.bv width)) (built : op.emit arg = .ok result) (env : SMTEnv) :
    (result.term.eval env).toNat = op.number width (arg.term.eval env).toNat := by
  cases op with
  | bitReverse => exact arg.bitReverse_toNat result built env
  | byteSwap => exact arg.byteSwap_toNat result built env

private theorem permutation_wrappedNat (width : Nat) (operand : Int) :
    (((operand % (2 : Int)^width) + (2 : Int)^width) % (2 : Int)^width).toNat =
      (BitVec.ofInt width operand).toNat := by
  rw [BitVec.toNat_ofInt, Int.natCast_pow]
  simp [Int.add_emod, Int.emod_emod]

/-- The actual target result, rather than an assumed output equality, supplies
the original scalar operation on an arbitrary mathematical integer carrier. -/
theorem IntegerPermutationOp.target_semIntUnOp {width : Nat} (op : IntegerPermutationOp)
    (arg result : SMTCheckedTerm (.bv width)) (built : op.emit arg = .ok result)
    (env : SMTEnv) (operand : Int) (source : arg.term.eval env = BitVec.ofInt width operand) :
    semIntUnOp op.irOp width operand = .ok (Int.ofNat (result.term.eval env).toNat) := by
  rw [op.emit_toNat arg result built env, source]
  cases op <;> simp only [IntegerPermutationOp.irOp, IntegerPermutationOp.number,
    semIntUnOp, permutation_wrappedNat]

theorem IntegerPermutationOp.semIntUnOp_number (op : IntegerPermutationOp) (width : Nat) (operand : Int) :
    semIntUnOp op.irOp width operand =
      .ok (Int.ofNat (op.number width (BitVec.ofInt width operand).toNat)) := by
  cases op <;> simp only [IntegerPermutationOp.irOp, IntegerPermutationOp.number,
    semIntUnOp, permutation_wrappedNat]

theorem int_unop_step_result (op : UnOp) (ty : Ty) (width : Nat) (id : ValueId)
    (state : MachineState) (model : ByteModel) (operand result : Int)
    (lookup : state.lookupValue id = some (.int width operand))
    (computed : semIntUnOp op width operand = .ok result) :
    Sem.run (stepInst (.UnOp op ty id) model) state =
      bindEncodedValue state (.ok (.int width result)) := by
  simp [stepInst, semUnOp, semUnOpValue, lookup, computed, Sem.run, Sem.lookupValue,
    Sem.rejectPartial, Sem.getState, Sem.setState, Sem.bindFresh, bindEncodedValue,
    StateT.run, StateT.bind, StateT.get, StateT.set, StateT.pure, StateT.lift,
    bind, pure, Except.bind, Except.pure]

/-- Source lookup still occurs before any arithmetic or emitted answer. -/
theorem int_unop_missing_operand (op : UnOp) (ty : Ty) (id : ValueId)
    (state : MachineState) (model : ByteModel) (missing : state.lookupValue id = none) :
    Sem.run (stepInst (.UnOp op ty id) model) state =
      .error (.typeError s!"undefined SSA value: {repr id}") := by
  simp [stepInst, semUnOp, Sem.run, Sem.lookupValue, missing, Sem.getState, Sem.throwTypeError,
    StateT.run, StateT.bind, StateT.get, StateT.pure, StateT.lift,
    bind, pure, Except.bind, Except.pure]
  rfl

/-- Any actual operand poison guard error remains terminal, independently of
whether an unrelated symbolic term or circuit can produce a value. -/
theorem int_unop_guard_error (op : UnOp) (ty : Ty) (id : ValueId) (value : Value)
    (state : MachineState) (model : ByteModel) (error : SemError)
    (lookup : state.lookupValue id = some value)
    (guard : Sem.run (Sem.rejectPartial value "UnOp") state = .error error) :
    Sem.run (stepInst (.UnOp op ty id) model) state = .error error := by
  change (Sem.rejectPartial value "UnOp") state = .error error at guard
  simp [stepInst, semUnOp, Sem.run, Sem.lookupValue, lookup, Sem.getState,
    StateT.run, StateT.bind, StateT.get, StateT.pure, StateT.lift,
    bind, pure, Except.bind, Except.pure, guard]

theorem int_unop_context_missing_operand (ctx : EvalContext) (op : UnOp) (ty : Ty) (id : ValueId)
    (state : MachineState) (missing : state.lookupValue id = none) :
    Sem.run (stepInstWithContext ctx (.UnOp op ty id)) state =
      .error (.typeError s!"undefined SSA value: {repr id}") :=
  int_unop_missing_operand op ty id state ctx.byteModel missing

theorem int_unop_context_guard_error (ctx : EvalContext) (op : UnOp) (ty : Ty) (id : ValueId) (value : Value)
    (state : MachineState) (error : SemError) (lookup : state.lookupValue id = some value)
    (guard : Sem.run (Sem.rejectPartial value "UnOp") state = .error error) :
    Sem.run (stepInstWithContext ctx (.UnOp op ty id)) state = .error error :=
  int_unop_guard_error op ty id value state ctx.byteModel error lookup guard

/-- A checked instruction subject retains both integer classification and the
actual target-dependent source width. Char is only its integer carrier here;
this is not a proof that a produced Char is a Unicode scalar value. -/
structure IntegerPermutationSubject (model : ByteModel) where
  op : IntegerPermutationOp
  ty : Ty
  width : Nat
  integer : ty.isInteger = true
  typeWidth : getTyWidth ty model = .ok width
  positive : 0 < width
  wholeBytes : op = .byteSwap → width % 8 = 0

def IntegerPermutationSubject.ofType (model : ByteModel) (op : IntegerPermutationOp) (ty : Ty) :
    Except String (IntegerPermutationSubject model) :=
  if integer : ty.isInteger = true then
    match actual : getTyWidth ty model with
    | .error _ => .error "integer permutation type has no supported width"
    | .ok width =>
      if positive : 0 < width then
        if bytes : op = .byteSwap → width % 8 = 0 then
          .ok ⟨op,ty,width,integer,actual,positive,bytes⟩
        else .error "byte swap requires a whole number of bytes"
      else .error "integer permutation width must be positive"
  else .error "integer permutation requires an integer type"

def IntegerPermutationSubject.instruction {model : ByteModel} (subject : IntegerPermutationSubject model)
    (operand : ValueId) : Inst := .UnOp subject.op.irOp subject.ty operand

theorem IntegerPermutationSubject.ofType_identity (model : ByteModel) (op : IntegerPermutationOp) (ty : Ty)
    (subject : IntegerPermutationSubject model) (built : IntegerPermutationSubject.ofType model op ty = .ok subject) :
    subject.op = op ∧ subject.ty = ty := by
  unfold IntegerPermutationSubject.ofType at built
  split at built
  · split at built
    · cases built
    · split at built
      · split at built
        · cases built; exact ⟨rfl,rfl⟩
        · cases built
      · cases built
  · cases built

theorem IntegerPermutationSubject.byte_width {model : ByteModel} (subject : IntegerPermutationSubject model)
    (bytes : subject.op = .byteSwap) : (subject.width/8)*8 = subject.width := by
  have whole := subject.wholeBytes bytes
  omega

/-- Concrete original input wires; byte width is derived from the subject,
never supplied independently by a caller. -/
def IntegerPermutationSubject.code {model : ByteModel} (subject : IntegerPermutationSubject model)
    (base : Nat) : WordCode subject.width :=
  match actual : subject.op with
  | .bitReverse => WordCode.bitReverse (fun i : Fin subject.width => base+i.val)
  | .byteSwap =>
    (WordCode.byteSwap (byteInputs (subject.width/8) base)).castWidth
      (by rw [byteInputs_length]; exact subject.byte_width actual)

theorem IntegerPermutationSubject.code_gates {model : ByteModel} (subject : IntegerPermutationSubject model)
    (base : Nat) : (subject.code base).gates = [] := by
  unfold IntegerPermutationSubject.code
  split
  · rfl
  · rw [WordCode.castWidth_gates]
    rfl

theorem IntegerPermutationSubject.code_check {model : ByteModel} (subject : IntegerPermutationSubject model)
    (base next : Nat) (bound : base+subject.width ≤ next) : (subject.code base).check next = true := by
  unfold IntegerPermutationSubject.code
  split
  · apply WordCode.bitReverse_check
    intro i
    have before := i.isLt
    omega
  · rename_i actual
    rw [WordCode.castWidth_check]
    apply WordCode.byteSwap_boundCheck
    rw [subject.byte_width actual]
    exact bound

theorem IntegerPermutationSubject.code_value {model : ByteModel} (subject : IntegerPermutationSubject model)
    (base : Nat) (word : BitVec subject.width) (env : Assignment) :
    ((subject.code base).value (bindWord base word env)).toNat = subject.op.number subject.width word.toNat := by
  unfold IntegerPermutationSubject.code
  split
  · rename_i actual
    simp only [actual, IntegerPermutationOp.number, WordCode.bitReverse_value]
    have source := congrArg BitVec.toNat (WordCode.input_value subject.width base word env)
    change (wordValue (fun i : Fin subject.width => base+i.val) (bindWord base word env)).toNat = word.toNat at source
    rw [source]
  · rename_i actual
    simp only [actual, IntegerPermutationOp.number, WordCode.castWidth_value, BitVec.toNat_cast,
      WordCode.byteSwap_value, byteInputs_length, WordCode.ofWireList_value, byteInputs_wires]
    rw [subject.byte_width actual, wireRange_tabulate, ← wordValue_toNat]
    have source := congrArg BitVec.toNat (WordCode.input_value subject.width base word env)
    change (wordValue (fun i : Fin subject.width => base+i.val) (bindWord base word env)).toNat = word.toNat at source
    rw [source]

/-- Reject the original input slice before constructing the output array or
any code. This receipt contains an actual checked evaluation, not an answer. -/
def IntegerPermutationSubject.checkedCode {model : ByteModel} (subject : IntegerPermutationSubject model)
    (base next : Nat) (word : BitVec subject.width) (env : Assignment) : Option (BitVec subject.width) :=
  if base+subject.width ≤ next then (subject.code base).checkedEval next (bindWord base word env)
  else none

theorem IntegerPermutationSubject.checkedCode_eq_some {model : ByteModel}
    (subject : IntegerPermutationSubject model) (base next : Nat) (word : BitVec subject.width)
    (env : Assignment) (result : BitVec subject.width) :
    subject.checkedCode base next word env = some result ↔
      base+subject.width ≤ next ∧ (subject.code base).value (bindWord base word env) = result := by
  by_cases bound : base+subject.width ≤ next
  · simp [IntegerPermutationSubject.checkedCode, bound, WordCode.checkedEval_eq_some, subject.code_check base next bound]
  · simp [IntegerPermutationSubject.checkedCode, bound]

theorem IntegerPermutationSubject.checkedCode_number {model : ByteModel}
    (subject : IntegerPermutationSubject model) (base next : Nat) (word : BitVec subject.width)
    (env : Assignment) (result : BitVec subject.width)
    (executed : subject.checkedCode base next word env = some result) :
    result.toNat = subject.op.number subject.width word.toNat := by
  have actual := (subject.checkedCode_eq_some base next word env result).mp executed
  rw [← actual.2]
  exact subject.code_value base word env

def IntegerPermutationSubject.toRequest {model : ByteModel} (subject : IntegerPermutationSubject model)
    (arg : SMTCheckedTerm (.bv subject.width)) : Except String (SMTTypedRequest (.bv subject.width)) := do
  let emitted ← subject.op.emit arg
  emitted.toTypedRequest

theorem IntegerPermutationSubject.request_toNat {model : ByteModel}
    (subject : IntegerPermutationSubject model) (arg : SMTCheckedTerm (.bv subject.width))
    (request : SMTTypedRequest (.bv subject.width)) (built : subject.toRequest arg = .ok request) (env : SMTEnv) :
    (request.target.eval env).toNat = subject.op.number subject.width (arg.term.eval env).toNat := by
  unfold IntegerPermutationSubject.toRequest at built
  cases emitted : subject.op.emit arg with
  | error reason => simp [emitted, bind, Except.bind] at built
  | ok result =>
    have requested : result.toTypedRequest = .ok request := by simpa [emitted, bind, Except.bind] using built
    rw [(result.toTypedRequest_admitted request requested).1]
    exact subject.op.emit_toNat arg result emitted env

/-- A successful request's exact emitted target determines the complete
original instruction result and state. The sole value premise identifies
its actual input; no result or final-state equality is assumed. -/
theorem IntegerPermutationSubject.request_outcome {model : ByteModel}
    (subject : IntegerPermutationSubject model) (arg : SMTCheckedTerm (.bv subject.width))
    (request : SMTTypedRequest (.bv subject.width)) (built : subject.toRequest arg = .ok request)
    (id : ValueId) (state : MachineState) (operand : Int) (env : SMTEnv)
    (lookup : state.lookupValue id = some (.int subject.width operand))
    (source : arg.term.eval env = BitVec.ofInt subject.width operand) :
    Sem.run (stepInst (subject.instruction id) model) state =
      bindEncodedValue state (.ok (.int subject.width (Int.ofNat (request.target.eval env).toNat))) := by
  unfold IntegerPermutationSubject.toRequest at built
  cases emitted : subject.op.emit arg with
  | error reason => simp [emitted, bind, Except.bind] at built
  | ok result =>
    have requested : result.toTypedRequest = .ok request := by
      simpa [emitted, bind, Except.bind] using built
    have actual := (result.toTypedRequest_admitted request requested).1
    rw [actual]
    exact int_unop_step_result subject.op.irOp subject.ty subject.width id state model operand _ lookup
      (subject.op.target_semIntUnOp arg result emitted env operand source)

theorem IntegerPermutationSubject.context_request_outcome (ctx : EvalContext)
    (subject : IntegerPermutationSubject ctx.byteModel) (arg : SMTCheckedTerm (.bv subject.width))
    (request : SMTTypedRequest (.bv subject.width)) (built : subject.toRequest arg = .ok request)
    (id : ValueId) (state : MachineState) (operand : Int) (env : SMTEnv)
    (lookup : state.lookupValue id = some (.int subject.width operand))
    (source : arg.term.eval env = BitVec.ofInt subject.width operand) :
    Sem.run (stepInstWithContext ctx (subject.instruction id)) state =
      bindEncodedValue state (.ok (.int subject.width (Int.ofNat (request.target.eval env).toNat))) :=
  subject.request_outcome arg request built id state operand env lookup source

/-- The checked site is indexed by its ORIGINAL instruction, preserving the
opcode, declared type, operand and model-derived width through request building. -/
structure IntegerPermutationSite (model : ByteModel) (original : Inst) where
  subject : IntegerPermutationSubject model
  operand : ValueId
  origin : original = subject.instruction operand

def IntegerPermutationSite.ofInst (model : ByteModel) (original : Inst) :
    Except String (IntegerPermutationSite model original) :=
  match original with
  | .UnOp .BitReverse ty id =>
    match checked : IntegerPermutationSubject.ofType model .bitReverse ty with
    | .error reason => .error reason
    | .ok subject =>
      .ok ⟨subject,id,by
        have identity := IntegerPermutationSubject.ofType_identity model .bitReverse ty subject checked
        simp [IntegerPermutationSubject.instruction, identity.1, identity.2, IntegerPermutationOp.irOp]⟩
  | .UnOp .BSwap ty id =>
    match checked : IntegerPermutationSubject.ofType model .byteSwap ty with
    | .error reason => .error reason
    | .ok subject =>
      .ok ⟨subject,id,by
        have identity := IntegerPermutationSubject.ofType_identity model .byteSwap ty subject checked
        simp [IntegerPermutationSubject.instruction, identity.1, identity.2, IntegerPermutationOp.irOp]⟩
  | _ => .error "instruction is not an integer bit/byte permutation"

def IntegerPermutationSite.toRequest {model : ByteModel} {original : Inst}
    (site : IntegerPermutationSite model original) (arg : SMTCheckedTerm (.bv site.subject.width)) :
    Except String (SMTTypedRequest (.bv site.subject.width)) := site.subject.toRequest arg

/-- From an actual admitted source site and its actual returned request, the
complete contextual instruction outcome follows without a supplied result. -/
theorem IntegerPermutationSite.request_outcome (ctx : EvalContext) (original : Inst)
    (site : IntegerPermutationSite ctx.byteModel original)
    (arg : SMTCheckedTerm (.bv site.subject.width)) (request : SMTTypedRequest (.bv site.subject.width))
    (built : site.toRequest arg = .ok request) (state : MachineState) (operand : Int) (env : SMTEnv)
    (lookup : state.lookupValue site.operand = some (.int site.subject.width operand))
    (source : arg.term.eval env = BitVec.ofInt site.subject.width operand) :
    Sem.run (stepInstWithContext ctx original) state =
      bindEncodedValue state (.ok (.int site.subject.width (Int.ofNat (request.target.eval env).toNat))) := by
  have identity := congrArg (fun inst => Sem.run (stepInstWithContext ctx inst) state) site.origin
  exact identity.trans (site.subject.context_request_outcome ctx arg request built site.operand state operand env lookup source)

theorem IntegerPermutationSite.bare_request_outcome (model : ByteModel) (original : Inst)
    (site : IntegerPermutationSite model original)
    (arg : SMTCheckedTerm (.bv site.subject.width)) (request : SMTTypedRequest (.bv site.subject.width))
    (built : site.toRequest arg = .ok request) (state : MachineState) (operand : Int) (env : SMTEnv)
    (lookup : state.lookupValue site.operand = some (.int site.subject.width operand))
    (source : arg.term.eval env = BitVec.ofInt site.subject.width operand) :
    Sem.run (stepInst original model) state =
      bindEncodedValue state (.ok (.int site.subject.width (Int.ofNat (request.target.eval env).toNat))) := by
  have identity := congrArg (fun inst => Sem.run (stepInst inst model) state) site.origin
  exact identity.trans (site.subject.request_outcome arg request built site.operand state operand env lookup source)

/-- The complete state equation exposes the one fresh binding and every
untouched field via MachineState.bindValue; this is not only scalar equality. -/
theorem IntegerPermutationSite.request_state (ctx : EvalContext) (original : Inst)
    (site : IntegerPermutationSite ctx.byteModel original)
    (arg : SMTCheckedTerm (.bv site.subject.width)) (request : SMTTypedRequest (.bv site.subject.width))
    (built : site.toRequest arg = .ok request) (state : MachineState) (operand : Int) (env : SMTEnv)
    (lookup : state.lookupValue site.operand = some (.int site.subject.width operand))
    (source : arg.term.eval env = BitVec.ofInt site.subject.width operand) :
    Sem.run (stepInstWithContext ctx original) state =
      .ok (.value (some ⟨state.nextValueId⟩),
        { state with
          locals := state.locals.set ⟨state.nextValueId⟩
            (.int site.subject.width (Int.ofNat (request.target.eval env).toNat))
          nextValueId := state.nextValueId+1 }) :=
  site.request_outcome ctx original arg request built state operand env lookup source

/-- All three actual objects meet: the source-indexed site, its returned
request and the independently checked circuit receipt. Only input mapping is
assumed; the equality of their outputs is derived. -/
theorem IntegerPermutationSite.gate_request_value {model : ByteModel} {original : Inst}
    (site : IntegerPermutationSite model original) (arg : SMTCheckedTerm (.bv site.subject.width))
    (request : SMTTypedRequest (.bv site.subject.width)) (built : site.toRequest arg = .ok request)
    (operand : Int) (target : SMTEnv) (source : arg.term.eval target = BitVec.ofInt site.subject.width operand)
    (base next : Nat) (env : Assignment) (result : BitVec site.subject.width)
    (executed : site.subject.checkedCode base next (BitVec.ofInt site.subject.width operand) env = some result) :
    result = request.target.eval target := by
  apply BitVec.eq_of_toNat_eq
  rw [site.subject.checkedCode_number base next _ env result executed,
    site.subject.request_toNat arg request built target, source]

/-- Actual checked gate evaluation also reaches the original instruction and
its complete state, for arbitrary signed/noncanonical operand carriers. -/
theorem IntegerPermutationSite.gate_outcome (ctx : EvalContext) (original : Inst)
    (site : IntegerPermutationSite ctx.byteModel original) (base next : Nat) (env : Assignment)
    (state : MachineState) (operand : Int) (result : BitVec site.subject.width)
    (lookup : state.lookupValue site.operand = some (.int site.subject.width operand))
    (executed : site.subject.checkedCode base next (BitVec.ofInt site.subject.width operand) env = some result) :
    Sem.run (stepInstWithContext ctx original) state =
      bindEncodedValue state (.ok (.int site.subject.width (Int.ofNat result.toNat))) := by
  have value := site.subject.checkedCode_number base next _ env result executed
  have computed := site.subject.op.semIntUnOp_number site.subject.width operand
  rw [← value] at computed
  have identity := congrArg (fun inst => Sem.run (stepInstWithContext ctx inst) state) site.origin
  apply identity.trans
  exact int_unop_step_result site.subject.op.irOp site.subject.ty site.subject.width site.operand state
    ctx.byteModel operand _ lookup computed

end TrustIr

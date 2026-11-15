-- Copyright 2026 Andrew Yates | Author: Andrew Yates | Apache-2.0
import TrustIr.Semantics.Eval

namespace TrustIr

@[simp] theorem checkClosureValue_ptr (ctx : EvalContext) (address : Nat)
    (provenance : Option AllocId) :
    checkClosureValue ctx .Ptr (.ptr address provenance) = .ok () := rfl

/-- Construction preserves the exact checked runtime values. -/
theorem makeClosureValue_of_checked (ctx : EvalContext) (cid : ClosureTyId)
    (fn : FuncId) (captures : List Value) (d : ClosureTy) (s : FuncTyDef)
    (f : EvalFunction)
    (hc : closureContract ctx cid fn = .ok (d, s, f))
    (hn : captures.length = d.captures.length)
    (hv : (d.captures.zip captures).forM (fun (t, v) => checkClosureValue ctx t v) = .ok ()) :
    makeClosureValue ctx cid fn captures = .ok (.typedClosure cid fn captures) := by
  simp [makeClosureValue, hc, hn, hv, Except.bind, Except.pure, Bind.bind, Pure.pure]

/-- The actual instruction dispatcher uses that checked value; no alternate
    constant environment or integer/pointer encoding is introduced. -/
theorem stepInstWithContext_makeClosure (ctx : EvalContext) (cid : ClosureTyId)
    (fn : FuncId) (ids : List ValueId) :
    stepInstWithContext ctx (.MakeClosure cid fn ids) = (do
      let captures ← ids.mapM Sem.lookupValue
      let v ← match makeClosureValue ctx cid fn captures with
        | .ok v => pure v
        | .error e => throw e
      pure (.value (some (← Sem.bindFresh v)))) := rfl

/-- Calls prepend the checked captures in order, and preserve the nominal
    signature identity even when another signature has the same shape. -/
theorem closureCall_of_checked (ctx : EvalContext) (cid : ClosureTyId)
    (fn : FuncId) (captures args : List Value) (sig : FuncTyId) (conv : CallingConv)
    (d : ClosureTy) (s : FuncTyDef) (f : EvalFunction)
    (hc : closureContract ctx cid fn = .ok (d, s, f))
    (hs : d.func = sig) (hv : f.callingConv = conv)
    (hm : makeClosureValue ctx cid fn captures = .ok (.typedClosure cid fn captures))
    (hn : args.length = s.params.length)
    (ha : (s.params.zip args).forM (fun (t, v) => checkClosureValue ctx t v) = .ok ()) :
    closureCall ctx cid fn captures sig args conv = .ok (fn, captures ++ args) := by
  have hconv : (conv != conv) = false := by cases conv <;> rfl
  simp [closureCall, hc, hs, hv, hm, hn, ha, hconv, Except.bind, Except.pure, Bind.bind, Pure.pure]

private def closureIdentityTarget : EvalFunction :=
  { body := { paramTys := [.Ptr], returnTys := [.Ptr] }
    cfg := fun pc => if pc == (⟨0⟩ : BlockId) then
      some { params := [(⟨0⟩, .Ptr)], body := [], terminator := .Return [⟨0⟩] } else none
    entryBlock := ⟨0⟩, callingConv := .Rust }

private def closureIdentityEntry : EvalFunction :=
  { body := { paramTys := [.Ptr], returnTys := [.Ptr] }
    cfg := fun pc => if pc == (⟨0⟩ : BlockId) then
      some { params := [(⟨0⟩, .Ptr)], body := [.MakeClosure ⟨0⟩ ⟨1⟩ [⟨0⟩], .CallIndirect ⟨1⟩ ⟨0⟩ [] .Rust], bodyResultDests := [[⟨1⟩], [⟨2⟩]], terminator := .Return [⟨2⟩] } else none
    entryBlock := ⟨0⟩, callingConv := .Rust }

private def closureIdentityContext : EvalContext :=
  { EvalContext.empty with
    maxCallDepth := 1
    functions := fun f => if f == (⟨0⟩ : FuncId) then some closureIdentityEntry
      else if f == (⟨1⟩ : FuncId) then some closureIdentityTarget else none
    funcTys := fun s => if s == (⟨0⟩ : FuncTyId) then
      some { params := [], returns := [.Ptr], isVararg := false } else none
    closures := fun c => if c == (⟨0⟩ : ClosureTyId) then
      some { func := ⟨0⟩, captures := [.Ptr] } else none }

-- Reduce the evaluator directly; generated smart-unfolding equations duplicate
-- large call/return terms during elaboration without changing the kernel proof.
set_option smartUnfolding false in
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
/-- A kernel-reduced run of the actual contextual evaluator: constructing and
    calling a closure preserves every address and allocation identity. This
    quantifies over the pointer, rather than checking one fixture address. -/
theorem evaluator_closure_preserves_pointer (address : Nat) (provenance : Option AllocId)
    (memory : Memory) :
    (Sem.run (evalFunctionInContext closureIdentityContext ⟨0⟩ [.ptr address provenance] 2)
      { MachineState.empty with memory := memory }).map Prod.fst = .ok [.ptr address provenance] := by
  rfl


set_option smartUnfolding false in
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
/-- The same operational run introduces no memory writes or allocations. -/
theorem evaluator_closure_preserves_memory (address : Nat) (provenance : Option AllocId)
    (memory : Memory) :
    (Sem.run (evalFunctionInContext closureIdentityContext ⟨0⟩ [.ptr address provenance] 2)
      { MachineState.empty with memory := memory }).map (fun result => result.2.memory) = .ok memory := by
  rfl

/-- A successful data update preserves both nominal and code identities and
    changes exactly the selected capture in declaration order. -/
theorem closureInsert_of_checked (ctx : EvalContext) (cid : ClosureTyId)
    (fn : FuncId) (captures : List Value) (field : Nat) (value : Value)
    (definition : ClosureTy) (fieldTy : Ty)
    (hc : checkedClosureCaptures ctx cid captures = .ok definition)
    (hf : (trustIrListGet? definition.captures field) = some fieldTy)
    (hv : checkClosureValue ctx fieldTy value = .ok ()) :
    closureInsert ctx (.Closure cid) cid fn captures field value =
      .ok (.typedClosure cid fn (captures.set field value)) := by
  simp [closureInsert, closureTyEq_refl, hc, hf, hv,
    Except.bind, Except.pure, Bind.bind, Pure.pure]

/-- Extracting a checked capture returns its original runtime value. -/
theorem closureExtract_of_checked (ctx : EvalContext) (cid : ClosureTyId)
    (fn : FuncId) (captures : List Value) (field : Nat) (value : Value)
    (definition : ClosureTy) (fieldTy : Ty)
    (hc : checkedClosureCaptures ctx cid captures = .ok definition)
    (ht : (trustIrListGet? definition.captures field) = some fieldTy)
    (hv : (trustIrListGet? captures field) = some value) :
    closureExtract ctx fieldTy cid fn captures field = .ok value := by
  simp [closureExtract, hc, ht, hv, closureTyEq_refl,
    Except.bind, Except.pure, Bind.bind, Pure.pure]

private def closureUpdateEntry : EvalFunction :=
  { body := { paramTys := [.Ptr, .Ptr], returnTys := [.Ptr, .Ptr] }
    cfg := fun pc => if pc == (⟨0⟩ : BlockId) then
      some { params := [(⟨0⟩, .Ptr), (⟨1⟩, .Ptr)]
             body := [.MakeClosure ⟨0⟩ ⟨1⟩ [⟨0⟩],
               .InsertField (.Closure ⟨0⟩) ⟨2⟩ 0 ⟨1⟩,
               .CallIndirect ⟨2⟩ ⟨0⟩ [] .Rust,
               .CallIndirect ⟨3⟩ ⟨0⟩ [] .Rust]
             bodyResultDests := [[⟨2⟩], [⟨3⟩], [⟨4⟩], [⟨5⟩]]
             terminator := .Return [⟨4⟩, ⟨5⟩] } else none
    entryBlock := ⟨0⟩, callingConv := .Rust }

private def closureUpdateContext : EvalContext :=
  { closureIdentityContext with functions := fun f =>
      if f == (⟨0⟩ : FuncId) then some closureUpdateEntry
      else closureIdentityContext.functions f }

set_option smartUnfolding false in
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
/-- Full contextual evaluation, quantified over both pointers and all memory:
    updating one closure value leaves the original environment intact and
    returns both exact captured pointers when the two values are applied. -/
theorem evaluator_closure_update_preserves_original
    (oldAddress newAddress : Nat) (oldProvenance newProvenance : Option AllocId)
    (memory : Memory) :
    (Sem.run (evalFunctionInContext closureUpdateContext ⟨0⟩
      [.ptr oldAddress oldProvenance, .ptr newAddress newProvenance] 2)
      { MachineState.empty with memory := memory }).map Prod.fst =
        .ok [.ptr oldAddress oldProvenance, .ptr newAddress newProvenance] := by
  rfl

set_option smartUnfolding false in
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
/-- Both environment construction and immutable replacement are value
    operations, including across the evaluator's real call/return frames. -/
theorem evaluator_closure_update_preserves_memory
    (oldAddress newAddress : Nat) (oldProvenance newProvenance : Option AllocId)
    (memory : Memory) :
    (Sem.run (evalFunctionInContext closureUpdateContext ⟨0⟩
      [.ptr oldAddress oldProvenance, .ptr newAddress newProvenance] 2)
      { MachineState.empty with memory := memory }).map (fun result => result.2.memory) =
        .ok memory := by
  rfl

end TrustIr

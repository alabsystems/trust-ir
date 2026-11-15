-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.StoreImageReadback

/- Enable kernel reduction through the imported mutual compiler equations.
The metadata is local to these proofs; no executable definition is replaced. -/
run_cmd do
  if Lean.versionString == "4.30.0-rc2" then
    let env ← Lean.getEnv
    let mut registered := 0
    for (n, _) in env.constants.map₁.toList do
      if n.toString.endsWith "TrustIr.SourceLayout.compileTy.eq_def" ||
         n.toString.endsWith "TrustIr.SourceLayout.compileTypes.eq_def" then
        Lean.Elab.Command.elabCommand (← `(command| attribute [local cbv_eval] $(Lean.mkIdent n):ident))
        registered := registered + 1
    unless registered == 2 do
      Lean.throwError "expected the two original layout compiler equations"
  else if Lean.versionString != "4.8.0" then
    Lean.throwError "unsupported compiler for layout equation reduction"

namespace TrustIr.StoreImageReadbackControls
open AggregateMemory

private def root : Ty := .Tuple [.U8,.U32]
private def fields : List (Nat × Plan) :=
  [(0,.leaf .U8 ⟨1,1⟩),(4,.leaf .U32 ⟨4,4⟩)]
private def plan : Plan := .fields root ⟨8,4⟩ fields
private def input : Value := .aggregate [.int 8 257,.int 32 9]
private def output : Value := .aggregate [.int 8 1,.int 32 9]
private def pointer : Value := .ptr 104 (some ⟨7⟩)
private def source (model : ByteModel) : SourceLayout.Environment := { model }
private def service (model : ByteModel) : Service := prepare (source model) [root]
private def context (model : ByteModel) : EvalContext :=
  { EvalContext.empty with byteModel := model,memoryService := some (service model) }
private def initial (value : Value) : MachineState :=
  { MachineState.empty with
    locals := (ValueMap.empty.set ⟨0⟩ pointer).set ⟨1⟩ value
    nextValueId := 40
    memory := (({ Memory.empty with
      allocations := [{ id := ⟨7⟩,base := 104,size := 16,requested := 16,alive := true,origin := .rustStack }]
      nextAddr := 120
      nextAllocId := 8 }).writeImage 104 (ByteImage.fill 16 (some 255))).recordUnwritten ⟨7⟩ 104 [(0,8)] }
private def afterStore (model : ByteModel) (value : Value) : MachineState :=
  match Sem.run (stepInstWithContext (context model) (.Store root ⟨0⟩ ⟨1⟩ false none)) (initial value) with
  | .ok (_,state) => state
  | .error _ => initial value
private theorem ran (model : ByteModel) (value : Value) (allowed : value = input) :
    Sem.run (stepInstWithContext (context model) (.Store root ⟨0⟩ ⟨1⟩ false none)) (initial value) =
      .ok (.value none,afterStore model value) := by
  trustIrCompilerProof {
    subst value
    cases model <;> rfl
  } {
    subst value
    cases model <;> trustIrReduce
  }

private theorem queried (model : ByteModel) : (service model).query root = .ok plan := by
  trustIrCompilerProof {
    cases model <;> rfl
  } {
    cases model <;> trustIrReduce
  }

private theorem typed (model : ByteModel) (memory : Memory) : ReadbackInput model none memory plan input := by
  apply ReadbackInput.fields_of_pairs
  exact .cons (.scalar (.integer .U8 ⟨1,1⟩ 8 257 rfl (by cases model <;> rfl) rfl))
    (.cons (.scalar (.integer .U32 ⟨4,4⟩ 32 9 rfl (by cases model <;> rfl) rfl)) .nil)
private theorem ready : TopCharReady plan input := by
  intro layout width raw impossible
  cases impossible

theorem actual_store_has_admitted_snapshot (model : ByteModel) :
    ∃ result, decode model none (afterStore model input).memory plan
      ((afterStore model input).memory.readImage 104 8) = .ok result ∧
      ValueReadback model (afterStore model input).memory input result := by
  have admitted : ∀ actual, (initial input).lookupValue ⟨1⟩ = some actual → ∀ selectedPlan,
      (prepare (source model) [root]).query root = .ok selectedPlan →
        ReadbackInput model none (afterStore model input).memory selectedPlan actual := by
    intro actual found selectedPlan query
    change some input = some actual at found
    cases found
    have equal : selectedPlan = plan := Except.ok.inj (query.symm.trans (queried model))
    subst selectedPlan
    exact typed model _
  have character : ∀ actual, (initial input).lookupValue ⟨1⟩ = some actual → ∀ selectedPlan,
      (prepare (source model) [root]).query root = .ok selectedPlan → TopCharReady selectedPlan actual := by
    intro actual found selectedPlan query
    change some input = some actual at found
    cases found
    have equal : selectedPlan = plan := Except.ok.inj (query.symm.trans (queried model))
    subst selectedPlan
    exact ready
  have clear : ∀ actual, (initial input).lookupValue ⟨1⟩ = some actual → carriesUnwritten actual = false := by
    intro actual found
    change some input = some actual at found
    cases found
    rfl
  obtain ⟨_,heldPointer,heldInput,selectedPlan,address,allocation,result,pointerFound,inputFound,query,pointerShape,decoded,related⟩ :=
    stepStore_prepared_snapshot_readback (context model) (source model) [root] root ⟨0⟩ ⟨1⟩ false none rfl
      (initial input) (afterStore model input) (.value none) admitted character clear (ran model input rfl)
  change some pointer = some heldPointer at pointerFound
  change some input = some heldInput at inputFound
  cases pointerFound
  cases inputFound
  have equal : selectedPlan = plan := Except.ok.inj (query.symm.trans (queried model))
  subst selectedPlan
  cases pointerShape
  exact ⟨result,decoded,related⟩

theorem snapshot_contains_normalized_integer_not_raw_carrier (model : ByteModel) :
    decode model none (afterStore model input).memory plan ((afterStore model input).memory.readImage 104 8) = .ok output := by
  trustIrCompilerProof {
    cases model <;> rfl
  } {
    cases model <;> trustIrReduce
  }

theorem raw_carrier_identity_is_not_the_readback_relation (model : ByteModel) :
    decode model none (afterStore model input).memory plan ((afterStore model input).memory.readImage 104 8) ≠ .ok input := by
  trustIrCompilerProof {
    cases model <;> intro bad <;> cases bad
  } {
    intro bad
    rw [snapshot_contains_normalized_integer_not_raw_carrier model] at bad
    cases bad
  }

theorem absent_padding_overwrites_stale_initialized_bytes (model : ByteModel) :
    ((initial input).memory.bytes 105,(afterStore model input).memory.bytes 105) = (some 255,none) := by
  trustIrCompilerProof {
    cases model <;> rfl
  } {
    cases model <;> trustIrReduce
  }

theorem ordinary_store_does_not_retain_stale_unwritten_coverage (model : ByteModel) :
    ((initial input).memory.isUnwritten ⟨7⟩ 104,(afterStore model input).memory.isUnwritten ⟨7⟩ 104) = (true,false) := by
  trustIrCompilerProof {
    cases model <;> rfl
  } {
    cases model <;> trustIrReduce
  }

theorem outside_snapshot_is_absent_even_when_following_memory_is_initialized (model : ByteModel) :
    (((afterStore model input).memory.readImage 104 8).get 8,(afterStore model input).memory.bytes 112) = (none,some 255) := by
  trustIrCompilerProof {
    cases model <;> rfl
  } {
    cases model <;> trustIrReduce
  }

theorem original_store_then_load_reads_the_normalized_value (model : ByteModel) :
    (Sem.run (do
      let _ ← stepInstWithContext (context model) (.Store root ⟨0⟩ ⟨1⟩ false none)
      stepInstWithContext (context model) (.Load root ⟨0⟩ false none)) (initial input)).map
      (fun pair => (pair.1,pair.2.lookupValue ⟨40⟩,pair.2.nextValueId,pair.2.memory.bytes 105)) =
      .ok (.value (some ⟨40⟩),some output,41,none) := by
  trustIrCompilerProof {
    cases model <;> rfl
  } {
    have accessed : Sem.run (Sem.checkedAccess "Load" 104 ⟨7⟩ 8 4 model)
        (afterStore model input) = .ok (104,afterStore model input) := by
      cases model <;> trustIrReduce
    have decoded : loadImageResult model none root false (afterStore model input).memory ⟨7⟩ 104 plan
        ((afterStore model input).memory.readImage 104 8) = .ok output := by
      simp only [loadImageResult,snapshot_contains_normalized_integer_not_raw_carrier model]
      cases model <;> trustIrReduce
    have loaded : Sem.run (selectedLoadAction (context model) root pointer false none)
        (afterStore model input) = .ok (output,afterStore model input) := by
      change Sem.run (loadValue (service model) none root pointer false none model)
        (afterStore model input) = .ok (output,afterStore model input)
      exact loadValue_of_checks (service model) none root false none model (afterStore model input)
        plan 4 104 ⟨7⟩ output (by cases model <;> trustIrReduce) (queried model) rfl accessed decoded
    have lookup : (afterStore model input).lookupValue ⟨0⟩ = some pointer := by
      cases model <;> trustIrReduce
    have fresh : (afterStore model input).nextValueId = 40 := by
      cases model <;> trustIrReduce
    have loadRun : Sem.run (stepInstWithContext (context model) (.Load root ⟨0⟩ false none))
        (afterStore model input) = .ok (.value (some ⟨(afterStore model input).nextValueId⟩),
          { afterStore model input with
            locals := (afterStore model input).locals.set ⟨(afterStore model input).nextValueId⟩ output
            nextValueId := (afterStore model input).nextValueId + 1 }) :=
      (stepLoad_success_iff (context model) root ⟨0⟩ false none _ _ _).mpr
        ⟨pointer,output,lookup,loaded,rfl,rfl⟩
    have padding : (afterStore model input).memory.bytes 105 = none :=
      congrArg Prod.snd (absent_padding_overwrites_stale_initialized_bytes model)
    rw [Sem.run_bind,ran model input rfl]
    simp only [Except.bind,loadRun,Except.map,MachineState.lookupValue,fresh,padding,ValueMap.set]
    rfl
  }

theorem partial_store_also_replaces_stale_bytes (model : ByteModel) :
    let value := Value.partial [none,some 2,none,none,some 9,some 0,some 0,some 0]
    ((afterStore model value).memory.bytes 104,(afterStore model value).memory.bytes 105,
      (afterStore model value).memory.isUnwritten ⟨7⟩ 104) = (none,some 2,false) := by
  trustIrCompilerProof {
    cases model <;> rfl
  } {
    cases model <;> trustIrReduce
  }

theorem partial_transport_has_no_typed_readback_admission (model : ByteModel) (memory : Memory) (selectedPlan : Plan) :
    ¬ ReadbackInput model none memory selectedPlan (.partial [none]) := by
  intro admitted
  cases admitted with
  | scalar scalar => cases scalar
  | function function => cases function

theorem empty_snapshot_has_no_outside_byte (memory : Memory) (allocation : AllocId) (address index : Nat) :
    (((memory.writeImage address ByteImage.empty).recordUnwritten allocation address []).readImage address 0).get index = none := by
  exact ByteImage.get_outside _ index (by simp)

end TrustIr.StoreImageReadbackControls

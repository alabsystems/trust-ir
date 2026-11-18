-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.StoreImageReadback
import TrustIr.Semantics.OriginalClosureMemory

namespace TrustIrEval.ClosureStorage

/-- Two checked observations of the same complete original module cannot
choose different code identities, even when their memory roots differ. -/
theorem Target.same_original_value {source : Module} {closure : TrustIr.ClosureTyId}
    (first second : Target source closure) : first.value = second.value := by
  obtain ⟨targets,firstRun,present,_⟩ := first.original_constructors
  obtain ⟨other,secondRun,_,unique⟩ := second.original_constructors
  rw [firstRun] at secondRun
  cases secondRun
  exact unique first.value present

/-- Repeated checked storage bindings retain the same source model, nominal
capture declaration, descriptor and shape, not just the same numeric target. -/
theorem Binding.same_original_storage {source : Module} {closure : TrustIr.ClosureTyId}
    (first second : Binding source closure) :
    first.model = second.model ∧ first.nominal = second.nominal ∧
    first.descriptor = second.descriptor ∧ first.shape = second.shape := by
  have model : first.model = second.model := Except.ok.inj (first.modelSource.symm.trans second.modelSource)
  have nominal : first.nominal = second.nominal := Option.some.inj (first.nominalSource.symm.trans second.nominalSource)
  have firstDescriptor := first.descriptorSource
  rw [model] at firstDescriptor
  have descriptor : first.descriptor = second.descriptor :=
    Option.some.inj (Except.ok.inj (firstDescriptor.symm.trans second.descriptorSource))
  obtain ⟨firstAfter,firstShape⟩ := first.shapeSource
  obtain ⟨secondAfter,secondShape⟩ := second.shapeSource
  rw [model] at firstShape
  have shape : first.shape = second.shape := congrArg Prod.fst (Except.ok.inj (firstShape.symm.trans secondShape))
  exact ⟨model,nominal,descriptor,shape⟩

/-- Only the existing successful shape query supplies capture separation.
This does not turn a shape into an execution Plan. -/
theorem Binding.field_geometry {source : Module} {closure : TrustIr.ClosureTyId}
    (binding : Binding source closure) : TrustIr.SourceLayout.FieldGeometry binding.shape := by
  obtain ⟨next,queried⟩ := binding.shapeSource
  have history := TrustIr.SourceLayout.Session.Reachable.prepared (source := layoutSourceOf source binding.model)
  exact (history.query_storage_geometry .shape (.Closure closure) binding.shape queried).1

end TrustIrEval.ClosureStorage

namespace TrustIr.AggregateMemory
open SourceLayout

/-- The existing field encoder and decoder transport every admitted capture
through a complete observed snapshot. Children keep their actual source origins;
no fictitious parent Closure Plan is introduced. -/
theorem capture_fields_readback (source : Environment) (model : ByteModel)
    (order : FunctionAddressOrder) (memory : Memory) (size : Nat)
    (fields : List (Nat × Plan)) (inputs : List Value) (stored : Image)
    (encoded : encodeCaptureImage model order size fields inputs = .ok stored)
    (storedSize : stored.bytes.size = size) (loaded : ByteImage)
    (extent : loaded.size = size) (bytes : ∀ index, loaded.get index = stored.bytes.get index)
    (census : fields.length = inputs.length)
    (origins : ∀ offset child, (offset,child) ∈ fields →
      Plan.Origin (SourceElement source) (ActualSummary source) child.ty child)
    (placement : ∀ position offset child, (trustIrListGet? fields position) = some (offset,child) →
      FieldsAvoidLane (fields.drop (position + 1)) offset child.layout.size)
    (admitted : ∀ position offset child input,
      (trustIrListGet? fields position) = some (offset,child) → (trustIrListGet? inputs position) = some input →
      ReadbackInput model order memory child input) :
    ∃ outputs, decodeCaptureImage model order memory fields loaded = .ok outputs ∧
      ValueReadback model memory (.aggregate inputs) (.aggregate outputs) := by
  have fieldRun : FieldsEncoded model order fields inputs false { bytes := ByteImage.fill size none } stored := encoded
  have reads : ∀ position offset child input,
      (trustIrListGet? fields position) = some (offset,child) → (trustIrListGet? inputs position) = some input →
      ∃ output, ChildDecoded model order memory child (loaded.slice offset child.layout.size) output ∧
        ValueReadback model memory input output := by
    intro position offset child input found selected
    obtain ⟨childImage,childEncoded,lane⟩ := fieldRun.child_lane position offset child found input selected
      (placement position offset child found)
    have observed := lane.of_parent_observations (extent.trans storedSize.symm) bytes
    have childSize := encode_extent model order child input false childImage childEncoded
    obtain ⟨partSize,partBytes⟩ := observed.slice_bytes
    have member : (offset,child) ∈ fields := CompilerCompat.listGetConstructive_mem (by
      trustIrCompilerProof { simpa only [CompilerCompat.listGetConstructive_pointwise] using found } { exact found })
    rw [childSize] at partSize partBytes
    exact (admitted position offset child input found selected).readback source
      (origins offset child member) childImage childEncoded (loaded.slice offset child.layout.size)
      partSize partBytes
  obtain ⟨outputs,decoded,related⟩ := fields_readback_of_children model order memory fields inputs loaded census reads
  exact ⟨outputs,decoded,related⟩


/-- A successful leaf-capture encoder establishes the initialization check of
actual closure Load. The parent padding is never read or initialized. Recursive
capture decoder readback above is broader; this coverage law intentionally
states its leaf-plan scope instead of assuming a caller's missing-byte answer. -/
theorem capture_leaf_coverage (model : ByteModel) (order : FunctionAddressOrder)
    (size : Nat) (fields : List (Nat × Plan)) (inputs : List Value) (stored : Image)
    (encoded : encodeCaptureImage model order size fields inputs = .ok stored)
    (storedSize : stored.bytes.size = size) (loaded : ByteImage)
    (extent : loaded.size = size) (bytes : ∀ index, loaded.get index = stored.bytes.get index)
    (placement : ∀ position offset child, (trustIrListGet? fields position) = some (offset,child) →
      FieldsAvoidLane (fields.drop (position + 1)) offset child.layout.size)
    (leaves : ∀ offset child, (offset,child) ∈ fields → ∃ ty layout, child = .leaf ty layout) :
    coveredCaptureImage fields loaded = .ok none := by
  have fieldRun : FieldsEncoded model order fields inputs false { bytes := ByteImage.fill size none } stored := encoded
  apply coveredCaptureImage_of_children
  intro offset child member
  obtain ⟨ty,layout,rfl⟩ := leaves offset child member
  obtain ⟨position,selected⟩ := List.mem_iff_get.mp member
  have found : (trustIrListGet? fields position.val) = some (offset,Plan.leaf ty layout) := by
    rw [CompilerCompat.listGet?_eq_get position.isLt,selected]
  obtain ⟨value,earlier,childImage,placed,valueAt,prefixRun,childEncoded,written,suffix⟩ :=
    fieldRun.at position.val offset (.leaf ty layout) found
  obtain ⟨image,encodedChild,lane⟩ := fieldRun.child_lane position.val offset (.leaf ty layout)
    found value valueAt (placement position.val offset (.leaf ty layout) found)
  have observed := lane.of_parent_observations (extent.trans storedSize.symm) bytes
  have childSize := encode_extent model order (.leaf ty layout) value false image encodedChild
  obtain ⟨partSize,partBytes⟩ := observed.slice_bytes
  rw [childSize] at partSize partBytes
  simp only [Plan.layout] at childSize partSize partBytes
  obtain ⟨initializedBytes,_length,initialized⟩ :=
    encode_leaf_range_initialized model order ty layout value image encodedChild 0 layout.size (by omega)
  have missing : firstMissing (loaded.slice offset layout.size) = none := by
    apply (firstMissing_eq_none_iff _).mpr
    intro index inside absent
    obtain ⟨byte,present⟩ := initialized.present (by rw [childSize]; omega) index (by omega)
    have same := partBytes index
    simp only [Nat.zero_add] at present
    rw [present,absent] at same
    cases same
  rw [covered]
  simp only [Plan.layout,partSize,bne_self_eq_false,Bool.false_eq_true,ite_false,missing,Pure.pure,Except.pure,Bind.bind,Except.bind]

end TrustIr.AggregateMemory

namespace TrustIr.OriginalClosureMemory

/-- Logical closure readback retains the checked full-source binding and code
identity. Captures use the existing residue/provenance-aware relation; raw
Value equality and a target inferred from geometry are deliberately absent. -/
def ValueReadback (source : TrustIrEval.Module) (closure : ClosureTyId)
    (binding : TrustIrEval.ClosureStorage.Binding source closure)
    (model : ByteModel) (memory : Memory) (input output : Value) : Prop :=
  ∃ inputs outputs,
    input = .typedClosure closure binding.target.value inputs ∧
    output = .typedClosure closure binding.target.value outputs ∧
    AggregateMemory.ValueReadback model memory (.aggregate inputs) (.aggregate outputs)

private theorem run_bind_success {α β : Type} (first : Sem α) (next : α → Sem β)
    (before after : MachineState) (result : β)
    (run : Sem.run (first >>= next) before = .ok (result,after)) :
    ∃ value middle, Sem.run first before = .ok (value,middle) ∧
      Sem.run (next value) middle = .ok (result,after) := by
  rw [Sem.run_bind] at run
  cases checked : Sem.run first before with
  | error error =>
    simp only [checked,Except.bind] at run
    all_goals cases run
  | ok pair =>
    obtain ⟨value,middle⟩ := pair
    simp only [checked,Except.bind] at run
    exact ⟨value,middle,rfl,run⟩

private theorem except_bind_success {α β : Type} (first : Except SemError α)
    (next : α → Sem β) (before after : MachineState) (result : β)
    (run : Sem.run (Sem.fromMemoryExcept first >>= next) before = .ok (result,after)) :
    ∃ value, first = .ok value ∧ Sem.run (next value) before = .ok (result,after) := by
  cases first with
  | error error => cases run
  | ok value => exact ⟨value,rfl,run⟩

private theorem access_success (model : ByteModel) (operation : String) (address : Nat) (allocation : AllocId)
    (size alignment : Nat) (before after : MachineState) (actual : Nat)
    (run : Sem.run (Sem.checkedAccess operation address allocation size alignment model)
      before = .ok (actual,after)) : after = before ∧ actual = address := by
  cases model with
  | le64 =>
    obtain ⟨same,addressSame,_⟩ := checkedAccess_ok_inv operation address allocation size alignment before after actual run
    exact ⟨same,addressSame⟩
  | le32 =>
    obtain ⟨same,addressSame,_⟩ := checkedAccess32_names_live_provenance operation address allocation size alignment before after actual run
    exact ⟨same,addressSame⟩


/-- Successful access depends on the same live allocation records and the
same target domain, not on stored bytes or an operation's diagnostic spelling. -/
private theorem access_same_allocations (model : ByteModel) (first second : String)
    (address : Nat) (allocation : AllocId) (size alignment : Nat) (before after : MachineState)
    (allocations : after.memory.allocations = before.memory.allocations)
    (run : Sem.run (Sem.checkedAccess first address allocation size alignment model) before = .ok (address,before)) :
    Sem.run (Sem.checkedAccess second address allocation size alignment model) after = .ok (address,after) := by
  have legacy : Sem.run (Sem.checkedAccess first address allocation size alignment .le64) before = .ok (address,before) := by
    cases model with
    | le64 => exact run
    | le32 => exact (checkedAccess32_retains_legacy first address allocation size alignment before before address run).1
  obtain ⟨_,_,record,found,live,aligned,base,extent⟩ :=
    checkedAccess_ok_inv first address allocation size alignment before before address legacy
  have foundAfter : after.memory.lookup allocation = some record := by
    unfold Memory.lookup
    rw [allocations]
    exact found
  have accepted := checkedAccess_ok_of second size alignment after address allocation record foundAfter live aligned base extent
  cases model with
  | le64 => exact accepted
  | le32 =>
    have bounds := checkedAccess32_retains_legacy first address allocation size alignment before before address run
    rw [checkedAccess_model_factor,Sem.run_bind]
    have range : Sem.run (Sem.checkTargetRange .le32 second address size) after = .ok ((),after) := by
      simp [Sem.checkTargetRange,bounds.2.1,bounds.2.2,Sem.run_pure]
    rw [range]
    exact accepted

private theorem alignment_same_operation (first second : String) (natural : Nat) (declared : Option Nat)
    (alignment : Nat) (run : checkedMemoryAlign first natural declared = .ok alignment) :
    checkedMemoryAlign second natural declared = .ok alignment := by
  obtain ⟨same,bounded,power⟩ := checkedMemoryAlign_ok_inv first natural declared alignment run
  subst alignment
  simp [checkedMemoryAlign,bounded,power]

/-- Execution introduction for the original-source service. Every actual Load
query, alignment/access check, coverage traversal and decoder result is kept;
this lemma does not infer a target or supply a decoder outcome. -/
theorem prepared_load_of_checks (source : TrustIrEval.Module) (model : ByteModel) (roots : List Ty)
    (order : FunctionAddressOrder) (closure : ClosureTyId) (strict : Bool) (align : Option Nat)
    (state : MachineState) (binding : TrustIrEval.ClosureStorage.Binding source closure)
    (storage : MemoryTypeLayout) (fields : List (Nat × AggregateMemory.Plan))
    (alignment address : Nat) (allocation : AllocId) (outputs : List Value)
    (modelSame : binding.model = model)
    (sourceSame : TrustIrEval.ClosureStorage.bindingOf source closure = .ok binding)
    (size : storage.size = binding.shape.size) (alignedShape : binding.shape.align = some storage.alignment)
    (queried : capturePlans (prepare source model roots) storage.size binding.nominal.captures
      binding.descriptor.captureOffsets binding.shape.fields = .ok fields)
    (aligned : checkedMemoryAlign "Load" storage.alignment align = .ok alignment)
    (accessed : Sem.run (Sem.checkedAccess "Load" address allocation storage.size alignment model) state = .ok (address,state))
    (covered : AggregateMemory.coveredCaptureImage fields (state.memory.readImage address storage.size) = .ok none)
    (decoded : AggregateMemory.decodeCaptureImage model order state.memory fields
      (state.memory.readImage address storage.size) = .ok outputs) :
    Sem.run (loadValue (prepare source model roots) order closure (.ptr address (some allocation)) strict align model)
      state = .ok (.typedClosure closure binding.target.value outputs,state) := by
  unfold loadValue
  rw [prepared_binding source model roots closure binding sourceSame modelSame]
  simp only [Sem.fromMemoryExcept,pure_bind]
  rw [layout_of_fields binding.shape storage size alignedShape]
  simp only [Sem.fromMemoryExcept,pure_bind]
  rw [queried]
  simp only [Sem.fromMemoryExcept,pure_bind]
  rw [aligned]
  simp only [Sem.fromMemoryExcept,pure_bind,Sem.rejectPartial,Sem.expectPointer]
  rw [Sem.run_bind,accessed]
  simp only [Except.bind]
  have get : Sem.run Sem.getState state = .ok (state,state) := rfl
  rw [Sem.run_bind,get]
  simp only [Except.bind]
  change Sem.run (do
    let missing ← Sem.fromMemoryExcept (AggregateMemory.coveredCaptureImage fields (state.memory.readImage address storage.size))
    if missing.isSome then Sem.throwUB "Load: reading uninitialized covered memory"
    let captures ← Sem.fromMemoryExcept (AggregateMemory.decodeCaptureImage model order state.memory fields
      (state.memory.readImage address storage.size))
    pure (Value.typedClosure closure binding.target.value captures)) state = .ok (Value.typedClosure closure binding.target.value outputs,state)
  simp only [covered,decoded,Sem.fromMemoryExcept,pure_bind,Option.isSome, Bool.false_eq_true,ite_false,Sem.run_pure]


/-- A successful original-source Load depends on the exact complete Memory,
not on the caller's local SSA frame. All source, target, alignment, provenance,
coverage and decoding checks are replayed by the same production action. The
hypothesis includes unwritten metadata and allocation records; byte equality
alone is not sufficient. -/
theorem prepared_load_same_memory (source : TrustIrEval.Module) (model : ByteModel)
    (roots : List Ty) (order : FunctionAddressOrder) (closure : ClosureTyId)
    (pointer : Value) (strict : Bool) (align : Option Nat) (before observer : MachineState) (value : Value)
    (sameMemory : observer.memory = before.memory)
    (run : Sem.run (loadValue (prepare source model roots) order closure pointer strict align model)
      before = .ok (value,before)) :
    Sem.run (loadValue (prepare source model roots) order closure pointer strict align model)
      observer = .ok (value,observer) := by
  unfold loadValue at run
  obtain ⟨held,heldRun,run⟩ := except_bind_success _ _ before before value run
  obtain ⟨bindingModel,bindingSource⟩ := binding_facts (prepare source model roots) model closure held heldRun
  obtain ⟨storage,storageRun,run⟩ := except_bind_success _ _ before before value run
  obtain ⟨fields,fieldsRun,run⟩ := except_bind_success _ _ before before value run
  obtain ⟨alignment,alignmentRun,run⟩ := except_bind_success _ _ before before value run
  obtain ⟨unit,middle,inspected,run⟩ := run_bind_success _ _ before before value run
  have noChange := rejectPartial_ok_state "Load" pointer before middle unit inspected
  subst middle
  cases unit
  obtain ⟨pair,middle,pointed,run⟩ := run_bind_success _ _ before before value run
  obtain ⟨noChange,pointerShape⟩ := expectPointer_ok_inv "Load" pointer before middle pair pointed
  subst middle
  obtain ⟨address,allocation⟩ := pair
  obtain ⟨actual,middle,accessed,run⟩ := run_bind_success _ _ before before value run
  obtain ⟨noChange,addressSame⟩ := access_success model "Load" address allocation storage.size alignment before middle actual accessed
  subst middle
  subst actual
  have get : Sem.run Sem.getState before = .ok (before,before) := rfl
  rw [Sem.run_bind,get] at run
  simp only [Except.bind] at run
  obtain ⟨missing,covered,run⟩ := except_bind_success _ _ before before value run
  cases missing with
  | some index => cases run
  | none =>
    simp only [Option.isSome,Bool.false_eq_true,ite_false,pure_bind] at run
    obtain ⟨outputs,decoded,run⟩ := except_bind_success _ _ before before value run
    cases run
    have storageLayout : storage.size = held.shape.size ∧ held.shape.align = some storage.alignment := by
      change ((match held.shape.align with
        | none => Except.error (.unsupported .layout "closure storage has no byte alignment")
        | some alignment => Except.ok ({size := held.shape.size,alignment} : MemoryTypeLayout)) : Except SemError MemoryTypeLayout) = .ok storage at storageRun
      cases aligned : held.shape.align with
      | none => rw [aligned] at storageRun; cases storageRun
      | some alignment => rw [aligned] at storageRun; cases storageRun; exact ⟨rfl,rfl⟩
    have loadAccess := access_same_allocations model "Load" "Load" address allocation storage.size alignment
      before observer (congrArg Memory.allocations sameMemory) accessed
    have coverage : AggregateMemory.coveredCaptureImage fields (observer.memory.readImage address storage.size) = .ok none := by
      rw [sameMemory]; exact covered
    have decoding : AggregateMemory.decodeCaptureImage model order observer.memory fields
        (observer.memory.readImage address storage.size) = .ok outputs := by
      rw [sameMemory]; exact decoded
    rw [pointerShape]
    exact prepared_load_of_checks source model roots order closure strict align observer held storage fields
      alignment address allocation outputs bindingModel bindingSource storageLayout.1 storageLayout.2 fieldsRun alignmentRun loadAccess coverage decoding

/-- A successful actual typed-closure Store supplies its original code binding,
real destination provenance and complete memory write. No selected image,
intermediate state or claimed decoder outcome is accepted from the caller. -/
theorem prepared_store_success_steps (source : TrustIrEval.Module) (model : ByteModel)
    (roots : List Ty) (order : FunctionAddressOrder) (closure nominal : ClosureTyId)
    (target : FuncId) (captures : List Value) (pointer : Value) (strict : Bool)
    (align : Option Nat) (before after : MachineState)
    (run : Sem.run (storeValue (prepare source model roots) order closure pointer
      (.typedClosure nominal target captures) strict align model) before = .ok ((),after)) :
    ∃ binding : TrustIrEval.ClosureStorage.Binding source closure,
      binding.model = model ∧ TrustIrEval.ClosureStorage.bindingOf source closure = .ok binding ∧
      nominal = closure ∧ target = binding.target.value ∧ captures.length = binding.nominal.captures.length ∧
      ∃ (storage : MemoryTypeLayout) (alignment : Nat) (fields : List (Nat × AggregateMemory.Plan))
        (address : Nat) (allocation : AllocId) (image : AggregateMemory.Image),
        storage.size = binding.shape.size ∧ binding.shape.align = some storage.alignment ∧
        checkedMemoryAlign "Store" storage.alignment align = .ok alignment ∧
        pointer = .ptr address (some allocation) ∧
        capturePlans (prepare source model roots) storage.size binding.nominal.captures
          binding.descriptor.captureOffsets binding.shape.fields = .ok fields ∧
        Sem.run (Sem.checkedAccess "Store" address allocation storage.size alignment model) before = .ok (address,before) ∧
        AggregateMemory.FieldBindings (binding.shape.fields.map (·.ty)) (binding.shape.fields.map (·.offset)) fields ∧
        AggregateMemory.FieldExtents binding.shape.fields fields ∧ fields.length = binding.nominal.captures.length ∧
        AggregateMemory.FieldBindings binding.nominal.captures binding.descriptor.captureOffsets fields ∧
        (∀ offset child, (offset,child) ∈ fields →
          (AggregateMemory.prepare (TrustIrEval.layoutSourceOf source model) roots).query child.ty = .ok child ∧
            offset + child.layout.size ≤ storage.size) ∧
        AggregateMemory.encodeCaptureImage model order storage.size fields captures = .ok image ∧
        image.bytes.size = storage.size ∧
        after = { before with memory :=
          (before.memory.writeImage address image.bytes).recordUnwritten allocation address image.unwritten } := by
  unfold storeValue at run
  by_cases rejected : (strict && ((Value.typedClosure nominal target captures).isPoison ||
      AggregateMemory.carriesUnwritten (.typedClosure nominal target captures))) = true
  · simp only [rejected,ite_true] at run
    cases run
  · simp only [rejected,ite_false,pure_bind] at run
    obtain ⟨held,heldRun,run⟩ := except_bind_success _ _ before after () run
    obtain ⟨bindingModel,bindingSource⟩ := binding_facts (prepare source model roots) model closure held heldRun
    obtain ⟨storage,storageRun,run⟩ := except_bind_success _ _ before after () run
    obtain ⟨fields,fieldsRun,run⟩ := except_bind_success _ _ before after () run
    obtain ⟨alignment,alignmentRun,run⟩ := except_bind_success _ _ before after () run
    obtain ⟨unit,middle,inspected,run⟩ := run_bind_success _ _ before after () run
    have same := rejectPartial_ok_state "Store" pointer before middle unit inspected
    subst middle
    cases unit
    obtain ⟨pair,middle,pointed,run⟩ := run_bind_success _ _ before after () run
    obtain ⟨same,pointerShape⟩ := expectPointer_ok_inv "Store" pointer before middle pair pointed
    subst middle
    obtain ⟨address,allocation⟩ := pair
    obtain ⟨actual,middle,accessed,run⟩ := run_bind_success _ _ before after () run
    obtain ⟨same,addressSame⟩ := access_success model "Store" address allocation storage.size alignment before middle actual accessed
    subst middle
    subst actual
    by_cases mismatch : (nominal != closure || target != held.target.value ||
      captures.length != held.nominal.captures.length) = true
    · simp only [mismatch,ite_true] at run
      cases run
    · simp only [mismatch,ite_false,pure_bind] at run
      have checked : nominal = closure ∧ target = held.target.value := by
        constructor
        · by_cases same : nominal = closure
          · exact same
          · exact False.elim (mismatch (by simp [same]))
        · by_cases same : target = held.target.value
          · exact same
          · exact False.elim (mismatch (by simp [same]))
      have captureCount : captures.length = held.nominal.captures.length := by
        by_cases same : captures.length = held.nominal.captures.length
        · exact same
        · exact False.elim (mismatch (by simp [same]))
      obtain ⟨image,encoded,run⟩ := except_bind_success _ _ before after () run
      by_cases extent : image.bytes.size = storage.size
      · simp only [extent,bne_self_eq_false,Bool.false_eq_true,ite_false,pure_bind] at run
        have finalState : after = { before with memory :=
          (before.memory.writeImage address image.bytes).recordUnwritten allocation address image.unwritten } := by
          cases run
          rfl
        have storageLayout : storage.size = held.shape.size ∧ held.shape.align = some storage.alignment := by
          change ((match held.shape.align with
            | none => Except.error (.unsupported .layout "closure storage has no byte alignment")
            | some alignment => Except.ok ({ size := held.shape.size, alignment } : MemoryTypeLayout)) : Except SemError MemoryTypeLayout) = .ok storage at storageRun
          cases aligned : held.shape.align with
          | none => rw [aligned] at storageRun; cases storageRun
          | some alignment => rw [aligned] at storageRun; cases storageRun; exact ⟨rfl,rfl⟩
        obtain ⟨fieldBindings,fieldExtents,fieldCount,inputBindings,fieldQueries⟩ :=
          capturePlans_facts (prepare source model roots) storage.size held.nominal.captures
            held.descriptor.captureOffsets held.shape.fields fields fieldsRun
        have childQueries : ∀ offset child, (offset,child) ∈ fields →
            (AggregateMemory.prepare (TrustIrEval.layoutSourceOf source model) roots).query child.ty = .ok child ∧
              offset + child.layout.size ≤ storage.size := by
          intro offset child member
          simpa only [prepared_memory] using fieldQueries offset child member
        exact ⟨held,bindingModel,bindingSource,checked.1,checked.2,captureCount,
          storage,alignment,fields,address,allocation,image,storageLayout.1,storageLayout.2,alignmentRun,
          pointerShape,fieldsRun,accessed,fieldBindings,fieldExtents,fieldCount,inputBindings,childQueries,encoded,extent,finalState⟩
      · have different : (image.bytes.size != storage.size) = true := by simpa using extent
        simp only [different,ite_true] at run
        cases run

/-- The actual Store supplies its exact complete image and state update. -/
theorem prepared_store_success_image (source : TrustIrEval.Module) (model : ByteModel)
    (roots : List Ty) (order : FunctionAddressOrder) (closure nominal : ClosureTyId)
    (target : FuncId) (captures : List Value) (pointer : Value) (strict : Bool)
    (align : Option Nat) (before after : MachineState)
    (run : Sem.run (storeValue (prepare source model roots) order closure pointer
      (.typedClosure nominal target captures) strict align model) before = .ok ((),after)) :
    ∃ binding : TrustIrEval.ClosureStorage.Binding source closure,
      nominal = closure ∧ target = binding.target.value ∧
      ∃ (address : Nat) (allocation : AllocId) (image : AggregateMemory.Image),
        pointer = .ptr address (some allocation) ∧ image.bytes.size = binding.shape.size ∧
        after = { before with memory :=
          (before.memory.writeImage address image.bytes).recordUnwritten allocation address image.unwritten } := by
  obtain ⟨binding,_model,_source,nominalSame,targetSame,_count,storage,_alignment,_fields,address,
    allocation,image,size,_aligned,_alignmentRun,pointed,_captureRun,_accessed,_bindings,_extents,_fieldCount,
    _inputBindings,_queries,_encoded,imageSize,changed⟩ :=
      prepared_store_success_steps source model roots order closure nominal target captures pointer strict align before after run
  exact ⟨binding,nominalSame,targetSame,address,allocation,image,pointed,imageSize.trans size,changed⟩

/-- The real closure Store leaves all allocation identities, lifetimes and
allocation frontiers intact. Only bytes in its exact source footprint and
unwritten-lane metadata may change. This is a source memory locality law, not
an unrestricted machine-memory equation or callee/placement certificate. -/
theorem prepared_store_memory_locality (source : TrustIrEval.Module) (model : ByteModel)
    (roots : List Ty) (order : FunctionAddressOrder) (closure nominal : ClosureTyId)
    (target : FuncId) (captures : List Value) (pointer : Value) (strict : Bool)
    (align : Option Nat) (before after : MachineState)
    (run : Sem.run (storeValue (prepare source model roots) order closure pointer
      (.typedClosure nominal target captures) strict align model) before = .ok ((),after)) :
    ∃ binding : TrustIrEval.ClosureStorage.Binding source closure,
      nominal = closure ∧ target = binding.target.value ∧
      ∃ (address : Nat) (allocation : AllocId),
        pointer = .ptr address (some allocation) ∧
        after.memory.allocations = before.memory.allocations ∧
        after.memory.nextAddr = before.memory.nextAddr ∧
        after.memory.nextAllocId = before.memory.nextAllocId ∧
        ∀ query, query < address ∨ address + binding.shape.size ≤ query →
          after.memory.bytes query = before.memory.bytes query := by
  obtain ⟨binding,nominalSame,targetSame,address,allocation,image,pointed,extent,changed⟩ :=
    prepared_store_success_image source model roots order closure nominal target captures pointer strict align before after run
  refine ⟨binding,nominalSame,targetSame,address,allocation,pointed,?_,?_,?_,?_⟩
  · rw [changed]
    cases image.unwritten <;> rfl
  · rw [changed]
    cases image.unwritten <;> rfl
  · rw [changed]
    cases image.unwritten <;> rfl
  · intro query apart
    rw [changed,Memory.recordUnwritten_bytes]
    exact Memory.bytes_writeImage_outside before.memory address query image.bytes (by simpa only [extent] using apart)

/-- Positional existing capture admission. Values are related in the actual
receiving memory; integer normalization and pointer provenance remain explicit.
This is neither a pointer-dereference nor a callee/frame permission. -/
def CaptureReadbackInputs (source : TrustIrEval.Module) (model : ByteModel) (roots : List Ty)
    (order : FunctionAddressOrder) (memory : Memory) (closure : ClosureTyId) (captures : List Value) : Prop :=
  ∀ nominal, (trustIrListGet? source.closureTys closure.index) = some nominal →
    ∀ position ty input plan,
      (trustIrListGet? nominal.captures position) = some ty →
      (trustIrListGet? captures position) = some input →
      (AggregateMemory.prepare (TrustIrEval.layoutSourceOf source model) roots).query ty = .ok plan →
      AggregateMemory.ReadbackInput model order memory plan input

/-- The actual successful Store supplies every byte and child query used by
capture readback. The only value premise is the existing typed transport
admission, never a caller-selected image or a claimed decoder outcome. -/
theorem prepared_store_snapshot_readback (source : TrustIrEval.Module) (model : ByteModel)
    (roots : List Ty) (order : FunctionAddressOrder) (closure nominal : ClosureTyId)
    (target : FuncId) (captures : List Value) (pointer : Value) (strict : Bool)
    (align : Option Nat) (before after : MachineState)
    (admitted : CaptureReadbackInputs source model roots order after.memory closure captures)
    (run : Sem.run (storeValue (prepare source model roots) order closure pointer
      (.typedClosure nominal target captures) strict align model) before = .ok ((),after)) :
    ∃ binding : TrustIrEval.ClosureStorage.Binding source closure,
      ∃ (storage : MemoryTypeLayout) (fields : List (Nat × AggregateMemory.Plan))
        (address : Nat) (allocation : AllocId) (outputs : List Value),
        pointer = .ptr address (some allocation) ∧ storage.size = binding.shape.size ∧
        AggregateMemory.decodeCaptureImage model order after.memory fields
          (after.memory.readImage address storage.size) = .ok outputs ∧
        ValueReadback source closure binding model after.memory (.typedClosure nominal target captures)
          (.typedClosure closure binding.target.value outputs) := by
  obtain ⟨binding,_model,_source,nominalSame,targetSame,captureCount,storage,alignment,fields,address,
    allocation,image,size,_aligned,_alignmentRun,pointed,_captureRun,_accessed,bindings,extents,fieldCount,
    inputBindings,queries,encoded,imageSize,changed⟩ :=
      prepared_store_success_steps source model roots order closure nominal target captures pointer strict align before after run
  have observations : ∀ index,
      (after.memory.readImage address storage.size).get index = image.bytes.get index := by
    intro index
    rw [changed,← imageSize]
    exact Memory.readImage_after_write_record before.memory allocation address image.bytes image.unwritten index
  have origins : ∀ offset child, (offset,child) ∈ fields →
      AggregateMemory.Plan.Origin (AggregateMemory.SourceElement (TrustIrEval.layoutSourceOf source model))
        (AggregateMemory.ActualSummary (TrustIrEval.layoutSourceOf source model)) child.ty child := by
    intro offset child member
    exact (AggregateMemory.prepared_plan_origin (TrustIrEval.layoutSourceOf source model) roots child.ty child
      (queries offset child member).1).own
  have placement : ∀ position offset child, (trustIrListGet? fields position) = some (offset,child) →
      AggregateMemory.FieldsAvoidLane (fields.drop (position + 1)) offset child.layout.size := by
    intro position offset child found
    simpa only [Nat.add_zero] using bindings.later_avoids_subrange extents binding.field_geometry.1
      position offset child found 0 child.layout.size (by omega)
  have inputs : ∀ position offset child input,
      (trustIrListGet? fields position) = some (offset,child) → (trustIrListGet? captures position) = some input →
      AggregateMemory.ReadbackInput model order after.memory child input := by
    intro position offset child input found selected
    have member : (offset,child) ∈ fields := CompilerCompat.listGetConstructive_mem (by
      trustIrCompilerProof { simpa only [CompilerCompat.listGetConstructive_pointwise] using found } { exact found })
    exact admitted binding.nominal binding.nominalSource position child.ty input child
      (inputBindings.at position offset child found).1 selected (queries offset child member).1
  obtain ⟨outputs,decoded,related⟩ := AggregateMemory.capture_fields_readback
    (TrustIrEval.layoutSourceOf source model) model order after.memory storage.size fields captures image encoded imageSize
    (after.memory.readImage address storage.size) (Memory.readImage_size _ _ _) observations
    (fieldCount.trans captureCount.symm) origins placement inputs
  refine ⟨binding,storage,fields,address,allocation,outputs,pointed,size,decoded,?_⟩
  refine ⟨captures,outputs,?_,rfl,related⟩
  rw [nominalSame,targetSame]


/-- Source-scoped leaf-capture coverage. This restricts the theorem, not the
runtime's existing recursive capture support; no layout is accepted without
its actual source query. An empty environment satisfies it vacuously. -/
def CaptureLeafQueries (source : TrustIrEval.Module) (model : ByteModel) (roots : List Ty)
    (closure : ClosureTyId) : Prop :=
  ∀ nominal, (trustIrListGet? source.closureTys closure.index) = some nominal →
    ∀ ty, ty ∈ nominal.captures → ∀ plan,
      (AggregateMemory.prepare (TrustIrEval.layoutSourceOf source model) roots).query ty = .ok plan →
      ∃ actualTy layout, plan = .leaf actualTy layout

/-- The actual successful original-closure Store is followed by the actual
checked Load at the same pointer and with the same alignment. Initialization
is derived from the real leaf capture encodings, not assumed as a decoder
answer; parent padding remains unwritten. Capture values retain the existing
residue/provenance-aware relation. This is source execution, not a machine
frame, callee-memory agreement or source-to-native certificate. -/
theorem prepared_store_load_readback (source : TrustIrEval.Module) (model : ByteModel)
    (roots : List Ty) (order : FunctionAddressOrder) (closure nominal : ClosureTyId)
    (target : FuncId) (captures : List Value) (pointer : Value) (strict : Bool)
    (align : Option Nat) (before after : MachineState)
    (admitted : CaptureReadbackInputs source model roots order after.memory closure captures)
    (leafQueries : CaptureLeafQueries source model roots closure)
    (run : Sem.run (storeValue (prepare source model roots) order closure pointer
      (.typedClosure nominal target captures) strict align model) before = .ok ((),after)) :
    ∃ (binding : TrustIrEval.ClosureStorage.Binding source closure) (output : Value),
      Sem.run (loadValue (prepare source model roots) order closure pointer strict align model) after = .ok (output,after) ∧
      ValueReadback source closure binding model after.memory (.typedClosure nominal target captures) output := by
  obtain ⟨binding,bindingModel,bindingSource,nominalSame,targetSame,captureCount,storage,alignment,fields,address,
    allocation,image,size,alignedShape,alignmentRun,pointed,captureRun,accessed,bindings,extents,fieldCount,
    inputBindings,queries,encoded,imageSize,changed⟩ :=
      prepared_store_success_steps source model roots order closure nominal target captures pointer strict align before after run
  have observations : ∀ index,
      (after.memory.readImage address storage.size).get index = image.bytes.get index := by
    intro index
    rw [changed,← imageSize]
    exact Memory.readImage_after_write_record before.memory allocation address image.bytes image.unwritten index
  have origins : ∀ offset child, (offset,child) ∈ fields →
      AggregateMemory.Plan.Origin (AggregateMemory.SourceElement (TrustIrEval.layoutSourceOf source model))
        (AggregateMemory.ActualSummary (TrustIrEval.layoutSourceOf source model)) child.ty child := by
    intro offset child member
    exact (AggregateMemory.prepared_plan_origin (TrustIrEval.layoutSourceOf source model) roots child.ty child
      (queries offset child member).1).own
  have placement : ∀ position offset child, (trustIrListGet? fields position) = some (offset,child) →
      AggregateMemory.FieldsAvoidLane (fields.drop (position + 1)) offset child.layout.size := by
    intro position offset child found
    simpa only [Nat.add_zero] using bindings.later_avoids_subrange extents binding.field_geometry.1
      position offset child found 0 child.layout.size (by omega)
  have inputs : ∀ position offset child input,
      (trustIrListGet? fields position) = some (offset,child) → (trustIrListGet? captures position) = some input →
      AggregateMemory.ReadbackInput model order after.memory child input := by
    intro position offset child input found selected
    have member : (offset,child) ∈ fields := CompilerCompat.listGetConstructive_mem (by
      trustIrCompilerProof { simpa only [CompilerCompat.listGetConstructive_pointwise] using found } { exact found })
    exact admitted binding.nominal binding.nominalSource position child.ty input child
      (inputBindings.at position offset child found).1 selected (queries offset child member).1
  obtain ⟨outputs,decoded,related⟩ := AggregateMemory.capture_fields_readback
    (TrustIrEval.layoutSourceOf source model) model order after.memory storage.size fields captures image encoded imageSize
    (after.memory.readImage address storage.size) (Memory.readImage_size _ _ _) observations
    (fieldCount.trans captureCount.symm) origins placement inputs

  have leaves : ∀ offset child, (offset,child) ∈ fields → ∃ ty layout, child = .leaf ty layout := by
    intro offset child member
    have typed : child.ty ∈ binding.nominal.captures := by
      rw [← inputBindings.1]
      exact List.mem_map.mpr ⟨(offset,child),member,rfl⟩
    exact leafQueries binding.nominal binding.nominalSource child.ty typed child (queries offset child member).1
  have covered := AggregateMemory.capture_leaf_coverage model order storage.size fields captures image encoded imageSize
    (after.memory.readImage address storage.size) (Memory.readImage_size _ _ _) observations placement leaves
  have allocations : after.memory.allocations = before.memory.allocations := by
    rw [changed]
    cases image.unwritten <;> rfl
  have loadAccess := access_same_allocations model "Store" "Load" address allocation storage.size alignment
    before after allocations accessed
  have loadAlignment := alignment_same_operation "Store" "Load" storage.alignment align alignment alignmentRun
  refine ⟨binding,.typedClosure closure binding.target.value outputs,?_,?_⟩
  · rw [pointed]
    exact prepared_load_of_checks source model roots order closure strict align after binding storage fields
      alignment address allocation outputs bindingModel bindingSource size alignedShape captureRun loadAlignment loadAccess covered decoded
  · refine ⟨captures,outputs,?_,rfl,related⟩
    rw [nominalSame,targetSame]


/-- Carry actual Store/readback into a source call frame that preserves the
complete Memory, including provenance/lifetimes and unwritten metadata. This
does not assert that an arbitrary callee preserves it. -/
theorem prepared_store_load_observer (source : TrustIrEval.Module) (model : ByteModel)
    (roots : List Ty) (order : FunctionAddressOrder) (closure nominal : ClosureTyId)
    (target : FuncId) (captures : List Value) (pointer : Value) (strict : Bool)
    (align : Option Nat) (before after observer : MachineState)
    (sameMemory : observer.memory = after.memory)
    (admitted : CaptureReadbackInputs source model roots order after.memory closure captures)
    (leafQueries : CaptureLeafQueries source model roots closure)
    (run : Sem.run (storeValue (prepare source model roots) order closure pointer
      (.typedClosure nominal target captures) strict align model) before = .ok ((),after)) :
    ∃ (binding : TrustIrEval.ClosureStorage.Binding source closure) (output : Value),
      Sem.run (loadValue (prepare source model roots) order closure pointer strict align model) observer = .ok (output,observer) ∧
      ValueReadback source closure binding model observer.memory (.typedClosure nominal target captures) output := by
  obtain ⟨binding,output,loaded,related⟩ := prepared_store_load_readback source model roots order closure nominal target
    captures pointer strict align before after admitted leafQueries run
  refine ⟨binding,output,prepared_load_same_memory source model roots order closure pointer strict align after observer output sameMemory loaded,?_⟩
  rw [sameMemory]
  exact related


end TrustIr.OriginalClosureMemory

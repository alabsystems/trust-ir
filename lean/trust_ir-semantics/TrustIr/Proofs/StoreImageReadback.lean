-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.ScalarLoadExecution
import TrustIr.Proofs.SourceRecursiveReadback

namespace TrustIr

theorem Memory.recordUnwritten_bytes (memory : Memory) (allocation : AllocId) (address : Nat)
    (lanes : List (Nat × Nat)) (query : Nat) :
    (memory.recordUnwritten allocation address lanes).bytes query = memory.bytes query := by
  cases lanes <;> rfl

/-- Every logical byte, including out-of-range observations, of the actual
    post-write snapshot agrees with the written image. No compact storage
    representation equality or materialization is assumed. -/
theorem Memory.readImage_after_write_record (memory : Memory) (allocation : AllocId) (address : Nat)
    (image : ByteImage) (lanes : List (Nat × Nat)) (index : Nat) :
    (((memory.writeImage address image).recordUnwritten allocation address lanes).readImage address image.size).get index =
      image.get index := by
  by_cases inside : index < image.size
  · rw [Memory.readImage_get _ _ _ _ inside,Memory.recordUnwritten_bytes,
      Memory.bytes_writeImage_inside memory address index image inside]
  · rw [ByteImage.get_outside _ index (by simpa using Nat.le_of_not_gt inside),
      ByteImage.get_outside image index (Nat.le_of_not_gt inside)]

namespace AggregateMemory

theorem ReadbackInput.not_poison {model : ByteModel} {order : FunctionAddressOrder} {memory : Memory}
    {plan : Plan} {input : Value} (admitted : ReadbackInput model order memory plan input) :
    input.isPoison = false := by
  cases admitted with
  | scalar scalar => cases scalar <;> rfl
  | function function => cases function <;> rfl
  | fields => rfl
  | array => rfl
  | enumeration => rfl

theorem StoreImageAccepted.ordinary_encode {model : ByteModel} {order : FunctionAddressOrder}
    {ty : Ty} {plan : Plan} {input : Value} {image : Image}
    (accepted : StoreImageAccepted model order ty plan input image)
    (clean : input.isPoison = false) (clear : carriesUnwritten input = false) :
    encode model order plan input false = .ok image := by
  cases input
  case «partial» bytes => cases clean
  case undef ty => cases clean
  all_goals simpa only [StoreImageAccepted,clear] using accepted

/-- Actual Store execution supplies the image and its exact subsequent memory
    observations, for ordinary, partial and poison stores alike. -/
theorem storeValue_success_image_bytes (service : Service) (order : FunctionAddressOrder) (ty : Ty)
    (pointer input : Value) (strict : Bool) (align : Option Nat) (model : ByteModel)
    (before after : MachineState)
    (run : Sem.run (storeValue service order ty pointer input strict align model) before = .ok ((),after)) :
    ∃ plan address allocation image,
      service.query ty = .ok plan ∧ pointer = .ptr address (some allocation) ∧
      StoreImageAccepted model order ty plan input image ∧ image.bytes.size = plan.layout.size ∧
      ∀ index, (after.memory.readImage address plan.layout.size).get index = image.bytes.get index := by
  obtain ⟨_clean,plan,alignment,address,allocation,image,_target,query,_aligned,pointerShape,_accessed,accepted,extent,rfl⟩ :=
    storeValue_success_steps service order ty pointer input strict align model before after run
  refine ⟨plan,address,allocation,image,query,pointerShape,accepted,extent,?_⟩
  intro index
  rw [← extent]
  exact Memory.readImage_after_write_record before.memory allocation address image.bytes image.unwritten index

/-- Source-admitted ordinary values read back from the snapshot actually
    produced by the original Store. Byte observations and encoding come from
    execution, not caller-supplied encoder/decoder outcomes. Admission is the
    existing receiving-memory value contract, not a decoded-result oracle. -/
theorem prepared_store_snapshot_readback (source : SourceLayout.Environment) (roots : List Ty)
    (order : FunctionAddressOrder) (ty : Ty) (pointer input : Value) (strict : Bool) (align : Option Nat)
    (model : ByteModel) (before after : MachineState)
    (admitted : ∀ plan, (prepare source roots).query ty = .ok plan → ReadbackInput model order after.memory plan input)
    (ready : ∀ plan, (prepare source roots).query ty = .ok plan → TopCharReady plan input)
    (clear : carriesUnwritten input = false)
    (run : Sem.run (storeValue (prepare source roots) order ty pointer input strict align model) before = .ok ((),after)) :
    ∃ plan address allocation output,
      (prepare source roots).query ty = .ok plan ∧ pointer = .ptr address (some allocation) ∧
      decode model order after.memory plan (after.memory.readImage address plan.layout.size) = .ok output ∧
      ValueReadback model after.memory input output := by
  obtain ⟨plan,address,allocation,image,query,pointerShape,accepted,_extent,bytes⟩ :=
    storeValue_success_image_bytes (prepare source roots) order ty pointer input strict align model before after run
  have typed := admitted plan query
  have encoded := accepted.ordinary_encode typed.not_poison clear
  obtain ⟨output,decoded,related⟩ := typed.top_readback source
    (prepared_plan_origin source roots ty plan query).own image encoded
    (after.memory.readImage address plan.layout.size) (Memory.readImage_size _ _ _) bytes (ready plan query)
  exact ⟨plan,address,allocation,output,query,pointerShape,decoded,related⟩

end AggregateMemory

theorem stepStore_descriptor_image_bytes (ctx : EvalContext) (ty : Ty) (pointer input : ValueId)
    (strict : Bool) (align : Option Nat) (service : AggregateMemory.Service)
    (selected : ctx.memoryRoute ty = .descriptor service) (before after : MachineState) (result : InstrResult)
    (run : Sem.run (stepInstWithContext ctx (.Store ty pointer input strict align)) before = .ok (result,after)) :
    result = .value none ∧ ∃ heldPointer heldInput plan address allocation image,
      before.lookupValue pointer = some heldPointer ∧ before.lookupValue input = some heldInput ∧
      service.query ty = .ok plan ∧ heldPointer = .ptr address (some allocation) ∧
      AggregateMemory.StoreImageAccepted ctx.byteModel ctx.functionOrder ty plan heldInput image ∧
      image.bytes.size = plan.layout.size ∧
      ∀ index, (after.memory.readImage address plan.layout.size).get index = image.bytes.get index := by
  obtain ⟨same,heldPointer,heldInput,pointerFound,inputFound,executed⟩ :=
    stepStore_descriptor_execution ctx ty pointer input strict align service selected before after result run
  obtain ⟨plan,address,allocation,image,query,pointerShape,accepted,extent,bytes⟩ :=
    AggregateMemory.storeValue_success_image_bytes service ctx.functionOrder ty heldPointer heldInput strict align ctx.byteModel before after executed
  exact ⟨same,heldPointer,heldInput,plan,address,allocation,image,pointerFound,inputFound,query,pointerShape,accepted,extent,bytes⟩

theorem stepStore_prepared_snapshot_readback (ctx : EvalContext) (source : SourceLayout.Environment) (roots : List Ty)
    (ty : Ty) (pointer input : ValueId) (strict : Bool) (align : Option Nat)
    (selected : ctx.memoryRoute ty = .descriptor (AggregateMemory.prepare source roots))
    (before after : MachineState) (result : InstrResult)
    (admitted : ∀ heldInput, before.lookupValue input = some heldInput → ∀ plan,
      (AggregateMemory.prepare source roots).query ty = .ok plan →
        AggregateMemory.ReadbackInput ctx.byteModel ctx.functionOrder after.memory plan heldInput)
    (ready : ∀ heldInput, before.lookupValue input = some heldInput → ∀ plan,
      (AggregateMemory.prepare source roots).query ty = .ok plan → AggregateMemory.TopCharReady plan heldInput)
    (clear : ∀ heldInput, before.lookupValue input = some heldInput → AggregateMemory.carriesUnwritten heldInput = false)
    (run : Sem.run (stepInstWithContext ctx (.Store ty pointer input strict align)) before = .ok (result,after)) :
    result = .value none ∧ ∃ heldPointer heldInput plan address allocation output,
      before.lookupValue pointer = some heldPointer ∧ before.lookupValue input = some heldInput ∧
      (AggregateMemory.prepare source roots).query ty = .ok plan ∧ heldPointer = .ptr address (some allocation) ∧
      AggregateMemory.decode ctx.byteModel ctx.functionOrder after.memory plan
        (after.memory.readImage address plan.layout.size) = .ok output ∧
      AggregateMemory.ValueReadback ctx.byteModel after.memory heldInput output := by
  obtain ⟨same,heldPointer,heldInput,pointerFound,inputFound,executed⟩ :=
    stepStore_descriptor_execution ctx ty pointer input strict align _ selected before after result run
  obtain ⟨plan,address,allocation,output,query,pointerShape,decoded,related⟩ :=
    AggregateMemory.prepared_store_snapshot_readback source roots ctx.functionOrder ty heldPointer heldInput strict align
      ctx.byteModel before after (admitted heldInput inputFound) (ready heldInput inputFound) (clear heldInput inputFound) executed
  exact ⟨same,heldPointer,heldInput,plan,address,allocation,output,pointerFound,inputFound,query,pointerShape,decoded,related⟩

end TrustIr

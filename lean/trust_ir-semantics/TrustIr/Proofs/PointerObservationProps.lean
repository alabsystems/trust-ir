-- Copyright 2026 Andrew Yates
-- Licensed under the Apache License, Version 2.0

import TrustIr.Proofs.IntResidue
import TrustIr.Proofs.MemorySafety
import TrustIr.Proofs.FunctionMemoryProps

namespace TrustIr

/-- Complete result of numeric pointer exposure, including width errors and
    overflow. Successful results use the shared residue representation. -/
theorem bindPointerInteger_run (op : String) (ty : Ty) (address : Nat)
    (model : ByteModel) (state : MachineState) :
    Sem.run (Sem.bindPointerInteger op ty address model) state =
      match getTyWidth ty model with
      | .error error => .error error
      | .ok width =>
        if address < model.addressLimit then
          .ok (state.bindValue (Value.intAt width (Int.ofNat address)))
        else .error (.ub s!"{op}: pointer address exceeds the target width") := by
  unfold Sem.bindPointerInteger
  cases getTyWidth ty model with
  | error error => simp only [Sem.run, sr_bind, sr_throw, Except.bind]
  | ok width =>
    simp only [pure_bind]
    split <;> rfl

/-- A successful exposure cannot leave a noncanonical integer in SSA. -/
theorem bindPointerInteger_success (op : String) (ty : Ty) (address : Nat)
    (model : ByteModel) (state finalState : MachineState) (id : ValueId)
    (h : Sem.run (Sem.bindPointerInteger op ty address model) state = .ok (id, finalState)) :
    address < model.addressLimit ∧
      ∃ width raw, getTyWidth ty model = .ok width ∧
        finalState.lookupValue id = some (.int width raw) ∧
        0 ≤ raw ∧ raw < 2 ^ width := by
  trustIrCompilerProof {
    rw [bindPointerInteger_run] at h
    cases hw : getTyWidth ty model with
    | error error => simp only [hw] at h
    | ok width =>
      simp only [hw] at h
      by_cases bound : address < model.addressLimit
      · simp only [bound, if_pos] at h
        have pair := Except.ok.inj h
        have hi : (state.bindValue (Value.intAt width (Int.ofNat address))).fst = id :=
          congrArg Prod.fst pair
        have hs : (state.bindValue (Value.intAt width (Int.ofNat address))).snd = finalState :=
          congrArg Prod.snd pair
        refine ⟨bound, width, truncateUnsigned (Int.ofNat address) width, rfl, ?_,
          truncateUnsigned_nonneg _ _, truncateUnsigned_lt _ _⟩
        rw [← hs, ← hi]
        simp [MachineState.bindValue, MachineState.lookupValue, ValueMap.get,
          ValueMap.set, Value.intAt]
      · simp only [bound, if_neg] at h
        cases h
  } {
    rw [bindPointerInteger_run] at h
    cases hw : getTyWidth ty model with
    | error error => simp [hw] at h
    | ok width =>
      simp only [hw] at h
      by_cases bound : address < model.addressLimit
      · simp only [bound, if_pos] at h
        have pair := Except.ok.inj h
        have hi : (state.bindValue (Value.intAt width (Int.ofNat address))).fst = id :=
          congrArg Prod.fst pair
        have hs : (state.bindValue (Value.intAt width (Int.ofNat address))).snd = finalState :=
          congrArg Prod.snd pair
        refine ⟨bound, width, truncateUnsigned (Int.ofNat address) width, rfl, ?_,
          truncateUnsigned_nonneg _ _, truncateUnsigned_lt _ _⟩
        rw [← hs, ← hi]
        simp [MachineState.bindValue, MachineState.lookupValue, ValueMap.get,
          ValueMap.set, Value.intAt]
      · simp only [bound, if_neg] at h
        cases h
  }

/-- A successful pointer image proves the physical address fits; dead
    allocations are not excluded by this value-level observation. -/
theorem encodeMemoryAt_pointer_address_bound (model : ByteModel) (ty : Ty)
    (address : Nat) (provenance : Option AllocId) (bytes : List UInt8)
    (h : encodeMemoryAt model ty (.ptr address provenance) = .ok bytes) :
    address < model.addressLimit := by
  by_cases bound : address < model.addressLimit
  · exact bound
  · simp [encodeMemoryAt, checkPointerImageWords, bound, Except.bind] at h

/-- Both pointer-valued lanes must fit before a fat-pointer image exists. -/
theorem encodeMemoryAt_fat_pointer_address_bounds (model : ByteModel) (ty : Ty)
    (data metadata : Nat) (dataProvenance metadataProvenance : Option AllocId)
    (bytes : List UInt8)
    (h : encodeMemoryAt model ty (.fatPtr data dataProvenance
      (.ptr metadata metadataProvenance)) = .ok bytes) :
    data < model.addressLimit ∧ metadata < model.addressLimit := by
  by_cases hd : data < model.addressLimit
  · refine ⟨hd, ?_⟩
    by_cases hm : metadata < model.addressLimit
    · exact hm
    · simp [encodeMemoryAt, checkPointerImageWords, hd, hm, bind, Except.bind, SeqRight.seqRight] at h
  · simp [encodeMemoryAt, checkPointerImageWords, hd, bind, Except.bind, SeqRight.seqRight] at h

/-- A bounded physical data address is encoded at the actual target width. -/
theorem encodeMemory_pointer_word (model : ByteModel) (order : FunctionAddressOrder) (ty : Ty)
    (address : Nat) (provenance : Option AllocId) (pointer : ty.isPointerLike = true)
    (bound : address < model.addressLimit) :
    encodeMemoryWithFunctions model order ty (.ptr address provenance) =
      .ok (encodeIntBytes (Int.ofNat address) model.pointerBytes) := by
  cases model <;> cases ty <;> simp only [Ty.isPointerLike,Ty.isReference] at pointer <;> try cases pointer
  all_goals simp [encodeMemoryWithFunctions,encodeMemoryAt,checkPointerImageWords,bound,
    encodeValueAt,encodeTypedAtModel,fatPtrStoreValueValidAtModel,encodeValueAtModel,encodePointerWord,
    encodeValue,Bind.bind,Except.bind,Pure.pure,Except.pure]
  all_goals rfl

/-- Data-pointer bytes recover provenance by address in the receiving memory;
stored provenance and allocation liveness are not decoding premises. -/
theorem decodeMemory_pointer_bytes (model : ByteModel) (order : FunctionAddressOrder) (memory : Memory)
    (ty : Ty) (bytes : List UInt8) (pointer : ty.isPointerLike = true) (size : bytes.length = model.pointerBytes) :
    decodeMemoryWithFunctions model order memory ty bytes = .ok (memory.resolveAddr (decodeIntBytes bytes)) := by
  cases model <;> cases ty <;> simp only [Ty.isPointerLike,Ty.isReference] at pointer <;> try cases pointer
  all_goals simp only [ByteModel.pointerBytes] at size
  all_goals simp only [decodeMemoryWithFunctions,decodeMemoryAt,decodeValueAt,decodeTypedAtModel,
    decodeImageAt,decodeImageAtModel,decodeValueAtModel,decodePointerWord,decodeValue,Ty.isFloat,
    size,ByteModel.pointerBytes,beq_self_eq_true,ite_true,Bool.false_eq_true,ite_false]
  all_goals by_cases zero : decodeIntBytes bytes = 0 <;>
    simp [zero,Memory.resolveDecoded,Memory.resolveAddr,Bind.bind,Except.bind,Pure.pure,Except.pure]

/-- All six thin-pointer families preserve the address and recover provenance. -/
theorem pointer_memory_roundtrip (model : ByteModel) (order : FunctionAddressOrder) (memory : Memory)
    (ty : Ty) (address : Nat) (provenance : Option AllocId) (pointer : ty.isPointerLike = true)
    (bound : address < model.addressLimit) :
    (encodeMemoryWithFunctions model order ty (.ptr address provenance)).bind
      (decodeMemoryWithFunctions model order memory ty) = .ok (memory.resolveAddr address) := by
  rw [encodeMemory_pointer_word model order ty address provenance pointer bound]
  simp only [Except.bind]
  rw [decodeMemory_pointer_bytes model order memory ty _ pointer (encodeIntBytes_length _ _),
    decode_encode_function_address model address bound]

/-- A physical address outside the target word is refused before truncation. -/
theorem pointer_memory_refuses_overflow (model : ByteModel) (order : FunctionAddressOrder) (ty : Ty)
    (address : Nat) (provenance : Option AllocId) (pointer : ty.isPointerLike = true)
    (bound : ¬ address < model.addressLimit) :
    encodeMemoryWithFunctions model order ty (.ptr address provenance) =
      .error (.ub "Store: pointer address exceeds the target width") := by
  cases ty <;> simp only [Ty.isPointerLike,Ty.isReference] at pointer <;> try cases pointer
  all_goals simp [encodeMemoryWithFunctions,encodeMemoryAt,checkPointerImageWords,bound,Bind.bind,Except.bind]

/-- Complete thin-pointer byte-codec result, including the original range refusal. -/
theorem pointer_memory_result (model : ByteModel) (order : FunctionAddressOrder) (memory : Memory)
    (ty : Ty) (address : Nat) (provenance : Option AllocId) (pointer : ty.isPointerLike = true) :
    (encodeMemoryWithFunctions model order ty (.ptr address provenance)).bind
      (decodeMemoryWithFunctions model order memory ty) =
      if address < model.addressLimit then .ok (memory.resolveAddr address)
      else .error (.ub "Store: pointer address exceeds the target width") := by
  by_cases bound : address < model.addressLimit
  · rw [if_pos bound]
    exact pointer_memory_roundtrip model order memory ty address provenance pointer bound
  · rw [if_neg bound,pointer_memory_refuses_overflow model order ty address provenance pointer bound]
    rfl

/-- The canonical null word round-trips at either target width. -/
theorem null_pointer_memory_roundtrip (model : ByteModel) (order : FunctionAddressOrder) (memory : Memory)
    (ty : Ty) (pointer : ty.isPointerLike = true) :
    (encodeMemoryWithFunctions model order ty .nullPtr).bind
      (decodeMemoryWithFunctions model order memory ty) = .ok .nullPtr := by
  trustIrCompilerProof {
    cases model <;> cases ty <;> simp only [Ty.isPointerLike,Ty.isReference] at pointer <;> try cases pointer
    all_goals rfl
  } {
    cases model <;> cases ty <;> simp only [Ty.isPointerLike,Ty.isReference] at pointer <;> try cases pointer
    all_goals trustIrReduce
  }

private theorem pointer_words_split (first second : List UInt8) :
    (first ++ second).take first.length = first ∧ (first ++ second).drop first.length = second := by
  induction first with
  | nil => exact ⟨rfl,rfl⟩
  | cons head tail ih =>
    simpa only [List.cons_append,List.length_cons,List.take,List.drop] using (And.intro (congrArg (head :: ·) ih.1) ih.2)

/-- Both physical lanes are decoded with the selected target width. Data and
vtable provenance are recovered independently from the receiving memory. -/
theorem decodeMemory_fat_pointer_words (model : ByteModel) (order : FunctionAddressOrder) (memory : Memory)
    (kind : FatPtrKind) (first second : List UInt8)
    (firstSize : first.length = model.pointerBytes) (secondSize : second.length = model.pointerBytes) :
    decodeMemoryWithFunctions model order memory (.FatPtr kind) (first ++ second) =
      let data := decodeIntBytes first
      let recovered := if data == 0 then none else memory.provenanceAt data
      match kind with
      | .Slice _ | .Str | .ContainerLen =>
        .ok (.fatPtr data recovered (.int model.pointerBits (Int.ofNat (decodeIntBytes second))))
      | .TraitObject _ | .ContainerVtable =>
        .ok (.fatPtr data recovered (memory.resolveAddr (decodeIntBytes second))) := by
  trustIrCompilerProof {
    have take := (pointer_words_split first second).1
    have drop := (pointer_words_split first second).2
    rw [firstSize] at take drop
    cases model <;> cases kind
    all_goals simp only [ByteModel.pointerBytes] at firstSize secondSize take drop
    all_goals simp only [decodeMemoryWithFunctions,decodeMemoryAt,decodeValueAt,decodeTypedAtModel,
      decodeImageAt,decodeImageAtModel,decodeValueAtModel,decodeValue,Ty.isFloat,ByteModel.pointerBytes,
      List.length_append,firstSize,secondSize,beq_self_eq_true,ite_true,Bool.false_eq_true,ite_false,take,drop]
    all_goals by_cases zero : decodeIntBytes second = 0 <;>
      simp [zero,Memory.resolveDecoded,Memory.resolveAddr,Bind.bind,Except.bind,Pure.pure,Except.pure]
    all_goals rfl
  } {
    have take := (pointer_words_split first second).1
    have drop := (pointer_words_split first second).2
    rw [firstSize] at take drop
    cases model <;> cases kind
    all_goals simp only [ByteModel.pointerBytes] at firstSize secondSize take drop
    all_goals simp only [decodeMemoryWithFunctions,decodeMemoryAt,decodeValueAt,decodeTypedAtModel,
      decodeImageAt,decodeImageAtModel,decodeValueAtModel,decodeValue,Ty.isFloat,ByteModel.pointerBytes,
      List.length_append,firstSize,secondSize,beq_self_eq_true,ite_true,Bool.false_eq_true,ite_false,take,drop]
    all_goals by_cases zero : decodeIntBytes second = 0 <;>
      simp [zero,Memory.resolveDecoded,Memory.resolveAddr,Bind.bind,Except.bind,Pure.pure,Except.pure]
    all_goals trustIrReduce
  }

/-- Length metadata is a target-width integer residue; it is never silently
interpreted as a vtable pointer. The legacy metadata selector classifies the
family; the actual carrier width below comes from the selected model. -/
theorem encodeMemory_fat_length_words (model : ByteModel) (order : FunctionAddressOrder)
    (kind : FatPtrKind) (data : Nat) (provenance : Option AllocId) (raw : Int)
    (lengthLane : kind.metadataTy = .U64) (bound : data < model.addressLimit) :
    encodeMemoryWithFunctions model order (.FatPtr kind) (.fatPtr data provenance (.int model.pointerBits raw)) =
      .ok (encodeIntBytes (Int.ofNat data) model.pointerBytes ++
        encodeIntBytes (truncateUnsigned raw model.pointerBits) model.pointerBytes) := by
  trustIrCompilerProof {
    cases model <;> cases kind <;> simp only [FatPtrKind.metadataTy] at lengthLane <;> try cases lengthLane
    all_goals simp [encodeMemoryWithFunctions,encodeMemoryAt,checkPointerImageWords,bound,
      encodeValueAt,encodeTypedAtModel,fatPtrStoreValueValidAtModel,metadataInhabitsAtModel,
      FatPtrKind.metadataTyAtModel,ByteModel.lengthTy,ByteModel.pointerBits,ByteModel.pointerBytes,
      encodeValueAtModel,encodeMetadataWord,encodePointerWord,encodeValue,integer_encoding_residue,truncateUnsigned,
      Bind.bind,Except.bind,Pure.pure,Except.pure]
    all_goals rfl
  } {
    cases model <;> cases kind <;> simp only [FatPtrKind.metadataTy] at lengthLane <;> try cases lengthLane
    all_goals simp [encodeMemoryWithFunctions,encodeMemoryAt,checkPointerImageWords,bound,
      encodeValueAt,encodeTypedAtModel,fatPtrStoreValueValidAtModel,metadataInhabitsAtModel,
      FatPtrKind.metadataTyAtModel,ByteModel.lengthTy,ByteModel.pointerBits,ByteModel.pointerBytes,
      encodeValueAtModel,encodeMetadataWord,encodePointerWord,encodeValue,integer_encoding_residue,truncateUnsigned,
      Bind.bind,Except.bind,Pure.pure,Except.pure]
    all_goals trustIrReduce
  }

theorem fat_length_memory_roundtrip (model : ByteModel) (order : FunctionAddressOrder) (memory : Memory)
    (kind : FatPtrKind) (data : Nat) (provenance : Option AllocId) (raw : Int)
    (lengthLane : kind.metadataTy = .U64) (bound : data < model.addressLimit) :
    (encodeMemoryWithFunctions model order (.FatPtr kind) (.fatPtr data provenance (.int model.pointerBits raw))).bind
      (decodeMemoryWithFunctions model order memory (.FatPtr kind)) =
      .ok (.fatPtr data (if data == 0 then none else memory.provenanceAt data)
        (Value.intAt model.pointerBits raw)) := by
  rw [encodeMemory_fat_length_words model order kind data provenance raw lengthLane bound]
  simp only [Except.bind]
  rw [decodeMemory_fat_pointer_words model order memory kind _ _ (encodeIntBytes_length _ _) (encodeIntBytes_length _ _)]
  rw [decode_encode_function_address model data bound]
  have decoded : Int.ofNat (decodeIntBytes (encodeIntBytes (truncateUnsigned raw model.pointerBits) model.pointerBytes)) =
      truncateUnsigned raw model.pointerBits := decode_encode_integer_residue raw model.pointerBytes
  cases kind <;> simp only [FatPtrKind.metadataTy] at lengthLane <;> try cases lengthLane
  all_goals simp only [decoded,Value.intAt]

/-- Vtable metadata is a checked address word, separate from the data word. -/
theorem encodeMemory_fat_vtable_words (model : ByteModel) (order : FunctionAddressOrder)
    (kind : FatPtrKind) (data metadata : Nat) (dataProv metadataProv : Option AllocId)
    (pointerLane : kind.metadataTy = .Ptr) (dataBound : data < model.addressLimit)
    (metaBound : metadata < model.addressLimit) :
    encodeMemoryWithFunctions model order (.FatPtr kind) (.fatPtr data dataProv (.ptr metadata metadataProv)) =
      .ok (encodeIntBytes (Int.ofNat data) model.pointerBytes ++ encodeIntBytes (Int.ofNat metadata) model.pointerBytes) := by
  cases model <;> cases kind <;> simp only [FatPtrKind.metadataTy] at pointerLane <;> try cases pointerLane
  all_goals simp [encodeMemoryWithFunctions,encodeMemoryAt,checkPointerImageWords,dataBound,metaBound,
    encodeValueAt,encodeTypedAtModel,fatPtrStoreValueValidAtModel,metadataInhabitsAtModel,
    FatPtrKind.metadataTyAtModel,ByteModel.lengthTy,ByteModel.pointerBits,ByteModel.pointerBytes,
    encodeValueAtModel,encodeMetadataWord,encodePointerWord,encodeValue,
    Bind.bind,Except.bind,Pure.pure,Except.pure]

theorem fat_vtable_memory_roundtrip (model : ByteModel) (order : FunctionAddressOrder) (memory : Memory)
    (kind : FatPtrKind) (data metadata : Nat) (dataProv metadataProv : Option AllocId)
    (pointerLane : kind.metadataTy = .Ptr) (dataBound : data < model.addressLimit)
    (metaBound : metadata < model.addressLimit) :
    (encodeMemoryWithFunctions model order (.FatPtr kind) (.fatPtr data dataProv (.ptr metadata metadataProv))).bind
      (decodeMemoryWithFunctions model order memory (.FatPtr kind)) =
      .ok (.fatPtr data (if data == 0 then none else memory.provenanceAt data) (memory.resolveAddr metadata)) := by
  trustIrCompilerProof {
    rw [encodeMemory_fat_vtable_words model order kind data metadata dataProv metadataProv pointerLane dataBound metaBound]
    simp only [Except.bind]
    rw [decodeMemory_fat_pointer_words model order memory kind _ _ (encodeIntBytes_length _ _) (encodeIntBytes_length _ _),
      decode_encode_function_address model data dataBound,decode_encode_function_address model metadata metaBound]
    cases kind <;> simp only [FatPtrKind.metadataTy] at pointerLane <;> try cases pointerLane
    all_goals rfl
  } {
    rw [encodeMemory_fat_vtable_words model order kind data metadata dataProv metadataProv pointerLane dataBound metaBound]
    simp only [Except.bind]
    rw [decodeMemory_fat_pointer_words model order memory kind _ _ (encodeIntBytes_length _ _) (encodeIntBytes_length _ _),
      decode_encode_function_address model data dataBound,decode_encode_function_address model metadata metaBound]
    cases kind <;> simp only [FatPtrKind.metadataTy] at pointerLane <;> try cases pointerLane
    all_goals trustIrReduce
  }

/-- Null vtable metadata has the same physical zero word as a zero-address
pointer; readback is the canonical null metadata value. -/
theorem fat_null_metadata_image (model : ByteModel) (order : FunctionAddressOrder) (kind : FatPtrKind)
    (data : Nat) (provenance : Option AllocId) :
    encodeMemoryWithFunctions model order (.FatPtr kind) (.fatPtr data provenance .nullPtr) =
      encodeMemoryWithFunctions model order (.FatPtr kind) (.fatPtr data provenance (.ptr 0 none)) := by
  trustIrCompilerProof {
    have zero : 0 < model.addressLimit := by cases model <;> decide
    by_cases bound : data < model.addressLimit
    · cases model <;> cases kind <;>
        simp [encodeMemoryWithFunctions,encodeMemoryAt,checkPointerImageWords,bound,zero,
          encodeValueAt,encodeTypedAtModel,fatPtrStoreValueValidAtModel,metadataInhabitsAtModel,
          FatPtrKind.metadataTyAtModel,ByteModel.pointerBytes,encodeValueAtModel,encodeMetadataWord,
          encodePointerWord,encodeValue,Bind.bind,Except.bind,Pure.pure,Except.pure]
      all_goals rfl
    · simp [encodeMemoryWithFunctions,encodeMemoryAt,checkPointerImageWords,bound,Bind.bind,Except.bind]
  } {
    have zero : 0 < model.addressLimit := by cases model <;> decide
    by_cases bound : data < model.addressLimit
    · cases model <;> cases kind <;>
        simp [encodeMemoryWithFunctions,encodeMemoryAt,checkPointerImageWords,bound,zero,
          encodeValueAt,encodeTypedAtModel,fatPtrStoreValueValidAtModel,metadataInhabitsAtModel,
          FatPtrKind.metadataTyAtModel,ByteModel.pointerBytes,encodeValueAtModel,encodeMetadataWord,
          encodePointerWord,encodeValue,Bind.bind,Except.bind,Pure.pure,Except.pure]
      all_goals trustIrReduce
    · simp [encodeMemoryWithFunctions,encodeMemoryAt,checkPointerImageWords,bound,Bind.bind,Except.bind]
  }

theorem fat_null_vtable_memory_roundtrip (model : ByteModel) (order : FunctionAddressOrder) (memory : Memory)
    (kind : FatPtrKind) (data : Nat) (provenance : Option AllocId)
    (pointerLane : kind.metadataTy = .Ptr) (bound : data < model.addressLimit) :
    (encodeMemoryWithFunctions model order (.FatPtr kind) (.fatPtr data provenance .nullPtr)).bind
      (decodeMemoryWithFunctions model order memory (.FatPtr kind)) =
      .ok (.fatPtr data (if data == 0 then none else memory.provenanceAt data) .nullPtr) := by
  rw [fat_null_metadata_image]
  exact fat_vtable_memory_roundtrip model order memory kind data 0 provenance none pointerLane bound
    (by cases model <;> decide)

theorem fat_pointer_memory_refuses_data (model : ByteModel) (order : FunctionAddressOrder)
    (kind : FatPtrKind) (data : Nat) (provenance : Option AllocId) (metadata : Value)
    (bound : ¬ data < model.addressLimit) :
    encodeMemoryWithFunctions model order (.FatPtr kind) (.fatPtr data provenance metadata) =
      .error (.ub "Store: pointer address exceeds the target width") := by
  simp [encodeMemoryWithFunctions,encodeMemoryAt,checkPointerImageWords,bound,Bind.bind,Except.bind]

theorem fat_pointer_memory_refuses_vtable (model : ByteModel) (order : FunctionAddressOrder)
    (kind : FatPtrKind) (data metadata : Nat) (dataProv metadataProv : Option AllocId)
    (dataBound : data < model.addressLimit) (metaBound : ¬ metadata < model.addressLimit) :
    encodeMemoryWithFunctions model order (.FatPtr kind) (.fatPtr data dataProv (.ptr metadata metadataProv)) =
      .error (.ub "Store: pointer address exceeds the target width") := by
  simp [encodeMemoryWithFunctions,encodeMemoryAt,checkPointerImageWords,dataBound,metaBound,Bind.bind,Except.bind]

/-- Canonical length-lane values satisfy the actual aggregate store guard. -/
theorem fat_length_store_valid (model : ByteModel) (kind : FatPtrKind) (data : Nat)
    (provenance : Option AllocId) (raw : Int) (lengthLane : kind.metadataTy = .U64)
    (bound : data < model.addressLimit) :
    fatPtrStoreValueValidFor model (.FatPtr kind) (.fatPtr data provenance (.int model.pointerBits raw)) = true := by
  trustIrCompilerProof {
    cases model <;> cases kind <;> simp only [FatPtrKind.metadataTy] at lengthLane <;> try cases lengthLane
    all_goals simp [fatPtrStoreValueValidFor,fatPtrStoreValueValid,fatPtrStoreValueValidAtModel,
      metadataInhabits,metadataInhabitsAtModel,FatPtrKind.metadataTy,FatPtrKind.metadataTyAtModel,
      ByteModel.lengthTy,ByteModel.pointerBits,ByteModel.pointerBytes,bound]
    all_goals rfl
  } {
    cases model <;> cases kind <;> simp only [FatPtrKind.metadataTy] at lengthLane <;> try cases lengthLane
    all_goals simp [fatPtrStoreValueValidFor,fatPtrStoreValueValid,fatPtrStoreValueValidAtModel,
      metadataInhabits,metadataInhabitsAtModel,FatPtrKind.metadataTy,FatPtrKind.metadataTyAtModel,
      ByteModel.lengthTy,ByteModel.pointerBits,ByteModel.pointerBytes,bound]
    all_goals trustIrReduce
  }

theorem fat_vtable_store_valid (model : ByteModel) (kind : FatPtrKind) (data metadata : Nat)
    (dataProv metadataProv : Option AllocId) (pointerLane : kind.metadataTy = .Ptr)
    (dataBound : data < model.addressLimit) (metaBound : metadata < model.addressLimit) :
    fatPtrStoreValueValidFor model (.FatPtr kind) (.fatPtr data dataProv (.ptr metadata metadataProv)) = true := by
  cases model <;> cases kind <;> simp only [FatPtrKind.metadataTy] at pointerLane <;> try cases pointerLane
  all_goals simp [fatPtrStoreValueValidFor,fatPtrStoreValueValid,fatPtrStoreValueValidAtModel,
    metadataInhabits,metadataInhabitsAtModel,FatPtrKind.metadataTy,FatPtrKind.metadataTyAtModel,dataBound,metaBound]

/-- Bounded thin data-pointer leaves recover the receiving memory's
provenance, with source extent checked by the actual aggregate encoder. -/
theorem pointer_aggregate_leaf_roundtrip (model : ByteModel) (order : FunctionAddressOrder) (memory : Memory)
    (ty : Ty) (layout : MemoryTypeLayout) (address : Nat) (provenance : Option AllocId)
    (pointer : ty.isPointerLike = true) (bound : address < model.addressLimit)
    (extent : layout.size = model.pointerBytes) :
    (AggregateMemory.encode model order (.leaf ty layout) (.ptr address provenance) false).bind
      (fun image => AggregateMemory.decode model order memory (.leaf ty layout) image.bytes) =
      .ok (memory.resolveAddr address) := by
  have encoded := encodeMemory_pointer_word model order ty address provenance pointer bound
  have size := (encodeIntBytes_length (Int.ofNat address) model.pointerBytes).trans extent.symm
  rw [AggregateMemory.encode_pointer_leaf_of_memory model order ty layout _ _ pointer
    (Or.inl ⟨address,provenance,rfl⟩) size encoded]
  simp only [Except.bind]
  rw [AggregateMemory.decode_leaf_of_bytes model order memory ty layout _ size,
    decodeMemory_pointer_bytes model order memory ty _ pointer (encodeIntBytes_length _ _),
    decode_encode_function_address model address bound]

theorem null_pointer_aggregate_leaf_roundtrip (model : ByteModel) (order : FunctionAddressOrder) (memory : Memory)
    (ty : Ty) (layout : MemoryTypeLayout) (pointer : ty.isPointerLike = true)
    (extent : layout.size = model.pointerBytes) :
    (AggregateMemory.encode model order (.leaf ty layout) .nullPtr false).bind
      (fun image => AggregateMemory.decode model order memory (.leaf ty layout) image.bytes) = .ok .nullPtr := by
  trustIrCompilerProof {
    have encoded : encodeMemoryWithFunctions model order ty .nullPtr = .ok (List.replicate model.pointerBytes 0) := by
      cases model <;> cases ty <;> simp only [Ty.isPointerLike,Ty.isReference] at pointer <;> try cases pointer
      all_goals rfl
    have size := (List.length_replicate model.pointerBytes (0 : UInt8)).trans extent.symm
    rw [AggregateMemory.encode_pointer_leaf_of_memory model order ty layout _ _ pointer (Or.inr rfl) size encoded]
    simp only [Except.bind]
    rw [AggregateMemory.decode_leaf_of_bytes model order memory ty layout _ size]
    have run := null_pointer_memory_roundtrip model order memory ty pointer
    rw [encoded] at run
    exact run
  } {
    have encoded : encodeMemoryWithFunctions model order ty .nullPtr = .ok (List.replicate model.pointerBytes 0) := by
      cases model <;> cases ty <;> simp only [Ty.isPointerLike,Ty.isReference] at pointer <;> try cases pointer
      all_goals trustIrReduce
    have size := (List.length_replicate (n := model.pointerBytes) (a := (0 : UInt8))).trans extent.symm
    rw [AggregateMemory.encode_pointer_leaf_of_memory model order ty layout _ _ pointer (Or.inr rfl) size encoded]
    simp only [Except.bind]
    rw [AggregateMemory.decode_leaf_of_bytes model order memory ty layout _ size]
    have run := null_pointer_memory_roundtrip model order memory ty pointer
    rw [encoded] at run
    exact run
  }

theorem fat_length_aggregate_leaf_roundtrip (model : ByteModel) (order : FunctionAddressOrder) (memory : Memory)
    (kind : FatPtrKind) (layout : MemoryTypeLayout) (data : Nat) (provenance : Option AllocId) (raw : Int)
    (lengthLane : kind.metadataTy = .U64) (bound : data < model.addressLimit)
    (extent : layout.size = 2 * model.pointerBytes) :
    (AggregateMemory.encode model order (.leaf (.FatPtr kind) layout)
      (.fatPtr data provenance (.int model.pointerBits raw)) false).bind
      (fun image => AggregateMemory.decode model order memory (.leaf (.FatPtr kind) layout) image.bytes) =
      .ok (.fatPtr data (if data == 0 then none else memory.provenanceAt data) (Value.intAt model.pointerBits raw)) := by
  have encoded := encodeMemory_fat_length_words model order kind data provenance raw lengthLane bound
  have size : (encodeIntBytes (Int.ofNat data) model.pointerBytes ++
      encodeIntBytes (truncateUnsigned raw model.pointerBits) model.pointerBytes).length = layout.size := by
    rw [List.length_append,encodeIntBytes_length,encodeIntBytes_length,extent]
    omega
  rw [AggregateMemory.encode_fat_pointer_leaf_of_memory model order kind layout data provenance _ _
    (fat_length_store_valid model kind data provenance raw lengthLane bound) size encoded]
  simp only [Except.bind]
  rw [AggregateMemory.decode_leaf_of_bytes model order memory (.FatPtr kind) layout _ size]
  have run := fat_length_memory_roundtrip model order memory kind data provenance raw lengthLane bound
  rw [encoded] at run
  exact run

theorem fat_vtable_aggregate_leaf_roundtrip (model : ByteModel) (order : FunctionAddressOrder) (memory : Memory)
    (kind : FatPtrKind) (layout : MemoryTypeLayout) (data metadata : Nat) (dataProv metadataProv : Option AllocId)
    (pointerLane : kind.metadataTy = .Ptr) (dataBound : data < model.addressLimit)
    (metaBound : metadata < model.addressLimit) (extent : layout.size = 2 * model.pointerBytes) :
    (AggregateMemory.encode model order (.leaf (.FatPtr kind) layout)
      (.fatPtr data dataProv (.ptr metadata metadataProv)) false).bind
      (fun image => AggregateMemory.decode model order memory (.leaf (.FatPtr kind) layout) image.bytes) =
      .ok (.fatPtr data (if data == 0 then none else memory.provenanceAt data) (memory.resolveAddr metadata)) := by
  have encoded := encodeMemory_fat_vtable_words model order kind data metadata dataProv metadataProv pointerLane dataBound metaBound
  have size : (encodeIntBytes (Int.ofNat data) model.pointerBytes ++
      encodeIntBytes (Int.ofNat metadata) model.pointerBytes).length = layout.size := by
    rw [List.length_append,encodeIntBytes_length,encodeIntBytes_length,extent]
    omega
  rw [AggregateMemory.encode_fat_pointer_leaf_of_memory model order kind layout data dataProv _ _
    (fat_vtable_store_valid model kind data metadata dataProv metadataProv pointerLane dataBound metaBound) size encoded]
  simp only [Except.bind]
  rw [AggregateMemory.decode_leaf_of_bytes model order memory (.FatPtr kind) layout _ size]
  have run := fat_vtable_memory_roundtrip model order memory kind data metadata dataProv metadataProv pointerLane dataBound metaBound
  rw [encoded] at run
  exact run

theorem fat_null_store_valid (model : ByteModel) (kind : FatPtrKind) (data : Nat)
    (provenance : Option AllocId) (pointerLane : kind.metadataTy = .Ptr) (bound : data < model.addressLimit) :
    fatPtrStoreValueValidFor model (.FatPtr kind) (.fatPtr data provenance .nullPtr) = true := by
  cases model <;> cases kind <;> simp only [FatPtrKind.metadataTy] at pointerLane <;> try cases pointerLane
  all_goals simp [fatPtrStoreValueValidFor,fatPtrStoreValueValid,fatPtrStoreValueValidAtModel,
    metadataInhabits,metadataInhabitsAtModel,FatPtrKind.metadataTy,FatPtrKind.metadataTyAtModel,bound]

theorem fat_null_vtable_aggregate_leaf_roundtrip (model : ByteModel) (order : FunctionAddressOrder) (memory : Memory)
    (kind : FatPtrKind) (layout : MemoryTypeLayout) (data : Nat) (provenance : Option AllocId)
    (pointerLane : kind.metadataTy = .Ptr) (bound : data < model.addressLimit)
    (extent : layout.size = 2 * model.pointerBytes) :
    (AggregateMemory.encode model order (.leaf (.FatPtr kind) layout) (.fatPtr data provenance .nullPtr) false).bind
      (fun image => AggregateMemory.decode model order memory (.leaf (.FatPtr kind) layout) image.bytes) =
      .ok (.fatPtr data (if data == 0 then none else memory.provenanceAt data) .nullPtr) := by
  have zero : 0 < model.addressLimit := by cases model <;> decide
  have encoded := encodeMemory_fat_vtable_words model order kind data 0 provenance none pointerLane bound zero
  rw [← fat_null_metadata_image] at encoded
  have size : (encodeIntBytes (Int.ofNat data) model.pointerBytes ++ encodeIntBytes (Int.ofNat 0) model.pointerBytes).length = layout.size := by
    rw [List.length_append,encodeIntBytes_length,encodeIntBytes_length,extent]
    omega
  rw [AggregateMemory.encode_fat_pointer_leaf_of_memory model order kind layout data provenance _ _
    (fat_null_store_valid model kind data provenance pointerLane bound) size encoded]
  simp only [Except.bind]
  rw [AggregateMemory.decode_leaf_of_bytes model order memory (.FatPtr kind) layout _ size]
  have run := fat_null_vtable_memory_roundtrip model order memory kind data provenance pointerLane bound
  rw [encoded] at run
  exact run

namespace PointerCodecControls

private def oldAllocation : Allocation :=
  { id := ⟨7⟩, base := 1024, size := 8, alive := false, origin := .cleanHeap, requested := 8 }
private def newAllocation : Allocation :=
  { id := ⟨9⟩, base := 1032, size := 8, alive := true, origin := .rustHeap, requested := 8 }
private def deadMemory : Memory := { Memory.empty with allocations := [oldAllocation] }
private def boundaryMemory : Memory := { Memory.empty with allocations := [newAllocation,oldAllocation] }

theorem zero_pointer_canonicalizes (model : ByteModel) (order : FunctionAddressOrder) :
    (encodeMemoryWithFunctions model order .Ptr (.ptr 0 (some ⟨99⟩))).bind
      (decodeMemoryWithFunctions model order Memory.empty .Ptr) = .ok .nullPtr :=
  pointer_memory_roundtrip model order Memory.empty .Ptr 0 (some ⟨99⟩) rfl (by cases model <;> decide)

theorem forged_provenance_is_not_restored (model : ByteModel) (order : FunctionAddressOrder) :
    (encodeMemoryWithFunctions model order .Ptr (.ptr 1 (some ⟨99⟩))).bind
      (decodeMemoryWithFunctions model order Memory.empty .Ptr) = .ok (.ptr 1 none) :=
  pointer_memory_roundtrip model order Memory.empty .Ptr 1 (some ⟨99⟩) rfl (by cases model <;> decide)

theorem dead_allocation_provenance_recovers (model : ByteModel) (order : FunctionAddressOrder) :
    (encodeMemoryWithFunctions model order .Ptr (.ptr 1025 (some ⟨99⟩))).bind
      (decodeMemoryWithFunctions model order deadMemory .Ptr) = .ok (.ptr 1025 (some ⟨7⟩)) :=
  pointer_memory_roundtrip model order deadMemory .Ptr 1025 (some ⟨99⟩) rfl (by cases model <;> decide)

theorem one_past_provenance_recovers (model : ByteModel) (order : FunctionAddressOrder) :
    (encodeMemoryWithFunctions model order .Ptr (.ptr 1032 none)).bind
      (decodeMemoryWithFunctions model order deadMemory .Ptr) = .ok (.ptr 1032 (some ⟨7⟩)) :=
  pointer_memory_roundtrip model order deadMemory .Ptr 1032 none rfl (by cases model <;> decide)

theorem containment_precedes_one_past (model : ByteModel) (order : FunctionAddressOrder) :
    (encodeMemoryWithFunctions model order .Ptr (.ptr 1032 (some ⟨7⟩))).bind
      (decodeMemoryWithFunctions model order boundaryMemory .Ptr) = .ok (.ptr 1032 (some ⟨9⟩)) :=
  pointer_memory_roundtrip model order boundaryMemory .Ptr 1032 (some ⟨7⟩) rfl (by cases model <;> decide)

theorem reference_leaf_recovers_by_address (model : ByteModel) (order : FunctionAddressOrder) :
    (AggregateMemory.encode model order (.leaf (.RefMut .U16) ⟨model.pointerBytes,model.pointerBytes⟩)
      (.ptr 1025 (some ⟨99⟩)) false).bind
      (fun image => AggregateMemory.decode model order deadMemory
        (.leaf (.RefMut .U16) ⟨model.pointerBytes,model.pointerBytes⟩) image.bytes) = .ok (.ptr 1025 (some ⟨7⟩)) :=
  pointer_aggregate_leaf_roundtrip model order deadMemory (.RefMut .U16) _ 1025 (some ⟨99⟩) rfl
    (by cases model <;> decide) rfl

theorem length_metadata_is_32_bit_residue (order : FunctionAddressOrder) (raw : Int) :
    (encodeMemoryWithFunctions .le32 order (.FatPtr .ContainerLen) (.fatPtr 1025 none (.int 32 raw))).bind
      (decodeMemoryWithFunctions .le32 order deadMemory (.FatPtr .ContainerLen)) =
      .ok (.fatPtr 1025 (some ⟨7⟩) (Value.intAt 32 raw)) :=
  fat_length_memory_roundtrip .le32 order deadMemory .ContainerLen 1025 none raw rfl (by decide)

theorem null_data_retains_length_lane (order : FunctionAddressOrder) (raw : Int) :
    (encodeMemoryWithFunctions .le64 order (.FatPtr .Str) (.fatPtr 0 (some ⟨99⟩) (.int 64 raw))).bind
      (decodeMemoryWithFunctions .le64 order deadMemory (.FatPtr .Str)) =
      .ok (.fatPtr 0 none (Value.intAt 64 raw)) :=
  fat_length_memory_roundtrip .le64 order deadMemory .Str 0 (some ⟨99⟩) raw rfl (by decide)

theorem data_and_vtable_provenance_are_independent (model : ByteModel) (order : FunctionAddressOrder) :
    (AggregateMemory.encode model order (.leaf (.FatPtr .ContainerVtable) ⟨2 * model.pointerBytes,model.pointerBytes⟩)
      (.fatPtr 1025 (some ⟨99⟩) (.ptr 1034 (some ⟨99⟩))) false).bind
      (fun image => AggregateMemory.decode model order boundaryMemory
        (.leaf (.FatPtr .ContainerVtable) ⟨2 * model.pointerBytes,model.pointerBytes⟩) image.bytes) =
      .ok (.fatPtr 1025 (some ⟨7⟩) (.ptr 1034 (some ⟨9⟩))) :=
  fat_vtable_aggregate_leaf_roundtrip model order boundaryMemory .ContainerVtable _ 1025 1034
    (some ⟨99⟩) (some ⟨99⟩) rfl (by cases model <;> decide) (by cases model <;> decide) rfl

theorem null_vtable_leaf_roundtrips (model : ByteModel) (order : FunctionAddressOrder) :
    (AggregateMemory.encode model order (.leaf (.FatPtr .ContainerVtable) ⟨2 * model.pointerBytes,model.pointerBytes⟩)
      (.fatPtr 1025 none .nullPtr) false).bind
      (fun image => AggregateMemory.decode model order deadMemory
        (.leaf (.FatPtr .ContainerVtable) ⟨2 * model.pointerBytes,model.pointerBytes⟩) image.bytes) =
      .ok (.fatPtr 1025 (some ⟨7⟩) .nullPtr) :=
  fat_null_vtable_aggregate_leaf_roundtrip model order deadMemory .ContainerVtable _ 1025 none rfl
    (by cases model <;> decide) rfl

theorem thin_overflow_is_not_truncated (model : ByteModel) (order : FunctionAddressOrder) :
    encodeMemoryWithFunctions model order .Ptr (.ptr model.addressLimit none) =
      .error (.ub "Store: pointer address exceeds the target width") :=
  pointer_memory_refuses_overflow model order .Ptr model.addressLimit none rfl (Nat.lt_irrefl _)

theorem fat_data_overflow_is_not_truncated (model : ByteModel) (order : FunctionAddressOrder) :
    encodeMemoryWithFunctions model order (.FatPtr .ContainerLen)
      (.fatPtr model.addressLimit none (.int model.pointerBits 0)) =
      .error (.ub "Store: pointer address exceeds the target width") :=
  fat_pointer_memory_refuses_data model order .ContainerLen model.addressLimit none _ (Nat.lt_irrefl _)

theorem vtable_overflow_is_not_truncated (model : ByteModel) (order : FunctionAddressOrder) :
    encodeMemoryWithFunctions model order (.FatPtr .ContainerVtable)
      (.fatPtr 0 none (.ptr model.addressLimit none)) =
      .error (.ub "Store: pointer address exceeds the target width") :=
  fat_pointer_memory_refuses_vtable model order .ContainerVtable 0 model.addressLimit none none
    (by cases model <;> decide) (Nat.lt_irrefl _)

theorem wrong_metadata_kind_refuses (model : ByteModel) (order : FunctionAddressOrder) :
    AggregateMemory.encode model order (.leaf (.FatPtr .ContainerLen) ⟨2 * model.pointerBytes,model.pointerBytes⟩)
      (.fatPtr 0 none (.ptr 1 none)) false =
      .error (.typeError "memory image: noncanonical fat-pointer lanes") := by
  trustIrCompilerProof {
    cases model <;> rfl
  } {
    cases model <;> trustIrReduce
  }

theorem wrong_thin_leaf_extent_refuses (model : ByteModel) (order : FunctionAddressOrder) :
    AggregateMemory.encode model order (.leaf .Ptr ⟨1,1⟩) (.ptr 1 none) false =
      .error (.typeError "memory image: leaf byte count mismatch") := by
  trustIrCompilerProof {
    cases model <;> rfl
  } {
    cases model <;> trustIrReduce
  }

theorem target32_aggregate_fat_guard_precedes_word_overflow (order : FunctionAddressOrder) :
    AggregateMemory.encode .le32 order (.leaf (.FatPtr .ContainerLen) ⟨8,4⟩)
      (.fatPtr ByteModel.le32.addressLimit none (.int 32 0)) false =
      .error (.typeError "memory image: noncanonical fat-pointer lanes") := by
  trustIrCompilerProof {
    rfl
  } {
    trustIrReduce
  }



theorem target64_aggregate_fat_word_overflow_is_ub (order : FunctionAddressOrder) :
    AggregateMemory.encode .le64 order (.leaf (.FatPtr .ContainerLen) ⟨16,8⟩)
      (.fatPtr ByteModel.le64.addressLimit none (.int 64 0)) false =
      .error (.ub "Store: pointer address exceeds the target width") := by
  trustIrCompilerProof {
    rfl
  } {
    trustIrReduce
  }



theorem target32_length_metadata_rejects_64_bit_carrier (order : FunctionAddressOrder) :
    AggregateMemory.encode .le32 order (.leaf (.FatPtr .ContainerLen) ⟨8,4⟩)
      (.fatPtr 0 none (.int 64 0)) false =
      .error (.typeError "memory image: noncanonical fat-pointer lanes") := by
  trustIrCompilerProof {
    rfl
  } {
    trustIrReduce
  }



theorem target64_length_metadata_rejects_32_bit_carrier (order : FunctionAddressOrder) :
    AggregateMemory.encode .le64 order (.leaf (.FatPtr .ContainerLen) ⟨16,8⟩)
      (.fatPtr 0 none (.int 32 0)) false =
      .error (.typeError "memory image: noncanonical fat-pointer lanes") := by
  trustIrCompilerProof {
    rfl
  } {
    trustIrReduce
  }



end PointerCodecControls

end TrustIr

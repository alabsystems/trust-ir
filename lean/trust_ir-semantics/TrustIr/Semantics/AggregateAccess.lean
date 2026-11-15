-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Semantics.AggregateDecoding
import TrustIr.Semantics.AggregateEquality
import TrustIr.Semantics.Atomic

namespace TrustIr.AggregateMemory

private def checkedPlan (service : Service) (model : ByteModel) (ty : Ty) : Except SemError Plan :=
  if model == service.model then service.query ty
  else .error (.typeError "memory: source layout target does not match evaluator target")

theorem checkedPlan_errors (error : SemError → Prop)
    (typeErrors : ∀ message, error (.typeError message)) (service : Service)
    (safe : ServiceErrorPolicy error service) (model : ByteModel) (ty : Ty) :
    ByteImage.BlockResult (fun _ => True) error (checkedPlan service model ty) := by
  unfold checkedPlan
  split
  · exact (safe ty).1
  · exact typeErrors _

def layoutQuery (service : Service) (model : ByteModel) (ty : Ty) : Except SemError MemoryTypeLayout := do
  if model == service.model then service.queryLayout ty
  else .error (.typeError "memory: source layout target does not match evaluator target")

/-- Holding values performs no private SSA publication. The caller supplies
    the actual source-layout service and source-order function namespace. -/
def loadValue (service : Service) (order : FunctionAddressOrder) (ty : Ty) (pointer : Value)
    (strict : Bool := false) (align : Option Nat := none) (model : ByteModel := .le64) : Sem Value := do
  let plan ← Sem.fromMemoryExcept (checkedPlan service model ty)
  let alignment ← Sem.fromMemoryExcept (checkedMemoryAlign "Load" plan.layout.alignment align)
  Sem.rejectPartial pointer "Load"
  let (address, allocation) ← Sem.expectPointer "Load" pointer
  let address ← Sem.checkedAccess "Load" address allocation plan.layout.size alignment model
  let state ← Sem.getState
  let image := state.memory.readImage address plan.layout.size
  if (firstMissing image).isNone then
    Sem.fromMemoryExcept (decode model order state.memory plan image)
  else if !strict && isPartialLoadTyFor model ty then pure (.partial image.toList)
  else
    match ← Sem.fromMemoryExcept (covered plan image) with
    | none => Sem.fromMemoryExcept (decode model order state.memory plan image)
    | some _ =>
      match plan with
      | .fields _ _ _ =>
        let explained := state.memory.unwritten.foldl (fun current lane =>
          if lane.allocation == allocation then
            let start := max address lane.start
            let stop := min (address + image.size) lane.stop
            if start < stop then
              let offset := start - address
              (current.slice 0 offset).append ((ByteImage.fill (stop - start) (some 0)).append
                (current.slice (stop - address) (image.size - (stop - address))))
            else current
          else current) image
        match ← Sem.fromMemoryExcept (covered plan explained) with
        | none => Sem.fromMemoryExcept (decodeUnwritten model order state.memory plan image)
        | some _ => Sem.throwUB "Load: reading uninitialized covered memory"
      | _ => Sem.throwUB "Load: reading uninitialized covered memory"

def load (service : Service) (order : FunctionAddressOrder) (ty : Ty) (pointer : ValueId)
    (strict : Bool := false) (align : Option Nat := none) (model : ByteModel := .le64) : Sem ValueId := do
  let pointer ← Sem.lookupValue pointer
  let value ← loadValue service order ty pointer strict align model
  Sem.bindFresh value

/-- A typed store writes absent padding and tracks only explicit Uninit
    lanes. Every write first clips previous records, including partial images. -/
def storeValue (service : Service) (order : FunctionAddressOrder) (ty : Ty)
    (pointer value : Value) (strict : Bool := false) (align : Option Nat := none)
    (model : ByteModel := .le64) : Sem Unit := do
  if strict && (value.isPoison || carriesUnwritten value) then
    Sem.throwUB "Store: strict store of poison or unwritten aggregate lane"
  let plan ← Sem.fromMemoryExcept (checkedPlan service model ty)
  let alignment ← Sem.fromMemoryExcept (checkedMemoryAlign "Store" plan.layout.alignment align)
  Sem.rejectPartial pointer "Store"
  let (address, allocation) ← Sem.expectPointer "Store" pointer
  let address ← Sem.checkedAccess "Store" address allocation plan.layout.size alignment model
  let image ← match value with
    | .partial bytes => pure ({ bytes := ByteImage.ofList bytes } : Image)
    | .undef held =>
      if closureTyEq held ty then pure { bytes := ByteImage.fill plan.layout.size none }
      else Sem.throwTypeError "Store: poison source type does not match store type"
    | _ => Sem.fromMemoryExcept (encode model order plan value (carriesUnwritten value))
  if image.bytes.size != plan.layout.size then
    Sem.throwTypeError "Store: image byte count does not match source layout"
  Sem.modifyState fun state =>
    let memory := state.memory.writeImage address image.bytes
    { state with memory := memory.recordUnwritten allocation address image.unwritten }

def store (service : Service) (order : FunctionAddressOrder) (ty : Ty)
    (pointer value : ValueId) (strict : Bool := false) (align : Option Nat := none)
    (model : ByteModel := .le64) : Sem Unit := do
  let pointer ← Sem.lookupValue pointer
  let value ← Sem.lookupValue value
  storeValue service order ty pointer value strict align model

def atomicLoad (service : Service) (order : FunctionAddressOrder) (ty : Ty)
    (pointer : ValueId) (ordering : MemOrdering) (model : ByteModel := .le64) : Sem ValueId := do
  if !isValidLoadOrdering ordering then Sem.throwTypeError "AtomicLoad: invalid load ordering"
  load service order ty pointer true none model

def atomicStore (service : Service) (order : FunctionAddressOrder) (ty : Ty)
    (pointer value : ValueId) (ordering : MemOrdering) (model : ByteModel := .le64) : Sem Unit := do
  if !isValidStoreOrdering ordering then Sem.throwTypeError "AtomicStore: invalid store ordering"
  store service order ty pointer value true none model

def atomicRMW (service : Service) (order : FunctionAddressOrder) (op : AtomicRMWOp)
    (ty : Ty) (pointer operand : ValueId) (_ordering : MemOrdering)
    (model : ByteModel := .le64) : Sem ValueId := do
  let pointer ← Sem.lookupValue pointer
  let operand ← Sem.lookupValue operand
  let current ← loadValue service order ty pointer true none model
  Sem.rejectPartial operand "AtomicRMW"
  let replacement ← match current, operand with
    | .int width raw, .int _ argument => pure (.int width (applyAtomicRMWOp op width raw argument))
    | _, _ => Sem.throwTypeError "AtomicRMW: expected integer operands"
  storeValue service order ty pointer replacement true none model
  Sem.bindFresh current

def cmpXchgExchange (service : Service) (order : FunctionAddressOrder) (ty : Ty)
    (pointer expected desired : ValueId) (model : ByteModel := .le64) : Sem (Value × Bool) := do
  let pointer ← Sem.lookupValue pointer
  let expected ← Sem.lookupValue expected
  let desired ← Sem.lookupValue desired
  let current ← loadValue service order ty pointer true none model
  Sem.rejectPartial expected "CmpXchg expected"
  let plan ← Sem.fromMemoryExcept (checkedPlan service model ty)
  let success ← Sem.fromMemoryExcept (equal model plan current expected)
  if success then storeValue service order ty pointer desired true none model
  pure (current, success)

end TrustIr.AggregateMemory

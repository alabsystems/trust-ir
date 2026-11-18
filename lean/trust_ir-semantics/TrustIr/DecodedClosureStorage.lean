-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.DecodedModule
import TrustIr.Layout.Service

namespace TrustIrEval.ClosureStorage
open TrustIr

/-! Source-bound closure storage identity. This consumes the existing decoded
Module; it does not parse, evaluate, construct a byte codec or license a callee.
A target is obtained only from actual typed original constructors. In particular
zero-byte geometry and a nominal id do not supply a code identity. -/

mutual
  /-- Constants do not carry nested nominal type annotations. -/
  def containsClosure : Constant → Bool
    | .closure _ _ => true
    | .aggregate values | .vector values | .sequence values | .set values
    | .array values => listContainsClosure values
    | .record fields => fieldsContainClosure fields
    | .splat value _ => containsClosure value
    | .int _ | .float _ | .bool _ | .u128 _ | .bytes _ _ | .fnDef _
    | .symbolAddr _ _ | .phantomData | .uninit | .fnItem _ => false
  def listContainsClosure : List Constant → Bool
    | [] => false
    | value :: rest => containsClosure value || listContainsClosure rest
  def fieldsContainClosure : List (String × Constant) → Bool
    | [] => false
    | (_, value) :: rest => containsClosure value || fieldsContainClosure rest
end

/-- The Rust storage binding's typed-constant boundary: an untyped or nested
closure cannot silently disappear from the whole-module target census. -/
def constantTargets (closure : ClosureTyId) (ty : Ty) (value : Constant) : D (List FuncId) :=
  match ty, value with
  | .Closure id, .closure target captures =>
    if listContainsClosure captures then unsupported "nested constant closure storage"
    else pure (if id == closure then [target] else [])
  | _, _ =>
    if containsClosure value then unsupported "untyped constant closure storage"
    else pure []

/-- Every raw body participates, including unreachable functions/blocks and
terminators. An original decode error is retained, never replaced by an empty
body or a call-graph-limited observation. -/
def sourceInstructions : List Function → D (List Inst)
  | [] => pure []
  | function :: rest => do
    let blocks ← function.blocks
    let later ← sourceInstructions rest
    pure ((trustIrListBind blocks (fun row => row.2.body ++ [row.2.terminator])) ++ later)

def instructionConstantTargets (closure : ClosureTyId) : List Inst → D (List FuncId)
  | [] => pure []
  | inst :: rest => do
    let here ← match inst with
      | .Const ty value => constantTargets closure ty value
      | _ => pure []
    let later ← instructionConstantTargets closure rest
    pure (here ++ later)

def globalTargets (closure : ClosureTyId) : List GlobalDef → D (List FuncId)
  | [] => pure []
  | global :: rest => do
    let here ← match global.initializer with
      | some value => constantTargets closure global.ty value
      | none => pure []
    let later ← globalTargets closure rest
    pure (here ++ later)

/-- Exact typed constructor sources of the original immutable decoded module.
No layout, geometry, inferred local type or dynamic value contributes a target. -/
def constructorTargets (source : Module) (closure : ClosureTyId) : D (List FuncId) := do
  let instructions ← sourceInstructions source.functions
  let constants ← instructionConstantTargets closure instructions
  let globals ← globalTargets closure source.globals
  let made := instructions.filterMap (fun inst => match inst with
    | .MakeClosure id target _ => if id == closure then some target else none
    | _ => none)
  pure (constants ++ globals ++ made)

def uniformTarget : List FuncId → D FuncId
  | [] => malformed "missing closure storage target"
  | target :: rest =>
    if rest.all (fun other => other == target) then pure target
    else malformed "conflicting closure storage targets"

/-- A nonempty original constructor occurrence and equality of EVERY observed
target are the checked source facts, rather than a caller-supplied Known row. -/
theorem uniformTarget_sound (targets : List FuncId) (target : FuncId)
    (success : uniformTarget targets = .ok target) :
    target ∈ targets ∧ ∀ other ∈ targets, other = target := by
  cases targets with
  | nil => cases success
  | cons first rest =>
    simp only [uniformTarget] at success
    split at success
    next same =>
      cases success
      constructor
      · exact .head _
      · intro other member
        cases member with
        | head => rfl
        | tail _ member =>
          have checked := (List.all_eq_true.mp same) other member
          exact of_decide_eq_true checked
    next => cases success

/-- Dependent source identity: constructing a target requires genuine source
occurrence and whole-census agreement for this exact Module and nominal id. -/
structure Target (source : Module) (closure : ClosureTyId) where
  private mk ::
  value : FuncId
  private occurrences : List FuncId
  private original : constructorTargets source closure = .ok occurrences
  private present : value ∈ occurrences
  private unique : ∀ other ∈ occurrences, other = value

def targetOf (source : Module) (closure : ClosureTyId) : D (Target source closure) :=
  match original : constructorTargets source closure with
  | .error error => .error error
  | .ok occurrences =>
    match selected : uniformTarget occurrences with
    | .error error => .error error
    | .ok value =>
      let checked := uniformTarget_sound occurrences value selected
      .ok ⟨value, occurrences, original, checked.1, checked.2⟩

theorem Target.original_constructors {source : Module} {closure : ClosureTyId}
    (target : Target source closure) :
    ∃ occurrences, constructorTargets source closure = .ok occurrences ∧
      target.value ∈ occurrences ∧ ∀ other ∈ occurrences, other = target.value :=
  ⟨target.occurrences, target.original, target.present, target.unique⟩

/-- Exact physical closure entry signature. Structural comparison is the
existing proved comparator, never layout equality or scalar-width coercion. -/
def physicalMatches (captures : List Ty) (apparent physical : FuncTyDef) : Bool :=
  closureTyListEq physical.params (captures ++ apparent.params) &&
    closureTyListEq physical.returns apparent.returns &&
    !physical.isVararg && physical.abi.isNone

theorem physicalMatches_sound (captures : List Ty) (apparent physical : FuncTyDef)
    (success : physicalMatches captures apparent physical = true) :
    physical.params = captures ++ apparent.params ∧
    physical.returns = apparent.returns ∧
    physical.isVararg = false ∧ physical.abi = none := by
  simp only [physicalMatches, Bool.and_eq_true_iff] at success
  refine ⟨closureTyListEq_sound _ _ success.1.1.1,
    closureTyListEq_sound _ _ success.1.1.2, ?_, ?_⟩
  · cases value : physical.isVararg <;> simp_all
  · cases value : physical.abi <;> simp_all

private def validateLayouts (session : SourceLayout.Session) :
    List SourceLayout.ClosureLayoutDescriptor → D Unit
  | [] => pure ()
  | row :: rest => do
    match session.query .shape (.Closure row.closure) with
    | .error error => malformed s!"closure layout: {repr error}"
    | .ok _ => validateLayouts session rest

/-- Checked DATA retains the actual declaration, descriptor and shape alongside
its dependent original target. Private construction supplies no memory codec,
callee rely, allocation/frame witness or native/proof authority. -/
structure Binding (source : Module) (closure : ClosureTyId) where
  private mk ::
  model : ByteModel
  modelSource : source.byteModel = .ok model
  target : Target source closure
  nominal : ClosureTy
  nominalSource : (trustIrListGet? source.closureTys closure.index) = some nominal
  apparent : FuncTyDef
  apparentSource : (trustIrListGet? source.funcTys nominal.func.index) = some apparent
  unadapted : apparent.isVararg = false ∧ apparent.abi = none
  function : Function
  functionSource : source.functions.filter (fun row => row.id == target.value) = [function]
  defined : function.isDeclaration = false
  body : List (BlockId × BasicBlock)
  bodySource : function.blocks = .ok body
  nonemptyBody : body ≠ []
  physical : FuncTyDef
  physicalSource : (trustIrListGet? source.funcTys function.ty.index) = some physical
  descriptor : SourceLayout.ClosureLayoutDescriptor
  descriptorSource : SourceLayout.closureDescriptor (layoutSourceOf source model) closure = .ok (some descriptor)
  shape : SourceLayout.Summary
  shapeSource : ∃ after, (SourceLayout.prepare (layoutSourceOf source model)).query .shape (.Closure closure) = .ok (shape, after)
  physicalContract : physicalMatches nominal.captures apparent physical = true

private def retainResult {α : Type} (result : D α) : D { value : α // result = .ok value } :=
  match result with
  | .error error => .error error
  | .ok value => .ok ⟨value, rfl⟩

private def requireSome {α : Type} (value : Option α) (message : String) :
    D { found : α // value = some found } :=
  match value with
  | none => malformed message
  | some found => .ok ⟨found, rfl⟩

private def requireSingleton {α : Type} (values : List α) (message : String) :
    D { found : α // values = [found] } :=
  match values with
  | [found] => .ok ⟨found, rfl⟩
  | _ => malformed message

private def requireFalse (value : Bool) (message : String) : D (PLift (value = false)) :=
  match value with
  | false => .ok ⟨rfl⟩
  | true => malformed message

private def requireTrue (value : Bool) (message : String) : D (PLift (value = true)) :=
  match value with
  | true => .ok ⟨rfl⟩
  | false => malformed message

/-- Proof-only bridge for the existing checked Boolean result. The original
Boolean remains fixed in the PLift type consumed by the caller continuation. -/
theorem requireTrue_eq_ok (value : Bool) (message : String) (success : value = true) :
    requireTrue value message = .ok (⟨success⟩ : PLift (value = true)) := by
  cases success
  rfl

/-- Failed checks preserve the original error and dependent result type. -/
theorem requireTrue_eq_error (value : Bool) (message : String) (failure : value = false) :
    requireTrue value message = (malformed message : D (PLift (value = true))) := by
  cases failure
  rfl

/-- The source-owned storage query. Existing layout validation remains the
canonical geometry engine; original constructors supply the separate code
identity, and the unique original body supplies the full physical signature. -/
def bindingOf (source : Module) (closure : ClosureTyId) : D (Binding source closure) := do
  let model ← retainResult source.byteModel
  let layouts := layoutSourceOf source model.val
  let session := SourceLayout.prepare layouts
  let _ ← validateLayouts session source.closureLayouts
  let descriptor ← match original : SourceLayout.closureDescriptor layouts closure with
    | .error error => malformed s!"closure descriptor: {repr error}"
    | .ok none => malformed "missing closure layout"
    | .ok (some descriptor) => pure (⟨descriptor, original⟩ :
        { descriptor // SourceLayout.closureDescriptor layouts closure = .ok (some descriptor) })
  let shape ← match original : session.query .shape (.Closure closure) with
    | .error error => malformed s!"closure layout: {repr error}"
    | .ok (shape, after) => pure (⟨shape, ⟨after, original⟩⟩ :
        { shape // ∃ after, session.query .shape (.Closure closure) = .ok (shape, after) })
  let nominal ← requireSome (trustIrListGet? source.closureTys closure.index) "missing closure type"
  let apparent ← requireSome (trustIrListGet? source.funcTys nominal.val.func.index) "missing closure signature"
  let notVararg ← requireFalse apparent.val.isVararg "closure storage requires an unadapted signature"
  let noAbi ← requireTrue apparent.val.abi.isNone "closure storage requires an unadapted signature"
  have noAbiSource : apparent.val.abi = none := by
    have checked := noAbi.down
    cases original : apparent.val.abi <;> simp_all
  let target ← targetOf source closure
  let function ← requireSingleton (source.functions.filter (fun row => row.id == target.value))
    "missing or ambiguous closure target"
  let defined ← requireFalse function.val.isDeclaration "closure storage target has no body"
  let body ← retainResult function.val.blocks
  let nonempty ← match original : body.val with
    | [] => malformed "closure storage target has no body"
    | first :: rest => pure (⟨by rw [original]; intro impossible; cases impossible⟩ : PLift (body.val ≠ []))
  let physical ← requireSome (trustIrListGet? source.funcTys function.val.ty.index)
    "missing closure target signature"
  let checked ← requireTrue (physicalMatches nominal.val.captures apparent.val physical.val)
    "closure storage target signature mismatch"
  pure ⟨model.val, model.property, target, nominal.val, nominal.property,
    apparent.val, apparent.property, ⟨notVararg.down, noAbiSource⟩,
    function.val, function.property, defined.down, body.val, body.property, nonempty.down,
    physical.val, physical.property, descriptor.val, descriptor.property,
    shape.val, shape.property, checked.down⟩

/-- Every result retains the full physical entry signature, independently of
storage geometry. This is an original-header equality, not an ABI/callee proof. -/
theorem Binding.physical_signature {source : Module} {closure : ClosureTyId}
    (binding : Binding source closure) :
    binding.physical.params = binding.nominal.captures ++ binding.apparent.params ∧
    binding.physical.returns = binding.apparent.returns ∧
    binding.physical.isVararg = false ∧ binding.physical.abi = none :=
  physicalMatches_sound _ _ _ binding.physicalContract

/-- Source occurrence and whole-original-module target agreement survive every
later layout/signature check; no target can be supplied by the byte footprint. -/
theorem Binding.original_constructors {source : Module} {closure : ClosureTyId}
    (binding : Binding source closure) :
    ∃ occurrences, constructorTargets source closure = .ok occurrences ∧
      binding.target.value ∈ occurrences ∧
      ∀ other ∈ occurrences, other = binding.target.value :=
  binding.target.original_constructors

end TrustIrEval.ClosureStorage

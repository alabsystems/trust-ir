-- Copyright 2026 Andrew Yates | Apache-2.0
-- Actual pure context assembly shared with the oracle runner.
-- Prepared lookups preserve the original queries; no JSON decoder is imported.
import Lean.Data.RBMap
import TrustIr.DecodedFunctionLookup
import TrustIr.PreparedCFG

namespace TrustIrEval
open TrustIr

def cfgOf (blocks : List (BlockId × BasicBlock)) : CFG :=
  fun id => (blocks.find? (fun p => p.fst == id)).map (·.snd)

trustIrDenseMatch
/-- Statically applied functions. A `FnDef` constant is not an eager edge:
    merely passing an unused function value must not inspect its body.
    Typed application resolves its exact identity at the call; decoder
    failures of dynamic targets remain in `EvalContext.functionErrors`. -/
def calleesOfInst (glueOf : Ty → Option FuncId) : Inst → List FuncId
  | .Call callee _ => [callee]
  | .MakeClosure _ target _ => [target]
  | .Const (.Closure _) (.closure target _) => [target]
  | .Invoke callee _ _ _ _ => [callee]
  | .SeqMap _ _ fwd => [fwd]
  -- Amendment D: a resolved drop transfers control to its glue.
  | .Drop ty _ => (glueOf ty).toList
  | .DropInvoke ty _ _ _ _ => (glueOf ty).toList
  | _ => []

def calleesOf (glueOf : Ty → Option FuncId) (blocks : List (BlockId × BasicBlock)) :
    List FuncId :=
  blocks.foldl (fun acc (_, b) =>
    acc ++ (b.body.foldl (fun a i => a ++ calleesOfInst glueOf i) [])
      ++ calleesOfInst glueOf b.terminator) []

/-- Amendment D (§20): the module's drop-glue table as the evaluator's
    lookup (the row whose key equals the dropped type). -/
def dropGlueOf (m : Module) : Ty → Option FuncId :=
  fun t => (m.dropGlue.find? (fun row => row.snd == some t)).map (·.fst)

trustIrDenseMatch
/-- Whether a block list contains a drop (either spelling). -/
def blocksDrop (blocks : List (BlockId × BasicBlock)) : Bool :=
  let isDrop : Inst → Bool
    | .Drop .. => true
    | .DropInvoke .. => true
    | _ => false
  blocks.any (fun (_, b) => b.body.any isDrop || isDrop b.terminator)

/-- Index original headers without inspecting executable bodies. The first
    source row for an id retains the previous lookup behavior, even for a
    malformed duplicate whose signature is absent. -/
def localTypeHeadersOf (m : Module) :
    Array FuncTyDef × (FuncId → Option FuncTyDef) :=
  let signatures := m.funcTys.toArray
  let initial : Lean.RBMap Nat (Option FuncTyDef) compare := Lean.mkRBMap ..
  let headers := m.functions.foldl (fun table function =>
    if table.contains function.id.index then table
    else table.insert function.id.index (trustIrArrayGet? signatures function.ty.index)) initial
  (signatures, fun id => (headers.find? id.index).join)

/-- The evaluator's view of one decoded body, using shared original header
    indexes. Signature and local declarations remain separate from execution. -/
def evalFunctionOfWithTypes (signatures : Array FuncTyDef)
    (direct : FuncId → Option FuncTyDef) (f : Function)
    (blocks : List (BlockId × BasicBlock)) :
    D EvalFunction := do
  let sig ← match trustIrArrayGet? signatures f.ty.index with
    | some s => pure s
    | none => malformed s!"function {f.name}: func type {f.ty.index} not in table"
  let declaredTypes := inferLocalTypes direct (fun sig => trustIrArrayGet? signatures sig.index)
    (trustIrListBind blocks (fun row => row.snd.params))
    (trustIrListBind blocks (fun (_, block) =>
      bodyInstsWithResultDests block.body block.bodyResultDests ++
        [(block.terminator, block.terminatorResultDests)]))
  let localTypes ← match declaredTypes with
    | .ok table => pure table
    | .error (.typeError message) => malformed message
    | .error error => malformed s!"SSA declarations: {repr error}"
  let prepared := TrustIr.GenericCoro.IndexedCFG.indexedCFG blocks
  pure { sourceId := some f.id
         body := { paramTys := sig.params, returnTys := sig.returns, abi := sig.abi, isVararg := sig.isVararg }
         cfg := prepared.cfg
         entryBlock := f.entry
         callingConv := f.callingConvention
         localTypes := some localTypes }

def evalFunctionOf (m : Module) (f : Function) (blocks : List (BlockId × BasicBlock)) :
    D EvalFunction :=
  let (signatures, direct) := localTypeHeadersOf m
  evalFunctionOfWithTypes signatures direct f blocks

/-- Only actual memory/SeqMap declarations form prepared roots. Unrelated
    type rows still participate in layout validation where Rust requires it,
    but do not force eager image compilation or execution of unused bodies. -/
private def memoryRootsOfInst (m : Module) : Inst → List Ty
  | .Alloca ty .. | .HeapAlloc ty .. | .GEP ty .. | .Load ty .. | .Store ty ..
  | .AtomicLoad ty .. | .AtomicStore ty .. | .AtomicRMW _ ty .. | .CmpXchg ty .. => [ty]
  | .SeqMap (.Sequence element) _ _ => ((trustIrListGet? m.types element.index).join).toList
  | _ => []

/-- Preserve the original function's header and body-declaration provenance
    together, including malformed headers and undecodable bodies. -/
def functionDeclarationOf (signatures : Array FuncTyDef) (function : Function) :
    FunctionItemPresence.FunctionDecl :=
  { id := function.id
    header := match trustIrArrayGet? signatures function.ty.index with
      | some signature => .ok
          { signatureId := function.ty,
            header := { signature, callingConv := function.callingConvention } }
      | none => .error s!"FnItem: function {function.id.index} has no original signature"
    frames := function.blocks.toOption.map (fun blocks =>
      trustIrListBind blocks (fun (_, block) => (block.body ++ [block.terminator]).filterMap (fun inst =>
        match inst with
        | .OpenFrame declaration => some declaration
        | _ => none))) }

/-- Lookup and containment share complete original finite declarations,
    including undecodable rows and their source positions. Function headers
    and frame origins come from the same raw function rows. -/
def valueSourceOf (m : Module) : FunctionItemPresence.Prepared :=
  let signatures := m.funcTys.toArray
  FunctionItemPresence.prepare
    { types := m.types, structs := m.structs, enums := m.enums,
      records := m.records, closures := m.closureTys,
      functions := m.functions.map (functionDeclarationOf signatures) }

private def memoryServiceOf (m : Module) (model : ByteModel) : AggregateMemory.Service :=
  let source : SourceLayout.Environment :=
    { model, canonicalScalars := true, hasTargetInfo := m.hasTargetInfo,
      types := m.types, structs := m.structs, enums := m.enums,
      records := m.records.filterMap (·.2), closures := m.closureTys,
      tupleLayouts := m.tupleLayouts, closureLayouts := m.closureLayouts,
      functions := m.functions.map (fun function => (function.id, function.ty)),
      funcTypes := m.funcTys }
  let roots := [.I64] ++ m.globals.map (·.ty) ++ trustIrListBind m.functions (fun function =>
    match function.blocks with
    | .error _ => []
    | .ok blocks => trustIrListBind blocks (fun (_, block) =>
      trustIrListBind (block.body ++ [block.terminator]) (memoryRootsOfInst m)))
  AggregateMemory.prepare source (roots.filter (fun ty => !ty.hasCanonicalMemoryLayout))

/-- Every function whose body decoded, keyed by id. A function whose body
    did NOT decode is absent (the runner refuses any run that reaches it
    before evaluation starts, see `reachableDecodeFailure`). -/
def contextOf (m : Module) (maxCallDepth : Nat) : D EvalContext := do
  let selectedModel ← m.byteModel
  -- Deliberately conservative: the decoder retains the full claims, but this
  -- oracle currently refuses any module containing a typed ABI signature.
  -- Comparing logical argument values would not validate its carrier mapping.
  if m.funcTys.any (fun sig => sig.abi.isSome) then
    unsupported "signature_abi.transport_semantics"
  let (signatures, direct) := localTypeHeadersOf m
  let initialHeaders : Lean.RBMap Nat (Except SemError FunctionHeader) compare := Lean.mkRBMap ..
  let headers := m.functions.foldl (fun table function =>
    if table.contains function.id.index then table
    else table.insert function.id.index (match trustIrArrayGet? signatures function.ty.index with
      | some signature => .ok { signature, callingConv := function.callingConvention }
      | none => .error (.typeError s!"function {function.id.index}: original signature is absent"))) initialHeaders
  -- Keep each body's metadata failure lazy, exactly like its decode failure.
  -- Direct-call result declarations inspect original headers, never this table.
  let defs : List (FuncId × D EvalFunction) := m.functions.filterMap (fun f =>
    match f.blocks with
    | .ok blocks =>
      if f.isDeclaration then none
      else some (f.id, evalFunctionOfWithTypes signatures direct f blocks)
    | .error _ => none)
  let lookups := FunctionLookup.prepare m.functions defs
  pure { byteModel := selectedModel
         valueSource := valueSourceOf m
         memoryService := some (memoryServiceOf m selectedModel)
         functions := fun fid => FunctionLookup.findFunction lookups fid
         functionHeaders := fun fid => headers.find? fid.index
         -- Memory code words use original source positions, including entries
         -- absent from executable `defs`. They decode to typed FnDef values;
         -- raw-pointer call admission and native reification remain separate.
         functionOrder := some (m.functions.map (·.id))
         funcPtrs := fun _ => none
         funcTys := fun id => trustIrArrayGet? signatures id.index
         maxCallDepth := maxCallDepth
         globalsTable := fun id => trustIrListGet? m.globals id.index
         -- A bodyless declaration is `unsupported.interprocedural_call` when
         -- called (the interpreter's `UnsupportedCall`), never "undefined".
         declared := fun fid => FunctionLookup.isDeclared lookups fid
         functionErrors := fun fid => FunctionLookup.findError lookups fid
         tupleLayouts := m.tupleLayouts
         -- Amendment D: a drop resolves to the glue of the row keyed on its
         -- type, and is then the ordinary `Call` / `Invoke`.
         dropGlue := dropGlueOf m }

/-- Definitional proof interface for the actual private root selector. -/
theorem memoryRootsOfInst_eq (m : Module) (inst : Inst) :
    memoryRootsOfInst m inst = (match inst with
      | .Alloca ty .. | .HeapAlloc ty .. | .GEP ty .. | .Load ty .. | .Store ty ..
      | .AtomicLoad ty .. | .AtomicStore ty .. | .AtomicRMW _ ty .. | .CmpXchg ty .. => [ty]
      | .SeqMap (.Sequence element) _ _ => ((trustIrListGet? m.types element.index).join).toList
      | _ => []) := rfl

/-- Definitional proof interface; this does not introduce another preparer. -/
theorem memoryServiceOf_eq (m : Module) (model : ByteModel) :
    memoryServiceOf m model = AggregateMemory.prepare
      { model, canonicalScalars := true, hasTargetInfo := m.hasTargetInfo,
        types := m.types, structs := m.structs, enums := m.enums,
        records := m.records.filterMap (·.2), closures := m.closureTys,
        tupleLayouts := m.tupleLayouts, closureLayouts := m.closureLayouts,
        functions := m.functions.map (fun function => (function.id, function.ty)),
        funcTypes := m.funcTys }
      (List.filter (fun ty => !ty.hasCanonicalMemoryLayout) ([Ty.I64] ++ m.globals.map (fun global : GlobalDef => global.ty) ++ trustIrListBind m.functions (fun function =>
        match function.blocks with
        | .error _ => []
        | .ok blocks => trustIrListBind blocks (fun (_, block) =>
          trustIrListBind (block.body ++ [block.terminator]) (memoryRootsOfInst m))))
        ) := rfl

end TrustIrEval

/-- info: 'TrustIrEval.blocksDrop' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIrEval.blocksDrop

/-- info: 'TrustIrEval.blocksDrop.match_1' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIrEval.blocksDrop.match_1

/-- info: 'TrustIrEval.calleesOfInst' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIrEval.calleesOfInst

/-- info: 'TrustIrEval.calleesOfInst.match_1' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIrEval.calleesOfInst.match_1

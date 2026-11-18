-- Copyright 2026 Andrew Yates | Apache-2.0
-- Pure decoded data shared by the JSON reader and source-to-source producers.
-- This module has no JSON import and retains the decoder's original records.
import TrustIr.ModuleSyntax
import TrustIr.Layout.Schema
import TrustIr.Template

namespace TrustIrEval
open TrustIr

/-- A decode failure: an unmodelled construct (reported as the oracle verdict
    `unsupported`) or a schema violation (reported as an oracle ERROR). -/
inductive DecodeError where
  | unsupported (feature : String)
  | malformed (msg : String)
  deriving Repr, Inhabited

abbrev D := Except DecodeError

def malformed {α : Type} (msg : String) : D α := throw (.malformed msg)
def unsupported {α : Type} (feature : String) : D α := throw (.unsupported feature)


/-- One decoded instruction node: the instruction and its declared result
    destinations (`InstrNode.results`). -/
structure Node where
  inst : Inst
  results : List ValueId


structure Function where
  id : FuncId
  name : String
  ty : FuncTyId
  entry : BlockId
  /-- `true` for a bodyless declaration (`Function::is_declaration`). -/
  isDeclaration : Bool
  callingConvention : CallingConv := .C
  /-- The body's decode outcome, kept PER FUNCTION so that one function using
      a construct with no Lean mirror makes only the runs that REACH it
      `unsupported` (the runner walks the static call graph), not every run
      of the module. Empty for a declaration. -/
  blocks : Except DecodeError (List (BlockId × BasicBlock))


/-- The decoded module: exactly the tables the evaluator context consumes. -/
structure Module where
  byteModel : D ByteModel := .ok .le64
  hasTargetInfo : Bool := false
  functions : List Function
  /-- Indexed by `FuncTyId` (the position in `Module.func_types`). -/
  funcTys : List FuncTyDef
  /-- Indexed by the actual module ClosureTyId, never matched by shape. -/
  closureTys : List ClosureTy := []
  /-- Indexed by `GlobalId` (the position in `Module.globals`). -/
  globals : List GlobalDef
  /-- Keyed by `EnumDef.id` (WS2.19 constant lowering). -/
  enums : List EnumDef
  /-- Keyed by `StructDef.id` (WS2.19 constant lowering). -/
  structs : List StructDef
  /-- Original v42 tuple descriptors, including their source TyIds. -/
  tupleLayouts : List TupleLayoutDescriptor := []
  closureLayouts : List SourceLayout.ClosureLayoutDescriptor := []
  /-- Keyed by actual record ids. An unsupported field type leaves a missing
      definition at use, without refusing an unrelated executable function. -/
  records : List (RecordId × Option RecordDef) := []
  /-- Indexed by `TyId` (the position in `Module.types`): the element types
      `Ty.Array` / `Ty.Sequence` / `Ty.Set` name by id. Kept per entry: an
      entry the decoder has no arm for refuses only the constants that
      resolve THROUGH it (a `none` entry is `unsupported.enum_def_table` at
      use), not the whole module. -/
  types : List (Option Ty)
  /-- Amendment D (§20): the drop-glue table, one `(glue, key)` row per
      `Module.drop_glue` entry (absent from a pre-table document, i.e. `[]`).
      A key the decoder has no arm for is kept as `none`: the runner then
      refuses every run reaching a drop (`reachableDecodeFailure`) rather
      than resolve one against an incomplete table. -/
  dropGlue : List (FuncId × Option Ty) := []


/-- The original decoded module's layout projection, shared by actual memory
preparation and source-bound storage queries. No constructor target is inferred
from these geometry/header tables. -/
def layoutSourceOf (m : Module) (model : ByteModel) : SourceLayout.Environment :=
  { model, canonicalScalars := true, hasTargetInfo := m.hasTargetInfo,
    types := m.types, structs := m.structs, enums := m.enums,
    records := m.records.filterMap (·.2), closures := m.closureTys,
    tupleLayouts := m.tupleLayouts, closureLayouts := m.closureLayouts,
    functions := m.functions.map (fun function => (function.id, function.ty)),
    funcTypes := m.funcTys }

end TrustIrEval

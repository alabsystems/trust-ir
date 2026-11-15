-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Semantics.Call
import TrustIr.Semantics.TypedInteger
import TrustIr.Semantics.NatIndex

namespace TrustIr

/-- Function-local SSA declarations, independent of dense ids and block order. -/
def LocalTypeTable := ValueId → Option Ty

/-- An instruction's result is declared directly, except for borrow chains. -/
inductive LocalTypeSource where
  | declared (ty : Ty)
  | borrow (operand : ValueId)

trustIrDenseMatch
/-- The bridge's result-type rule, applied to original module headers rather
    than executable callee bodies. Unsupported callees need not be decoded. -/
def localResultTypes (direct : FuncId → Option FuncTyDef) (indirect : FuncTyTable) :
    Inst → Except SemError (List LocalTypeSource)
  | .MakeClosure ty _ _ => .ok [.declared (.Closure ty)]
  | .BinOp _ ty _ _ | .UnOp _ ty _ | .Load ty _ _ _
  | .AtomicLoad ty _ _ | .AtomicRMW _ ty _ _ _
  | .MakeAggregate ty _ _ | .ArraySplat ty _ | .ExtractField ty _ _
  | .InsertField ty _ _ _ | .ExtractElement ty _ _ | .InsertElement ty _ _ _
  | .Const ty _ | .Undef ty | .Copy ty _ | .Select ty _ _ _
  | .LoadSlot _ _ ty | .PtrMetadata _ ty _ | .PtrFromParts ty _ _ _
  | .SeqMapAddK ty _ _ | .SeqMapNot ty _ | .SeqMap ty _ _ => .ok [.declared ty]
  | .Cast _ _ ty _ => .ok [.declared ty]
  | .Overflow _ ty _ _ | .CmpXchg ty _ _ _ _ _ _ =>
    .ok [.declared ty, .declared .Bool]
  | .ICmp _ ty _ _ | .FCmp _ ty _ _ =>
    .ok [.declared (match ty with | .Vector n _ => .Vector n .Bool | _ => .Bool)]
  | .IsUnique _ => .ok [.declared .Bool]
  | .Alloca _ _ _ | .HeapAlloc _ _ _ _ | .GEP _ _ _ _ | .PtrData _ _
  | .NullPtr | .GlobalAddr _ | .OpenFrame _ | .BindSlot _ _ _ => .ok [.declared .Ptr]
  | .Borrow operand | .BorrowMut operand => .ok [.borrow operand]
  | .Call fid _ | .CallCannotUnwind fid _ | .Invoke fid _ _ _ _ =>
    match direct fid with
    | some signature => .ok (signature.returns.map LocalTypeSource.declared)
    | none => .error (.typeError "SSA types: direct callee header is absent")
  | .CallIndirect _ sig _ _ | .CallIndirectCannotUnwind _ sig _ _
  | .InvokeIndirect _ sig _ _ _ _ _ =>
    match indirect sig with
    | some signature => .ok (signature.returns.map LocalTypeSource.declared)
    | none => .error (.typeError "SSA types: indirect signature is absent")
  | .DialectOp op => .ok (op.resultTys.map LocalTypeSource.declared)
  | .LandingPad _ _ => .ok [.declared .Ptr, .declared .I32]
  | .Drop _ _ | .DropInvoke _ _ _ _ _ | .Store _ _ _ _ _
  | .AtomicStore _ _ _ _ | .Fence _ | .Br _ _ | .CondBr _ _ _ _ _
  | .Switch _ _ _ _ _ | .Return _ | .Assume _ | .Assert _ _ _
  | .AssertInvoke _ _ _ _ _ _ | .Unreachable | .EndBorrow _ | .Retain _
  | .Release _ | .Dealloc _ | .MemCopy _ _ _ _ | .MemSet _ _ _
  | .CloseFrame _ | .CoroSuspend _ _ _ _ | .Resume _ => .ok []

/-- Logical map work, independent of elapsed time and executable fuel.
    The sparse binary indexes use exact Nat ids; there are no hash collisions. -/
structure LocalTypeWork where
  declarations : Nat := 0
  declarationLookups : Nat := 0
  memoLookups : Nat := 0
  borrowEdges : Nat := 0
  resolvedDeclarations : Nat := 0
  declarationDepth : Nat := 0
  memoDepth : Nat := 0
  deriving Repr

/-- A finite inference result carries an executable bound of its actual
    lookup tree. The proof is erased at runtime and assumes no search-tree
    lookup or insertion law. Source transformations can reserve ids above
    both this bound and every source definition/operand. -/
structure LocalTypeInference where
  table : LocalTypeTable
  work : LocalTypeWork
  keyBound : Nat
  outsideBound : ∀ id : ValueId, keyBound ≤ id.index → table id = none

/-! The inference steps are named explicitly so kernel proofs can use the
verified index equations without unfolding its complete sparse tree. -/
namespace LocalTypeInference

abbrev DeclarationIndex := NatIndex LocalTypeSource

inductive LocalTypeResolution where
  | visiting
  | resolved (ty : Ty)

abbrev ResolutionIndex := NatIndex LocalTypeResolution

def addLocalTypeSource (state : DeclarationIndex × List ValueId)
    (id : ValueId) (source : LocalTypeSource) :
    Except SemError (DeclarationIndex × List ValueId) :=
  if state.fst.contains id.index then
    .error (.typeError "SSA types: duplicate value declaration")
  else .ok (state.fst.insert id.index source, id :: state.snd)

def addLocalTypeNode (direct : FuncId → Option FuncTyDef) (indirect : FuncTyTable)
    (state : DeclarationIndex × List ValueId) (node : Inst × List ValueId) :
    Except SemError (DeclarationIndex × List ValueId) := do
  let types ← localResultTypes direct indirect node.fst
  if types.length != node.snd.length then
    throw (.typeError "SSA types: instruction result count mismatch")
  (node.snd.zip types).foldlM (fun acc (id, source) => addLocalTypeSource acc id source) state

def borrowedLocalType : Ty → Ty
  | .FatPtr kind => .FatPtr kind
  | _ => .Ptr

/-- A borrow chain preserves a fat root and otherwise yields Ptr at every
    edge. Fill the entire traversed path once, without a recursive unwind. -/
def finishLocalTypePath (root : Ty) (path : List ValueId)
    (memo : ResolutionIndex) (work : LocalTypeWork) : ResolutionIndex × LocalTypeWork :=
  let ty := borrowedLocalType root
  let memo := path.foldl (fun table id => table.insert id.index (.resolved ty)) memo
  (memo, { work with resolvedDeclarations := work.resolvedDeclarations + path.length })

/-- Tail-recursive graph traversal. The exact declaration count bounds a
    simple path; a repeated visiting node is a cycle. Completed roots are
    shared by every later lookup, regardless of declaration order. -/
def resolveLocalType (declarations : DeclarationIndex) :
    Nat → ValueId → List ValueId → ResolutionIndex → LocalTypeWork →
      Except SemError (ResolutionIndex × LocalTypeWork)
  | 0, _, _, _, _ => .error (.typeError "SSA types: cyclic borrow declarations")
  | fuel + 1, id, path, memo, work =>
    let work := { work with memoLookups := work.memoLookups + 1 }
    match memo.find? id.index with
    | some (.resolved ty) => .ok (finishLocalTypePath ty path memo work)
    | some .visiting => .error (.typeError "SSA types: cyclic borrow declarations")
    | none =>
      let work := { work with declarationLookups := work.declarationLookups + 1 }
      match declarations.find? id.index with
      | none => .error (.typeError "SSA types: borrowed value has no declaration")
      | some (.declared ty) =>
        let memo := memo.insert id.index (.resolved ty)
        let work := { work with resolvedDeclarations := work.resolvedDeclarations + 1 }
        .ok (finishLocalTypePath ty path memo work)
      | some (.borrow operand) =>
        resolveLocalType declarations fuel operand (id :: path)
          (memo.insert id.index .visiting) { work with borrowEdges := work.borrowEdges + 1 }

end LocalTypeInference

open LocalTypeInference

/-- The shared inference implementation, with a bound certified from the
    final memo. Collection, resolution and refusal order are unchanged. -/
def inferLocalTypesWithEvidence (direct : FuncId → Option FuncTyDef) (indirect : FuncTyTable)
    (params : List (ValueId × Ty)) (nodes : List (Inst × List ValueId)) :
    Except SemError LocalTypeInference := do
  let initial : DeclarationIndex × List ValueId := (NatIndex.empty, [])
  let state ← params.foldlM
    (fun acc (id, ty) => addLocalTypeSource acc id (.declared ty)) initial
  let (declarations, ids) ← nodes.foldlM (addLocalTypeNode direct indirect) state
  let count := ids.length
  let initialMemo : ResolutionIndex := NatIndex.empty
  let (memo, work) ← ids.foldlM (fun (memo, work) id =>
    resolveLocalType declarations (count + 1) id [] memo work)
    (initialMemo, { declarations := count : LocalTypeWork })
  let work := { work with declarationDepth := declarations.depth
                          memoDepth := memo.depth }
  let table : LocalTypeTable := fun id => match memo.find? id.index with
    | some (.resolved ty) => some ty
    | _ => none
  pure { table := table
         work := work
         keyBound := memo.keyBound
         outsideBound := by
           intro id h
           change (match memo.find? id.index with
             | some (.resolved ty) => some ty
             | _ => none) = none
           have hFind : memo.find? id.index = none :=
             memo.outsideBound id.index h
           rw [hFind] }

/-- The diagnostic projection retains the existing table/work API. Each
    successful declaration is resolved once; no alternative inference path
    or configurable bound is introduced. -/
def inferLocalTypesWithWork (direct : FuncId → Option FuncTyDef) (indirect : FuncTyTable)
    (params : List (ValueId × Ty)) (nodes : List (Inst × List ValueId)) :
    Except SemError (LocalTypeTable × LocalTypeWork) := do
  let inferred ← inferLocalTypesWithEvidence direct indirect params nodes
  pure (inferred.table, inferred.work)

/-- Collect every parameter and actual result before resolution. Sparse ids,
    non-dominance serialization and arbitrarily long finite borrow paths use
    the same complete declaration graph; no execution budget is imposed. -/
def inferLocalTypes (direct : FuncId → Option FuncTyDef) (indirect : FuncTyTable)
    (params : List (ValueId × Ty)) (nodes : List (Inst × List ValueId)) :
    Except SemError LocalTypeTable := do
  let (table, _) ← inferLocalTypesWithWork direct indirect params nodes
  pure table

end TrustIr

#trustIrAxiomsExact TrustIr.localResultTypes == []

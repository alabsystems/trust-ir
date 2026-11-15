-- Copyright 2026 Andrew Yates | Apache-2.0
-- Prepared lookup views of actual decoded source and executable rows.
import TrustIr.DecodedModule

namespace TrustIrEval.FunctionLookup
open TrustIr

/-- Preserve occupancy even when the stored payload is an error. -/
def insertFirst {α : Type} (index : NatIndex α) (key : Nat) (value : α) : NatIndex α :=
  match index.find? key with
  | some _ => index
  | none => index.insert key value

/-- One source-order pass prepares the first raw decode status and the
    independent any-declaration view. A later declaration remains observable
    even when an earlier row with the same key has a body or a decode error. -/
def prepareSourceFrom : List Function → NatIndex (D Unit) → NatIndex Unit →
    NatIndex (D Unit) × NatIndex Unit
  | [], statuses, declarations => (statuses, declarations)
  | function :: rest, statuses, declarations =>
    let statuses := insertFirst statuses function.id.index (function.blocks.map (fun _ => ()))
    let declarations := if function.isDeclaration then
      declarations.insert function.id.index () else declarations
    prepareSourceFrom rest statuses declarations

/-- The caller supplies its actual eager, source-ordered executable conversion
    results. `some (.error _)` occupies the first matching key exactly as a
    successful body does; later duplicates cannot replace it. -/
def prepareDefsFrom : List (FuncId × D EvalFunction) → NatIndex (D EvalFunction) →
    NatIndex (D EvalFunction)
  | [], definitions => definitions
  | (id, result) :: rest, definitions =>
    prepareDefsFrom rest (insertFirst definitions id.index result)

/-- A data result keeps preparation outside the public query closures when
    these fields are captured by the actual EvalContext constructor. -/
structure Prepared where
  sourceStatuses : NatIndex (D Unit)
  executables : NatIndex (D EvalFunction)
  declarations : NatIndex Unit

/-- Prepare all three views without changing executable-body conversion order
    or eagerly propagating a retained per-function error. -/
def prepare (source : List Function) (definitions : List (FuncId × D EvalFunction)) : Prepared :=
  let sourceViews := prepareSourceFrom source NatIndex.empty NatIndex.empty
  { sourceStatuses := sourceViews.1
    executables := prepareDefsFrom definitions NatIndex.empty
    declarations := sourceViews.2 }

trustIrDenseMatch
def findFunction (prepared : Prepared) (id : FuncId) : Option EvalFunction :=
  match prepared.executables.find? id.index with
  | some (Except.ok function) => some function
  | _ => none

def isDeclared (prepared : Prepared) (id : FuncId) : Bool :=
  prepared.declarations.contains id.index

trustIrDenseMatch
/-- Match the original first-raw-row error priority, then the first retained
    executable metadata error. Missing/declaration status and body lookup stay
    independent; this is not an eager whole-module admission check. -/
def findError (prepared : Prepared) (id : FuncId) : Option SemError :=
  match prepared.sourceStatuses.find? id.index with
  | some (Except.error (.unsupported feature)) => some (.unsupported .interproceduralCall
      (trustIrStringBuild s!"function {id.index} body is unsupported: {feature}"))
  | some (Except.error (.malformed message)) => some (.typeError
      (trustIrStringBuild s!"function {id.index} body is malformed: {message}"))
  | some (Except.ok ()) =>
    match prepared.executables.find? id.index with
    | some (Except.error (.malformed message)) => some (.typeError message)
    | some (Except.error (.unsupported feature)) => some (.unsupported .ssaTypeTable feature)
    | _ => none
  | none => none

end TrustIrEval.FunctionLookup

/-- info: 'TrustIrEval.FunctionLookup.findFunction' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIrEval.FunctionLookup.findFunction

/-- info: 'TrustIrEval.FunctionLookup.findFunction.match_1' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIrEval.FunctionLookup.findFunction.match_1

/-- info: 'TrustIrEval.FunctionLookup.findError' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIrEval.FunctionLookup.findError

/-- info: 'TrustIrEval.FunctionLookup.findError.match_1' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIrEval.FunctionLookup.findError.match_1

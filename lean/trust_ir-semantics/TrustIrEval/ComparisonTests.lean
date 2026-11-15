-- Copyright 2026 Andrew Yates | Author: Andrew Yates | Apache-2.0
-- Direct runtime-value refusal controls; malformed values here are not claims
-- about validator-admitted modules. Run: lake env lean --run TrustIrEval/ComparisonTests.lean
import TrustIrRuntime
import TrustIrEval.Run

open TrustIr TrustIrEval

private def ops : List ICmpOp := [.Eq, .Ne, .Ult, .Ule, .Ugt, .Uge, .Slt, .Sle, .Sgt, .Sge]

private def runCompare (op : ICmpOp) (ty : Ty) (lhs rhs : Value)
    (model : ByteModel := .le64) : Except SemError Value :=
  let state := { MachineState.empty with
    locals := ValueMap.empty.set ⟨0⟩ lhs |>.set ⟨1⟩ rhs
    nextValueId := 2 }
  match Sem.run (semICmpInst op ty ⟨0⟩ ⟨1⟩ model) state with
  | .error error => .error error
  | .ok (id, final) =>
    match final.lookupValue id with
    | some value => .ok value
    | none => .error (.typeError "comparison result was not bound")

private def require (label : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError label)

private def expectValue (label : String) (actual : Except SemError Value) (expected : Value) : IO Unit :=
  require label (match actual with
    | .ok value => Observation.renderGraphSpec [value] == Observation.renderGraphSpec [expected]
    | .error _ => false)

private def expectError (label code : String) (actual : Except SemError Value) : IO Unit :=
  require label (match actual with
    | .error error => error.code == code
    | .ok _ => false)

def main : IO Unit := do
  for op in ops do
    for model in [ByteModel.le32, .le64] do
      expectValue "scalar Bool comparison binds a Bool"
        (runCompare op .Bool (.bool true) (.bool false) model)
        (.bool (semBoolICmp op true false))
      for poison in [Value.undef .Bool, .partial [none], .uninit] do
        expectError "left root poison precedes malformed right operand" "ub"
          (runCompare op .Bool poison (.int 1 0) model)
        expectError "right root poison precedes scalar shape checking" "ub"
          (runCompare op .Bool (.int 1 0) poison model)
      expectError "Bool rejects an integer payload" "type_error"
        (runCompare op .Bool (.int 1 1) (.int 1 0) model)
      expectError "integer rejects Bool payloads" "type_error"
        (runCompare op .I8 (.bool true) (.bool false) model)
      expectError "declared integer width is checked" "type_error"
        (runCompare op .I8 (.int 16 1) (.int 16 0) model)
      expectError "float type cannot borrow integer comparison" "type_error"
        (runCompare op .F32 (.int 32 1) (.int 32 0) model)
      for count in [1, 3, 5, 17, 257] do
        let lhs := List.replicate count (Value.int 8 255)
        let rhs := List.replicate count (Value.int 8 0)
        expectValue "arbitrary positive integer vector census"
          (runCompare op (.Vector count .I8) (.vector lhs) (.vector rhs) model)
          (.vector (List.replicate count (.bool (semICmp op 8 255 0))))
        expectValue "arbitrary positive Bool vector census"
          (runCompare op (.Vector count .Bool)
            (.vector (List.replicate count (.bool true)))
            (.vector (List.replicate count (.bool false))) model)
          (.vector (List.replicate count (.bool (semBoolICmp op true false))))
      for laneTy in [Ty.Bool, .I8] do
        let defined := if laneTy == .Bool then Value.bool false else .int 8 0
        let good := .vector [defined, defined, defined]
        expectError "declared census rejects short left vector" "type_error"
          (runCompare op (.Vector 3 laneTy) (.vector [defined, defined]) good model)
        expectError "declared census rejects long right vector" "type_error"
          (runCompare op (.Vector 3 laneTy) good (.vector [defined, defined, defined, defined]) model)
        expectError "vector type rejects scalar payloads" "type_error"
          (runCompare op (.Vector 3 laneTy) defined defined model)
        for poison in [Value.undef laneTy, .partial [none], .uninit] do
          expectError "left poison lane is inspected" "ub"
            (runCompare op (.Vector 3 laneTy) (.vector [defined, poison, defined]) good model)
          expectError "right poison lane is inspected" "ub"
            (runCompare op (.Vector 3 laneTy) good (.vector [defined, poison, defined]) model)
      expectError "Bool vector rejects integer lanes" "type_error"
        (runCompare op (.Vector 1 .Bool) (.vector [.int 1 0]) (.vector [.bool false]) model)
      expectError "integer vector rejects Bool lanes" "type_error"
        (runCompare op (.Vector 1 .I8) (.vector [.bool false]) (.vector [.int 8 0]) model)
      expectError "integer vector rejects a mismatched lane width" "type_error"
        (runCompare op (.Vector 1 .I8) (.vector [.int 16 0]) (.vector [.int 8 0]) model)
      expectError "zero lane vectors remain refused" "unsupported.vector_type"
        (runCompare op (.Vector 0 .Bool) (.vector []) (.vector []) model)
      for laneTy in [Ty.Isize, .Usize, .I128, .U128, .F32, .Ptr, .Vector 1 .Bool] do
        expectError "unadmitted comparison lane types remain refused" "unsupported.vector_type"
          (runCompare op (.Vector 1 laneTy) (.vector [.int 64 0]) (.vector [.int 64 0]) model)
  expectValue "Bool signed true is minus one"
    (runCompare .Slt .Bool (.bool true) (.bool false)) (.bool true)
  expectValue "Bool unsigned true is one"
    (runCompare .Ult .Bool (.bool true) (.bool false)) (.bool false)
  expectValue "32 bit usize compares at the selected width"
    (runCompare .Ult .Usize (.int 32 0) (.int 32 1) .le32) (.bool true)
  expectError "32 bit usize rejects a 64 bit payload" "type_error"
    (runCompare .Ult .Usize (.int 64 0) (.int 64 1) .le32)
  IO.println "Bool and vector ICmp runtime checks passed"

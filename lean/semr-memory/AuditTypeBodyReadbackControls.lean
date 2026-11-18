import Lean

/-! Synthetic ConstantInfo data checks for the audit expression read-back only.
The changed-body theorem below is intentionally invalid as a declaration; it is
never added to an environment or replayed. No proof, axiom, admission or project
module is introduced. This file is an UNRUN Source test proposal for modern Lean.
The comparison checks exact type/body expressions, not all ConstantInfo fields. -/

open Lean

private def sameTypeBody (actual expected : ConstantInfo) : Bool :=
  let sameValue :=
    match actual.value? (allowOpaque := true), expected.value? (allowOpaque := true) with
    | some actualValue, some expectedValue => Expr.equal actualValue expectedValue
    | none, none => true
    | _, _ => false
  Expr.equal actual.type expected.type && sameValue

private def theoremData (type value : Expr) : ConstantInfo :=
  ConstantInfo.thmInfo {
    name := `AuditReadbackSynthetic
    levelParams := []
    type := type
    value := value }

private def definitionData (type value : Expr) : ConstantInfo :=
  ConstantInfo.defnInfo {
    name := `AuditReadbackSyntheticDefinition
    levelParams := []
    type := type
    value := value
    hints := .opaque
    safety := .safe }

open Elab Command in
run_cmd do
  let check (label : String) (actual expected : Bool) : CommandElabM Unit := do
    unless actual == expected do
      throwError "audit type/body control failed: {label}"
  let good := theoremData (mkConst ``True) (mkConst ``True.intro)
  let changed := theoremData (mkConst ``True) (mkConst ``False.elim)
  check "theorem exact positive" (sameTypeBody good good) true
  check "old default value option omits theorem bodies" (good.value? == changed.value?) true
  check "new comparison rejects changed theorem body" (sameTypeBody good changed) false
  check "new comparison rejects changed theorem type"
    (sameTypeBody good (theoremData (mkConst ``False) (mkConst ``True.intro))) false
  let typeX := Expr.forallE `x (mkConst ``Nat) (mkConst ``Nat) .default
  let typeY := Expr.forallE `y (mkConst ``Nat) (mkConst ``Nat) .default
  let typeImplicit := Expr.forallE `x (mkConst ``Nat) (mkConst ``Nat) .implicit
  let bodyX := Expr.lam `x (mkConst ``Nat) (Expr.bvar 0) .default
  let bodyY := Expr.lam `y (mkConst ``Nat) (Expr.bvar 0) .default
  let bodyImplicit := Expr.lam `x (mkConst ``Nat) (Expr.bvar 0) .implicit
  let original := definitionData typeX bodyX
  check "definition exact positive" (sameTypeBody original original) true
  check "type binder name preserved" (sameTypeBody original (definitionData typeY bodyX)) false
  check "type binder annotation preserved"
    (sameTypeBody original (definitionData typeImplicit bodyX)) false
  check "definition body binder name preserved"
    (sameTypeBody original (definitionData typeX bodyY)) false
  check "definition body binder annotation preserved"
    (sameTypeBody original (definitionData typeX bodyImplicit)) false
  check "definition body literal preserved"
    (sameTypeBody (definitionData (mkConst ``Nat) (mkNatLit 0))
      (definitionData (mkConst ``Nat) (mkNatLit 1))) false
  let constructor <- getConstInfo ``Nat.zero
  check "genuine imported constructor reflexive none values" (sameTypeBody constructor constructor) true
  check "some versus none value refuses"
    (sameTypeBody constructor (definitionData constructor.type (mkNatLit 0))) false
  check "none versus some value refuses"
    (sameTypeBody (definitionData constructor.type (mkNatLit 0)) constructor) false
  logInfo "audit exact type/body synthetic controls complete; no declaration replay or admission"

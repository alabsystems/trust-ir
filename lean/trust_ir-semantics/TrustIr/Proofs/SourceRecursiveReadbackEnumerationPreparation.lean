-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.SourceRecursiveReadbackFixtureData

/- Enable kernel reduction through the imported mutual compiler equations.
The metadata is local to these proofs; no executable definition is replaced. -/
run_cmd do
  if Lean.versionString == "4.30.0-rc2" then
    let env ← Lean.getEnv
    let mut registered := 0
    for (n, _) in env.constants.map₁.toList do
      if n.toString.endsWith "TrustIr.SourceLayout.compileTy.eq_def" ||
         n.toString.endsWith "TrustIr.SourceLayout.compileTypes.eq_def" then
        Lean.Elab.Command.elabCommand (← `(command| attribute [local cbv_eval] $(Lean.mkIdent n):ident))
        registered := registered + 1
    unless registered == 2 do
      Lean.throwError "expected the two original layout compiler equations"
  else if Lean.versionString != "4.8.0" then
    Lean.throwError "unsupported compiler for layout equation reduction"

namespace TrustIr.AggregateMemory.RecursiveReadbackControls
open SourceLayout
open FixtureData
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096























private theorem enumPrepared : (prepare enumSource []).query (.Enum ⟨0⟩) = .ok enumPlan := by
  trustIrCompilerProof {
    dsimp only [enumSource,definition,enumPlan,enumInfo,enumVariants,root,rootTy,rootFields,fat,kind,tail,tailTy,tailFields,
      array,arrayTy,element,elementTy,elementFields,byte,boolean,pointer,character]
    rfl
  } {
    dsimp only [enumSource,definition,enumPlan,enumInfo,enumVariants,root,rootTy,rootFields,fat,kind,tail,tailTy,tailFields,
      array,arrayTy,element,elementTy,elementFields,byte,boolean,pointer,character]
    trustIrReduce
  }

/-- Internal fixture certificate for the actual enum source/query; no presence-to-success inference. -/
theorem enum_preparation_fixture_support :
    (prepare enumSource []).query (.Enum ⟨0⟩) = .ok enumPlan :=
  enumPrepared

end TrustIr.AggregateMemory.RecursiveReadbackControls

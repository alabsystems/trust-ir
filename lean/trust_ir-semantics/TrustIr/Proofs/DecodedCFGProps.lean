-- Copyright 2026 Andrew Yates | Apache-2.0
-- Exact correspondence to the pre-index decoded conversion, proof-only.
import TrustIr.DecodedContext
import TrustIr.Proofs.GenericCoroIndexedCFG

namespace TrustIrEval.DecodedCFG
open TrustIr

-- Select before elaboration; preserve the original declaration syntax tree.
macro "trustIrDecodedCFGOriginalMatchers " original:command : command => do
  if Lean.versionString == "4.8.0" then pure original
  else if Lean.versionString == "4.30.0-rc2" then
    let signatureName := Lean.mkIdent
      (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "evalFunctionListSpec") "match_1")
    let pairName := Lean.mkIdent
      (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "evalFunctionListSpec") "match_2")
    let errorName := Lean.mkIdent
      (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "evalFunctionListSpec") "match_3")
    let originalUniverse := Lean.mkIdent (Lean.Name.str Lean.Name.anonymous "u_1")
    let originalLevel ← `(level| $originalUniverse:ident)
    let signatureHelper ← `(command| run_cmd do
      let helperName := `TrustIrEval.DecodedCFG.evalFunctionListSpec.match_1
      if ((← Lean.getEnv).find? helperName).isSome then
        throwError "original signature matcher already exists; refusing replacement"
      let u := Lean.Name.str Lean.Name.anonymous "u_1"
      let selectedName := Lean.Name.num
        (Lean.Name.str (Lean.Name.str
          (Lean.Name.num `x.«_@».TrustIr.Proofs.DecodedCFGProps 3072574140)
          "_hygCtx") "_hyg") 75
      let functionType := Lean.Expr.const `TrustIr.FuncTyDef []
      let optionType := Lean.Expr.app (Lean.Expr.const `Option [.zero]) functionType
      let noneValue := Lean.Expr.app (Lean.Expr.const `Option.none [.zero]) functionType
      let someValue := Lean.mkAppN (Lean.Expr.const `Option.some [.zero]) #[functionType, .bvar 0]
      let motiveType := Lean.Expr.forallE selectedName optionType (.sort (.param u)) .default
      let someHandlerType := Lean.Expr.forallE
        (Lean.Name.str Lean.Name.anonymous "s") functionType (.app (.bvar 2) someValue) .default
      -- The original recorded type requires this binder to be literally anonymous.
      let noneHandlerType := Lean.Expr.forallE Lean.Name.anonymous
        (Lean.Expr.const `Unit []) (.app (.bvar 3) noneValue) .default
      let declaredType := Lean.Expr.forallE
        (Lean.Name.str Lean.Name.anonymous "motive") motiveType
        (.forallE selectedName optionType
          (.forallE (Lean.Name.str Lean.Name.anonymous "h_1") someHandlerType
            (.forallE (Lean.Name.str Lean.Name.anonymous "h_2") noneHandlerType
              (.app (.bvar 3) (.bvar 2)) .default) .default) .default) .default
      let eliminatorBody := Lean.mkAppN (Lean.Expr.const `Option.casesOn [.param u, .zero]) #[
        functionType,
        .lam (Lean.Name.str Lean.Name.anonymous "x") optionType (.app (.bvar 4) (.bvar 0)) .default,
        .bvar 2,
        .app (.bvar 0) (.const `Unit.unit []),
        .lam (Lean.Name.str Lean.Name.anonymous "s") functionType (.app (.bvar 2) (.bvar 0)) .default]
      let declaredValue := Lean.Expr.lam
        (Lean.Name.str Lean.Name.anonymous "motive") motiveType
        (.lam selectedName optionType
          (.lam (Lean.Name.str Lean.Name.anonymous "h_1") someHandlerType
            (.lam (Lean.Name.str Lean.Name.anonymous "h_2") noneHandlerType
              eliminatorBody .default) .default) .default) .default
      Lean.Elab.Command.liftCoreM <| Lean.addAndCompile (.defnDecl {
        name := helperName, levelParams := [u], type := declaredType,
        value := declaredValue, hints := .abbrev, safety := .safe }))
    let pairHelper ← `(command|
      def $pairName:ident.{$originalUniverse:ident}
          (motive : (BlockId × BasicBlock) → Sort $originalLevel:level)
          (selected : BlockId × BasicBlock)
          (h_1 : (fst : BlockId) → (block : BasicBlock) → motive (fst, block)) :
          motive selected := Prod.casesOn selected (fun fst block => h_1 fst block))
    let errorHelper ← `(command|
      def $errorName:ident.{$originalUniverse:ident}
          (motive : Except SemError LocalTypeTable → Sort $originalLevel:level)
          (selected : Except SemError LocalTypeTable)
          (h_1 : (table : LocalTypeTable) → motive (.ok table))
          (h_2 : (message : String) → motive (.error (.typeError message)))
          (h_3 : (error : SemError) → motive (.error error)) : motive selected :=
        Except.casesOn selected
          (fun error => SemError.casesOn error
            (fun message => h_3 (.ub message))
            (fun message site => h_3 (.panic message site))
            (fun message => h_2 message)
            (fun feature message => h_3 (.unsupported feature message))
            (h_3 .outOfFuel)
            (fun message => h_3 (.outOfMemory message))
            (fun addr state => h_3 (.unwinding addr state)))
          (fun table => h_1 table))
    let rewrite (stx : Lean.Syntax) : StateT (Nat × Nat × Nat) Lean.MacroM (Option Lean.Syntax) := do
      match stx with
      | `(doElem| match $selected:term with
          | some $signature:ident => $available:doSeq
          | none => $missing:doSeq) =>
        modify fun counts => (counts.1 + 1, counts.2.1, counts.2.2)
        let replacement ← `(doElem|
          $signatureName:ident (fun (_ : Option FuncTyDef) => D FuncTyDef)
            $selected:term (fun $signature:ident => do $available:doSeq)
            (fun _ => do $missing:doSeq))
        pure (some replacement.raw)
      | `(term| fun (_, $block:ident) => $body:term) =>
        modify fun counts => (counts.1, counts.2.1 + 1, counts.2.2)
        let replacement ← `(term| fun row =>
          $pairName:ident (fun (_ : BlockId × BasicBlock) => List (Inst × List ValueId)) row
            (fun _ $block:ident => $body:term))
        pure (some replacement.raw)
      | `(doElem| match $selected:term with
          | .ok $table:ident => $okay:doSeq
          | .error (.typeError $message:ident) => $typed:doSeq
          | .error $error:ident => $other:doSeq) =>
        modify fun counts => (counts.1, counts.2.1, counts.2.2 + 1)
        let replacement ← `(doElem|
          $errorName:ident (fun (_ : Except SemError LocalTypeTable) => D LocalTypeTable)
            $selected:term (fun $table:ident => do $okay:doSeq)
            (fun $message:ident => do $typed:doSeq) (fun $error:ident => do $other:doSeq))
        pure (some replacement.raw)
      | _ => pure none
    let (transformed, counts) ← (original.raw.replaceM rewrite).run (0, 0, 0)
    unless counts == (1, 1, 1) do
      Lean.Macro.throwError "original CFG matcher syntax changed: expected exactly one signature lookup, pair callback and declaredTypes match"
    pure ⟨Lean.mkNullNode #[signatureHelper.raw, pairHelper.raw, errorHelper.raw, transformed]⟩
  else Lean.Macro.throwError "unsupported compiler for original CFG matchers"

trustIrDecodedCFGOriginalMatchers
/-- The genuine prior conversion, including inference/error order and the
    original list CFG. This specification is never a runtime fallback. -/
noncomputable def evalFunctionListSpec (signatures : Array FuncTyDef)
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
  pure { body := { paramTys := sig.params, returnTys := sig.returns, abi := sig.abi, isVararg := sig.isVararg }
         cfg := cfgOf blocks
         entryBlock := f.entry
         callingConv := f.callingConvention
         localTypes := some localTypes }

/-- Same first-match raw rows at every Nat-backed BlockId. -/
theorem indexedCFG_eq_cfgOf (blocks : List (BlockId × BasicBlock)) :
    (TrustIr.GenericCoro.IndexedCFG.indexedCFG blocks).cfg = cfgOf blocks := by
  exact TrustIr.GenericCoro.IndexedCFG.indexedCFG_eq_cfgOf blocks

/-- Full conversion equality for all raw signatures, functions and rows.
    No validity, uniqueness, metadata-success or resource premise is added. -/
theorem evalFunctionOfWithTypes_eq_listSpec (signatures : Array FuncTyDef)
    (direct : FuncId → Option FuncTyDef) (function : Function)
    (blocks : List (BlockId × BasicBlock)) :
    evalFunctionOfWithTypes signatures direct function blocks =
      evalFunctionListSpec signatures direct function blocks := by
  trustIrCompilerProof {
  unfold evalFunctionOfWithTypes evalFunctionListSpec
  simp only [indexedCFG_eq_cfgOf]
  rfl
  } {
    unfold evalFunctionOfWithTypes evalFunctionListSpec
    simp only [indexedCFG_eq_cfgOf]
    unfold evalFunctionListSpec.match_2 evalFunctionListSpec.match_3
    cases signature : trustIrArrayGet? signatures function.ty.index with
    | none => rfl
    | some signature =>
      generalize (inferLocalTypes direct (fun sig => trustIrArrayGet? signatures sig.index)
        (trustIrListBind blocks (fun row => row.snd.params))
        (trustIrListBind blocks (fun (_, block) =>
          bodyInstsWithResultDests block.body block.bodyResultDests ++
            [(block.terminator, block.terminatorResultDests)]))) = declaredTypes
      cases declaredTypes with
      | ok table => rfl
      | error error => cases error <;> rfl
  }

end TrustIrEval.DecodedCFG

-- Copyright 2026 Andrew Yates | Apache-2.0
-- Typed source-body binding only. This cannot grant runtime correspondence.
import Lean
import TrustIrRuntime.ImageMap

open Lean Meta Elab Command

namespace TrustIrEval.ImageMapStepBinding

private def withoutMetadata : Expr → Expr
  | .mdata _ body => withoutMetadata body
  | expression => expression

-- Do not beta/delta-reduce lets: those reductions erase eager construction.
private def rawLambdaBody : Nat → Expr → Option Expr
  | 0, expression => some (withoutMetadata expression)
  | count + 1, expression => match withoutMetadata expression with
    | .lam _ _ body _ => rawLambdaBody count body
    | _ => none

private def boundUses (index : Nat) : Expr → Nat
  | .bvar slot => if slot == index then 1 else 0
  | .app function argument => boundUses index function + boundUses index argument
  | .lam _ domain body _ | .forallE _ domain body _ =>
    boundUses index domain + boundUses (index + 1) body
  | .letE _ type value body _ =>
    boundUses index type + boundUses index value + boundUses (index + 1) body
  | .mdata _ body | .proj _ _ body => boundUses index body
  | _ => 0

private def eagerMissPrelude (index : Nat) : Expr → Bool
  | .mdata _ body => eagerMissPrelude index body
  | .letE _ _ value body _ =>
    boundUses index value != 0 || eagerMissPrelude (index + 1) body
  | _ => false

/-- Re-run at the consumer boundary: importing a compiled module alone does not
    execute its earlier elaboration commands. This check grants no proof grade. -/
def checkSourceBodies : CommandElabM Unit := do
  let env ← getEnv
  let find (text : String) := env.constants.toList.filter (fun entry => entry.1.toString == text)
  let implementations := find "_private.TrustIrRuntime.ImageMap.0.TrustIr.ByteImage.ImageMapRuntime.uncached"
  let recursiveCalls := find "_private.TrustIrRuntime.ImageMap.0.TrustIr.ByteImage.ImageMapRuntime.visit"
  unless implementations.length == 1 && recursiveCalls.length == 1 do
    throwError "uncached/visit source identities are absent or ambiguous"
  let implementation := implementations.head!
  let recursiveCall := recursiveCalls.head!
  unless implementation.2.isUnsafe && recursiveCall.2.isUnsafe do
    throwError "runtime safety boundary changed"
  let .defnInfo definition := implementation.2 | throwError "uncached is not an inspectable definition"
  let some shared := env.find? ``TrustIr.ByteImage.Tree.mapStep | throwError "shared safe step absent"
  if shared.isUnsafe then throwError "shared constructor step became unsafe"
  let some (.thmInfo _) := env.find? ``TrustIr.ByteImage.Tree.mapStep_refines |
    throwError "shared-step refinement theorem absent"
  liftTermElabM do
    lambdaTelescope definition.value fun parameters body => do
      unless parameters.size == 3 do throwError "uncached source binder shape changed"
      let arguments := body.getAppArgs
      unless body.getAppFn.constName? == some ``TrustIr.ByteImage.Tree.mapStep && arguments.size == 5 do
        throwError "runtime uncached body bypasses the proved shared constructor step: {body}"
      unless arguments[1]! == parameters[0]! && arguments[3]! == parameters[1]! && arguments[4]! == parameters[2]! do
        throwError "runtime changed the mapping function, extent or input tree"
      let expectedVisit := mkApp (mkConst recursiveCall.1) parameters[0]!
      unless ← isDefEq arguments[2]! expectedVisit do
        throwError "runtime changed the recursive child callback"
  let .defnInfo visitor := recursiveCall.2 | throwError "visit is not an inspectable definition"
  let some sharedCache := env.find? ``TrustIr.ByteImage.Tree.mapCacheStep |
    throwError "shared safe cache transition absent"
  if sharedCache.isUnsafe then throwError "shared cache transition became unsafe"
  let some (.thmInfo _) := env.find? ``TrustIr.ByteImage.Tree.mapCacheStep_refines |
    throwError "shared cache-step refinement theorem absent"
  -- Inspect unreduced bodies before Meta's definitional equality can erase lets.
  let some rawVisit := rawLambdaBody 3 visitor.value |
    throwError "runtime visit lambda structure changed"
  unless rawVisit.getAppFn.constName? == some ``TrustIr.ByteImage.Tree.mapCacheStep do
    throwError "runtime visit has eager wrapper instead of a direct shared cache call"
  let rawArguments := rawVisit.getAppArgs
  unless rawArguments.size == 4 do throwError "runtime visit argument structure changed"
  let .lam _ _ rawThunkBody _ := withoutMetadata rawArguments[2]! |
    throwError "runtime visit cache callback is not an explicit Unit thunk"
  unless (withoutMetadata rawThunkBody).getAppFn.constName? == some implementation.1 do
    throwError "runtime visit thunk constructs something before uncached"
  let .defnInfo cacheDefinition := sharedCache | throwError "shared cache body is unavailable"
  let some rawCache := rawLambdaBody 5 cacheDefinition.value |
    throwError "shared cache lambda structure changed"
  let .letE _ _ missClosure branches _ := rawCache |
    throwError "shared cache must first construct its delayed miss closure"
  let .lam _ _ _ _ := withoutMetadata missClosure |
    throwError "shared cache forces the callback before its miss closure"
  -- After five binders the callback is #2; the new miss let shifts it to #3.
  unless boundUses 2 missClosure == 1 && boundUses 3 branches == 0 && boundUses 0 branches == 2
      && !eagerMissPrelude 0 branches do
    throwError "shared cache callback force escaped miss-only custody"
  liftTermElabM do
    lambdaTelescope visitor.value fun parameters body => do
      unless parameters.size == 3 do throwError "visit source binder shape changed"
      let arguments := body.getAppArgs
      unless body.getAppFn.constName? == some ``TrustIr.ByteImage.Tree.mapCacheStep && arguments.size == 4 do
        throwError "runtime visit bypasses the proved shared cache transition: {body}"
      unless arguments[1]! == parameters[1]! && arguments[3]! == parameters[2]! do
        throwError "runtime cache step changed extent or input tree"
      let expectedCall := mkAppN (mkConst implementation.1) parameters
      let expectedUncached := mkLambda `_unit .default (mkConst ``Unit) expectedCall
      unless ← isDefEq arguments[2]! expectedUncached do
        throwError "runtime cache step changed delayed uncached callback/function/input"
      let address ← mkAppM ``ptrAddrUnsafe #[parameters[2]!]
      let expectedKey ← mkAppM ``Prod.mk #[parameters[1]!, address]
      unless ← isDefEq arguments[0]! expectedKey do
        throwError "runtime cache step changed size/pointer key"
  logInfo "IMAGE_MAP_UNCACHED_SHARED_BODY_BOUND recursive_child_cache_and_machine_obligations=UNPROVED"
  logInfo "IMAGE_MAP_CACHE_FORCE_CUSTODY delayed_callback_occurrences=1 branch_callback_occurrences=0 miss_uses=2"
  logInfo "IMAGE_MAP_VISIT_SHARED_CACHE_BODY_BOUND key_hash_retention_and_machine_obligations=UNPROVED"

end TrustIrEval.ImageMapStepBinding

run_cmd TrustIrEval.ImageMapStepBinding.checkSourceBodies

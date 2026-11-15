-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import TrustIr.Proofs.FrameCheckedCalls
import TrustIr.Proofs.GenericCoroPrefixIndirect

namespace TrustIr.FrameLifetime
open GenericCoro GenericCoro.Prefix

private theorem append_member {α : Type} (left right : List α) (value : α)
    (member : value ∈ left ++ right) : value ∈ left ∨ value ∈ right := by
  induction left with
  | nil => exact Or.inr member
  | cons first rest ih =>
    cases member with
    | head => exact Or.inl (.head _)
    | tail _ member =>
      cases ih member with
      | inl found => exact Or.inl (.tail _ found)
      | inr found => exact Or.inr found

/-- Typed closure application prepends the original captures to the original
arguments after all contract, capture and argument checks succeed. -/
theorem closure_call_arguments (ctx : EvalContext) (cid : ClosureTyId) (fn : FuncId)
    (captures args : List Value) (sig : FuncTyId) (conv : CallingConv)
    (resolved : FuncId × List Value)
    (run : closureCall ctx cid fn captures sig args conv = .ok resolved) :
    resolved = (fn,captures ++ args) := by
  unfold closureCall at run
  simp only [bind, pure, Except.bind, Except.pure, throw, throwThe, MonadExceptOf.throw] at run
  repeat' first
    | exact (Except.ok.inj run).symm
    | contradiction
    | split at run

theorem closure_call_arguments_minted (bound : Nat) (ctx : EvalContext)
    (cid : ClosureTyId) (fn : FuncId) (captures args : List Value)
    (sig : FuncTyId) (conv : CallingConv) (resolved : FuncId × List Value)
    (held : MintedValue bound (.typedClosure cid fn captures)) (incoming : MintedArgs bound args)
    (run : closureCall ctx cid fn captures sig args conv = .ok resolved) :
    MintedArgs bound resolved.2 := by
  rw [closure_call_arguments ctx cid fn captures args sig conv resolved run]
  have validCaptures := (mintedValue_iff_shape bound (.typedClosure cid fn captures)).1 held
  intro value member
  cases append_member captures args value member with
  | inl found => exact validCaptures value found
  | inr found => exact incoming value found

private theorem pure_arguments_success (bound : Nat) (id : FuncId) (args : List Value)
    (s final : MachineState) (resolved : FuncId × List Value) (valid : MintedArgs bound args)
    (run : Sem.run (pure (id,args) : Sem (FuncId × List Value)) s = .ok (resolved,final)) :
    final = s ∧ MintedArgs bound resolved.2 := by
  cases run
  exact ⟨rfl,valid⟩

/-- Raw pointer signature validation preserves the original argument list and
all state, without assuming that its ABI/signature checks independently pass. -/
theorem raw_indirect_arguments_success (bound : Nat) (ctx : EvalContext) (address : Addr)
    (sig : FuncTyId) (args : List Value) (s final : MachineState)
    (resolved : FuncId × List Value) (incoming : MintedArgs bound args)
    (run : Sem.run (rawIndirectArguments ctx address sig args) s = .ok (resolved,final)) :
    final = s ∧ MintedArgs bound resolved.2 := by
  unfold rawIndirectArguments requireUntypedAbi at run
  simp only [pure_bind] at run
  repeat' first
    | exact pure_arguments_success bound _ args s final resolved incoming run
    | contradiction
    | (change Except.error _ = Except.ok _ at run; contradiction)
    | split at run

/-- All three original indirect argument paths preserve incoming frame
identities. Typed closures additionally transport their recursively valid
captures; raw pointers and FnDef values retain their actual checks. -/
theorem indirect_arguments_success (bound : Nat) (ctx : EvalContext) (held : Value)
    (address : Addr) (sig : FuncTyId) (args : List Value) (conv : CallingConv)
    (s final : MachineState) (resolved : FuncId × List Value)
    (validHeld : MintedValue bound held) (incoming : MintedArgs bound args)
    (run : Sem.run (indirectArguments ctx held address sig args conv) s = .ok (resolved,final)) :
    final = s ∧ MintedArgs bound resolved.2 := by
  cases held
  case fnDef held fn =>
    cases checked : functionCall ctx held fn sig with
    | error error => simp only [indirectArguments,checked] at run; cases run
    | ok id =>
      simp only [indirectArguments,checked] at run
      exact pure_arguments_success bound id args s final resolved incoming run
  case typedClosure cid fn captures =>
    cases checked : closureCall ctx cid fn captures sig args conv with
    | error error => simp only [indirectArguments,checked] at run; cases run
    | ok prepared =>
      simp only [indirectArguments,checked] at run
      change Except.ok (prepared,s) = Except.ok (resolved,final) at run
      cases run
      exact ⟨rfl,closure_call_arguments_minted bound ctx cid fn captures args sig conv _ validHeld incoming checked⟩
  all_goals exact raw_indirect_arguments_success bound ctx address sig args s final resolved incoming run

end TrustIr.FrameLifetime

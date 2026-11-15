-- Copyright 2026 Andrew Yates
-- Author: Andrew Yates <andrewyates.name@gmail.com>
-- Licensed under the Apache License, Version 2.0
--
-- Amendment D, Part 1 (`docs/SPEC_RATIFICATIONS.md` §20): a drop is a call
-- of its type's glue.
--
-- The evaluator resolves every drop of a block through the context's
-- drop-glue table BEFORE dispatch (`EvalContext.resolveBlock` in
-- `stepNWithContext`), so a resolved `Drop` literally runs the `Call` rule
-- and a resolved `DropInvoke` the `Invoke` rule. This file proves:
--
--   * `resolveDrop_drop` / `resolveDrop_dropInvoke`: with a row, a drop IS a
--     call (an invoke) of its glue on the place;
--   * `resolveDrop_unresolved`: without a row it is left as is;
--   * `resolveDrop_idem`: resolution is idempotent;
--   * `stepNWithContext_resolveDrops`: running a CFG IS running the same CFG
--     with every drop rewritten to its call (`EvalContext.resolveCfg`), for
--     every fuel, depth, block and argument list — the producer-side
--     "resolution rewrite" is an identity of the evaluator, not a trusted
--     step;
--   * `drop_unresolved_is_unsupported`: an unresolved drop (and its twin) is
--     the structured `unsupported.destructor`, never a no-op.

import TrustIr.Semantics.Eval

namespace TrustIr

/-- With a drop-glue row for `ty`, a `Drop` IS a `Call` of the glue on the
    place. -/
theorem resolveDrop_drop (ctx : EvalContext) (ty : Ty) (p : ValueId) (g : FuncId)
    (h : ctx.dropGlue ty = some g) :
    ctx.resolveDrop (.Drop ty p) = .Call g [p] := by
  simp [EvalContext.resolveDrop, h]

/-- With a drop-glue row for `ty`, a `DropInvoke` IS an `Invoke` of the glue
    on the place, with the same successors. -/
theorem resolveDrop_dropInvoke (ctx : EvalContext) (ty : Ty) (p : ValueId) (g : FuncId)
    (nd : BlockId) (na : List ValueId) (ud : BlockId)
    (h : ctx.dropGlue ty = some g) :
    ctx.resolveDrop (.DropInvoke ty p nd na ud) = .Invoke g [p] nd na ud := by
  simp [EvalContext.resolveDrop, h]

/-- Without a row, a drop (and its twin) is left unresolved. -/
theorem resolveDrop_unresolved (ctx : EvalContext) (ty : Ty) (p : ValueId)
    (nd : BlockId) (na : List ValueId) (ud : BlockId)
    (h : ctx.dropGlue ty = none) :
    ctx.resolveDrop (.Drop ty p) = .Drop ty p
      ∧ ctx.resolveDrop (.DropInvoke ty p nd na ud) = .DropInvoke ty p nd na ud := by
  simp [EvalContext.resolveDrop, h]

/-- Resolution is idempotent: a call it produced is not a drop. -/
theorem resolveDrop_idem (ctx : EvalContext) (i : Inst) :
    ctx.resolveDrop (ctx.resolveDrop i) = ctx.resolveDrop i := by
  cases i with
  | Drop ty p => cases h : ctx.dropGlue ty <;> simp [EvalContext.resolveDrop, h]
  | DropInvoke ty p nd na ud => cases h : ctx.dropGlue ty <;> simp [EvalContext.resolveDrop, h]
  | _ => rfl

theorem resolveBlock_idem (ctx : EvalContext) (b : BasicBlock) :
    ctx.resolveBlock (ctx.resolveBlock b) = ctx.resolveBlock b := by
  cases b
  simp only [EvalContext.resolveBlock, List.map_map, Function.comp_def, resolveDrop_idem]

theorem resolveCfg_apply (ctx : EvalContext) (cfg : CFG) (pc : BlockId) :
    ctx.resolveCfg cfg pc = (cfg pc).map ctx.resolveBlock := rfl

/-- Resolution leaves a landing pad alone and makes none: a resolved drop is
    a call or an invoke. -/
theorem padClauses_resolveDrop (ctx : EvalContext) (i : Inst) :
    (ctx.resolveDrop i).padClauses = i.padClauses := by
  cases i with
  | Drop ty p =>
    cases h : ctx.dropGlue ty <;> simp [EvalContext.resolveDrop, Inst.padClauses, h]
  | DropInvoke ty p nd na ud =>
    cases h : ctx.dropGlue ty <;> simp [EvalContext.resolveDrop, Inst.padClauses, h]
  | _ => rfl

/-- Entering a landing pad (amendment D, Part 2, R4) reads only the pad
    heading the block, so it is blind to drop resolution. -/
theorem semEnterPad_resolveCfg (ctx : EvalContext) (cfg : CFG) (exn : Addr) (dest : BlockId) :
    semEnterPad (ctx.resolveCfg cfg) exn dest = semEnterPad cfg exn dest := by
  unfold semEnterPad
  rw [resolveCfg_apply]
  cases cfg dest with
  | none => rfl
  | some blk =>
    have h : ((ctx.resolveBlock blk).body.head?).bind Inst.padClauses
        = (blk.body.head?).bind Inst.padClauses := by
      cases hb : blk.body with
      | nil => simp [EvalContext.resolveBlock, hb]
      | cons i rest => simp [EvalContext.resolveBlock, hb, padClauses_resolveDrop]
    simp only [Option.map, h]

/-- The `.unwind` terminator step is blind to drop resolution of the CFG it
    enters pads of. -/
theorem stepTermUnwind_resolveCfg (ctx : EvalContext) (cfg : CFG) (t : Inst)
    (model : ByteModel := .le64) :
    stepTermUnwind (ctx.resolveCfg cfg) t model = stepTermUnwind cfg t model := by
  simp only [stepTermUnwind, semEnterPad_resolveCfg]

/-- The contextual closure wrapper preserves that same CFG independence:
    only its unchanged fallback can enter a landing pad. -/
theorem stepTermWithContext_resolveCfg (ctx : EvalContext) (depth : Nat) (cfg : CFG)
    (term : Inst) (strat : PanicStrategy) :
    stepTermWithContext ctx depth (ctx.resolveCfg cfg) term strat =
      stepTermWithContext ctx depth cfg term strat := by
  cases strat with
  | abort => rfl
  | unwind => simp only [stepTermWithContext, stepTermUnwind_resolveCfg]

set_option maxHeartbeats 6400000 in
/-- **The resolution rewrite is an identity of the evaluator.** Running a CFG
    whose drops were rewritten to calls of their glue (`Drop` → `Call`,
    `DropInvoke` → `Invoke`; `EvalContext.resolveCfg`) is running the
    original CFG: same values, same final state, same error, for every fuel,
    call depth, block and arguments, under either panic strategy (amendment
    D, Part 2: the landing pads an unwinding enters are blind to resolution,
    `semEnterPad_resolveCfg`). -/
theorem stepNWithContext_resolveDrops (ctx : EvalContext) (cfg : CFG)
    (strat : PanicStrategy := .abort) :
    ∀ (fuel depth : Nat) (pc : BlockId) (args : List Value),
      stepNWithContext ctx fuel depth (ctx.resolveCfg cfg) pc args strat
        = stepNWithContext ctx fuel depth cfg pc args strat := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _; simp only [stepNWithContext]
  | succ n ih =>
    intro depth pc args
    simp only [stepNWithContext, resolveCfg_apply, ih, semEnterPad_resolveCfg,
      stepTermWithContext_resolveCfg, stepTermUnwind_resolveCfg]
    cases cfg pc with
    | none => rfl
    | some blk => simp only [Option.map, resolveBlock_idem]

/-- An unresolved drop is the structured `unsupported.destructor` of the bare
    step, from any state: never a no-op. -/
theorem drop_unresolved_is_unsupported (ty : Ty) (p : ValueId) (s : MachineState) :
    Sem.run (stepInst (.Drop ty p)) s
      = .error (.unsupported .destructor
          "Drop: the executable model does not model destructors") := rfl

/-- Its unwinding twin, the same. -/
theorem dropInvoke_unresolved_is_unsupported (ty : Ty) (p : ValueId) (nd : BlockId)
    (na : List ValueId) (ud : BlockId) (s : MachineState) :
    Sem.run (stepInst (.DropInvoke ty p nd na ud)) s
      = .error (.unsupported .destructor
          "DropInvoke: the executable model does not model destructors") := rfl

end TrustIr

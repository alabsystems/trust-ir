-- Copyright 2026 Andrew Yates
-- Author: Andrew Yates <andrewyates.name@gmail.com>
-- Licensed under the Apache License, Version 2.0
--
-- Amendment S (`docs/SPEC_RATIFICATIONS.md` §22): what instantiation's FORMAT
-- side is, proved over the model in `TrustIr/Template.lean`.
--
--   * `substTy_embed` / `substTys_embeds`: substitution is the identity on
--     ground (level-R) types, whatever the parameter and hole images;
--   * `substTy_total` / `substTys_total`: a template type whose every
--     parameter and hole has an image substitutes to SOME level-R type (T1's
--     guarantee that substitution cannot fail on a valid template);
--   * `substConst_embed`, `substConst_total`: the same for root constants;
--   * the drop rewrite's contract on a block: no erased drop survives
--     (`eraseDrops_removes_erased`; an erased `DropInvoke` terminator is its
--     normal edge, `eraseDrops_terminator`), every other body instruction is
--     kept (`eraseDrops_keeps_others`), it is idempotent
--     (`eraseDrops_body_idem`, `eraseTerminator_idem`), and it commutes with
--     drop resolution when no erased type has a glue row
--     (`resolveBlock_eraseDrops_body`, `resolveDrop_eraseTerminator`, and
--     for the whole block and CFG `resolveBlock_eraseDropsBlock`,
--     `resolveCfg_eraseDrops`): it removes only drops resolution would leave
--     unresolved.
--
-- NOT claimed: that an instance means what the source means (the host's
-- claim), nor that an erased drop is a no-op (rustc's meaning of a type
-- without drop glue, a host fact; see the amendment's review, "Lean").

import TrustIr.Template
import TrustIr.Proofs.DropProps

namespace TrustIr

mutual
theorem substTy_embed (σ η : Nat → Option Ty) : ∀ t : Ty, substTy σ η (embed t) = some t
  | .I8 => by simp [embed, substTy]
  | .I16 => by simp [embed, substTy]
  | .I32 => by simp [embed, substTy]
  | .I64 => by simp [embed, substTy]
  | .I128 => by simp [embed, substTy]
  | .U8 => by simp [embed, substTy]
  | .U16 => by simp [embed, substTy]
  | .U32 => by simp [embed, substTy]
  | .U64 => by simp [embed, substTy]
  | .U128 => by simp [embed, substTy]
  | .Isize => by simp [embed, substTy]
  | .Usize => by simp [embed, substTy]
  | .Char => by simp [embed, substTy]
  | .Error => by simp [embed, substTy]
  | .F16 => by simp [embed, substTy]
  | .F32 => by simp [embed, substTy]
  | .F64 => by simp [embed, substTy]
  | .Bool => by simp [embed, substTy]
  | .Ptr => by simp [embed, substTy]
  | .FatPtr a0 => by simp [embed, substTy]
  | .Struct a0 => by simp [embed, substTy]
  | .Array a0 a1 => by simp [embed, substTy]
  | .Func a0 => by simp [embed, substTy]
  | .Unit => by simp [embed, substTy]
  | .Never => by simp [embed, substTy]
  | .Tuple a0 => by simp [embed, substTy, substTys_embeds σ η a0]
  | .Enum a0 => by simp [embed, substTy]
  | .Vector a0 a1 => by simp [embed, substTy, substTy_embed σ η a1]
  | .Ref a0 => by simp [embed, substTy, substTy_embed σ η a0]
  | .RefMut a0 => by simp [embed, substTy, substTy_embed σ η a0]
  | .PtrConst a0 => by simp [embed, substTy, substTy_embed σ η a0]
  | .PtrMut a0 => by simp [embed, substTy, substTy_embed σ η a0]
  | .Rc a0 => by simp [embed, substTy, substTy_embed σ η a0]
  | .Set a0 a1 => by simp [embed, substTy]
  | .Sequence a0 => by simp [embed, substTy]
  | .Record a0 => by simp [embed, substTy]
  | .Closure a0 => by simp [embed, substTy]
  | .Refine a0 a1 => by simp [embed, substTy]
  | .Dialect a0 a1 a2 => by simp [embed, substTy]
  | .Storage a0 a1 => by simp [embed, substTy]
  | .Handle a0 a1 => by simp [embed, substTy]
theorem substTys_embeds (σ η : Nat → Option Ty) : ∀ ts : List Ty, substTys σ η (embeds ts) = some ts
  | [] => by simp [embeds, substTys]
  | t :: ts => by simp [embeds, substTys, substTy_embed σ η t, substTys_embeds σ η ts]
end

mutual
theorem substTy_total (σ η : Nat → Option Ty) :
    ∀ t : TemplateTy, refsOk σ η t = true → (substTy σ η t).isSome = true
  | .I8, _ => by simp [substTy]
  | .I16, _ => by simp [substTy]
  | .I32, _ => by simp [substTy]
  | .I64, _ => by simp [substTy]
  | .I128, _ => by simp [substTy]
  | .U8, _ => by simp [substTy]
  | .U16, _ => by simp [substTy]
  | .U32, _ => by simp [substTy]
  | .U64, _ => by simp [substTy]
  | .U128, _ => by simp [substTy]
  | .Isize, _ => by simp [substTy]
  | .Usize, _ => by simp [substTy]
  | .Char, _ => by simp [substTy]
  | .Error, _ => by simp [substTy]
  | .F16, _ => by simp [substTy]
  | .F32, _ => by simp [substTy]
  | .F64, _ => by simp [substTy]
  | .Bool, _ => by simp [substTy]
  | .Ptr, _ => by simp [substTy]
  | .FatPtr _, _ => by simp [substTy]
  | .Struct _, _ => by simp [substTy]
  | .Array _ _, _ => by simp [substTy]
  | .Func _, _ => by simp [substTy]
  | .Unit, _ => by simp [substTy]
  | .Never, _ => by simp [substTy]
  | .Tuple a0, h => by
      simp only [refsOk] at h
      obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp (substTys_total σ η a0 h)
      simp [substTy, hu]
  | .Enum _, _ => by simp [substTy]
  | .Vector _ a1, h => by
      simp only [refsOk] at h
      obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp (substTy_total σ η a1 h)
      simp [substTy, hu]
  | .Ref a0, h => by
      simp only [refsOk] at h
      obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp (substTy_total σ η a0 h)
      simp [substTy, hu]
  | .RefMut a0, h => by
      simp only [refsOk] at h
      obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp (substTy_total σ η a0 h)
      simp [substTy, hu]
  | .PtrConst a0, h => by
      simp only [refsOk] at h
      obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp (substTy_total σ η a0 h)
      simp [substTy, hu]
  | .PtrMut a0, h => by
      simp only [refsOk] at h
      obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp (substTy_total σ η a0 h)
      simp [substTy, hu]
  | .Rc a0, h => by
      simp only [refsOk] at h
      obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp (substTy_total σ η a0 h)
      simp [substTy, hu]
  | .Set _ _, _ => by simp [substTy]
  | .Sequence _, _ => by simp [substTy]
  | .Record _, _ => by simp [substTy]
  | .Closure _, _ => by simp [substTy]
  | .Refine _ _, _ => by simp [substTy]
  | .Dialect _ _ _, _ => by simp [substTy]
  | .Storage _ _, _ => by simp [substTy]
  | .Handle _ _, _ => by simp [substTy]
  | .param _, h => by simpa [substTy, refsOk] using h
  | .hole _, h => by simpa [substTy, refsOk] using h
theorem substTys_total (σ η : Nat → Option Ty) :
    ∀ ts : List TemplateTy, refsOks σ η ts = true → (substTys σ η ts).isSome = true
  | [], _ => by simp [substTys]
  | t :: ts, h => by
      simp only [refsOks, Bool.and_eq_true] at h
      obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp (substTy_total σ η t h.1)
      obtain ⟨us, hus⟩ := Option.isSome_iff_exists.mp (substTys_total σ η ts h.2)
      simp [substTys, hu, hus]
end

/-- Substitution is the identity on ground constants. -/
theorem substConst_embed (σ η : Nat → Option Constant) (c : Constant) :
    substConst σ η (embedConst c) = some c := rfl

/-- A template constant whose name has an image substitutes. -/
theorem substConst_total (σ η : Nat → Option Constant) (c : TemplateConst)
    (h : match c with
      | .ground _ => True
      | .param i => (σ i).isSome = true
      | .hole k => (η k).isSome = true) :
    (substConst σ η c).isSome = true := by
  cases c with
  | ground _ => rfl
  | param i => simpa [substConst] using h
  | hole k => simpa [substConst] using h

-- ---------------------------------------------------------------------------
-- The drop rewrite
-- ---------------------------------------------------------------------------

/-- No erased drop survives in the body. -/
theorem eraseDrops_removes_erased (erase : Ty → Bool) (b : BasicBlock) :
    ∀ i ∈ (eraseDropsBlock erase b).body, isErasedDrop erase i = false := by
  intro i hi
  simp only [eraseDropsBlock, List.mem_filter] at hi
  simpa using hi.2

/-- Nor as the terminator: an erased `DropInvoke` is its normal edge. -/
theorem eraseDrops_terminator (erase : Ty → Bool) (ty : Ty) (p : ValueId) (nd : BlockId)
    (na : List ValueId) (ud : BlockId) (h : erase ty = true) :
    eraseTerminator erase (.DropInvoke ty p nd na ud) = .Br nd na := by
  simp [eraseTerminator, h]

/-- Every other body instruction is kept. -/
theorem eraseDrops_keeps_others (erase : Ty → Bool) (b : BasicBlock) (i : Inst)
    (hi : i ∈ b.body) (h : isErasedDrop erase i = false) :
    i ∈ (eraseDropsBlock erase b).body := by
  simp only [eraseDropsBlock, List.mem_filter]
  exact ⟨hi, by simp [h]⟩

/-- A non-drop terminator is unchanged. -/
theorem eraseTerminator_idem (erase : Ty → Bool) (t : Inst) :
    eraseTerminator erase (eraseTerminator erase t) = eraseTerminator erase t := by
  cases t with
  | DropInvoke ty p nd na ud =>
    cases h : erase ty <;> simp [eraseTerminator, h]
  | _ => rfl

/-- Filtering twice by one predicate is filtering once. -/
theorem filter_filter_idem {α : Type} (p : α → Bool) :
    ∀ l : List α, (l.filter p).filter p = l.filter p
  | [] => rfl
  | a :: l => by
    by_cases h : p a = true
    · simp [List.filter, h, filter_filter_idem p l]
    · have h' : p a = false := by simpa using h
      simp [List.filter, h', filter_filter_idem p l]

/-- The rewrite is idempotent on a body. -/
theorem eraseDrops_body_idem (erase : Ty → Bool) (b : BasicBlock) :
    (eraseDropsBlock erase (eraseDropsBlock erase b)).body = (eraseDropsBlock erase b).body := by
  simp only [eraseDropsBlock]
  exact filter_filter_idem _ b.body

/-- Resolution leaves an erased drop's "erased" status unchanged when no
    erased type has a glue row. -/
theorem isErasedDrop_resolveDrop (ctx : EvalContext) (erase : Ty → Bool)
    (hglue : ∀ ty, erase ty = true → ctx.dropGlue ty = none) (i : Inst) :
    isErasedDrop erase (ctx.resolveDrop i) = isErasedDrop erase i := by
  cases i with
  | Drop ty p =>
    cases hg : ctx.dropGlue ty with
    | none => simp [EvalContext.resolveDrop, hg]
    | some g =>
      have : erase ty = false := by
        cases he : erase ty with
        | false => rfl
        | true => simp [hglue ty he] at hg
      simp [EvalContext.resolveDrop, hg, isErasedDrop, this]
  | DropInvoke ty p nd na ud =>
    cases hg : ctx.dropGlue ty <;> simp [EvalContext.resolveDrop, hg, isErasedDrop]
  | _ => rfl

theorem filter_map_comm {α : Type} (f : α → α) (p : α → Bool) (hp : ∀ a, p (f a) = p a) :
    ∀ l : List α, (l.map f).filter p = (l.filter p).map f
  | [] => rfl
  | a :: l => by
    by_cases h : p a = true
    · simp [List.filter, hp a, h, filter_map_comm f p hp l]
    · have h' : p a = false := by simpa using h
      simp [List.filter, hp a, h', filter_map_comm f p hp l]

/-- The rewrite commutes with drop resolution on a body, when no erased type
    has a glue row: it removes only drops resolution would leave unresolved. -/
theorem resolveBlock_eraseDrops_body (ctx : EvalContext) (erase : Ty → Bool)
    (hglue : ∀ ty, erase ty = true → ctx.dropGlue ty = none) (b : BasicBlock) :
    (ctx.resolveBlock (eraseDropsBlock erase b)).body
      = (eraseDropsBlock erase (ctx.resolveBlock b)).body := by
  simp only [EvalContext.resolveBlock, eraseDropsBlock]
  exact (filter_map_comm ctx.resolveDrop (fun i => !isErasedDrop erase i)
    (fun i => by simp [isErasedDrop_resolveDrop ctx erase hglue i]) b.body).symm

/-- And on a terminator. -/
theorem resolveDrop_eraseTerminator (ctx : EvalContext) (erase : Ty → Bool)
    (hglue : ∀ ty, erase ty = true → ctx.dropGlue ty = none) (t : Inst) :
    ctx.resolveDrop (eraseTerminator erase t) = eraseTerminator erase (ctx.resolveDrop t) := by
  cases t with
  | DropInvoke ty p nd na ud =>
    cases he : erase ty with
    | true => simp [eraseTerminator, he, EvalContext.resolveDrop, hglue ty he]
    | false =>
      cases hg : ctx.dropGlue ty <;> simp [eraseTerminator, he, EvalContext.resolveDrop, hg]
  | Drop ty p =>
    cases hg : ctx.dropGlue ty <;> simp [eraseTerminator, EvalContext.resolveDrop, hg]
  | _ => rfl

/-- Filtering zipped pairs by a predicate on the first lane is blind to a map
    of that lane the predicate does not see. -/
theorem zip_map_filter_snd {α β : Type} (f : α → α) (p : α → Bool) (hp : ∀ a, p (f a) = p a) :
    ∀ (l : List α) (d : List β),
      (((l.map f).zip d).filter (fun q => p q.1)).map Prod.snd
        = ((l.zip d).filter (fun q => p q.1)).map Prod.snd
  | [], _ => rfl
  | _ :: _, [] => rfl
  | a :: l, x :: d => by
    have ih := zip_map_filter_snd f p hp l d
    simp only [List.zip] at ih
    by_cases h : p a = true
    · simp [List.zip, List.filter, hp a, h, ih]
    · have h' : p a = false := by simpa using h
      simp [List.zip, List.filter, hp a, h', ih]

/-- The whole block: the rewrite commutes with drop resolution (body, result
    destinations and terminator), when no erased type has a glue row. -/
theorem resolveBlock_eraseDropsBlock (ctx : EvalContext) (erase : Ty → Bool)
    (hglue : ∀ ty, erase ty = true → ctx.dropGlue ty = none) (b : BasicBlock) :
    ctx.resolveBlock (eraseDropsBlock erase b) = eraseDropsBlock erase (ctx.resolveBlock b) := by
  have hp : ∀ i, (!isErasedDrop erase (ctx.resolveDrop i)) = (!isErasedDrop erase i) := by
    intro i
    simp [isErasedDrop_resolveDrop ctx erase hglue i]
  have hbody := resolveBlock_eraseDrops_body ctx erase hglue b
  have hterm := resolveDrop_eraseTerminator ctx erase hglue b.terminator
  have hdests := zip_map_filter_snd ctx.resolveDrop (fun i => !isErasedDrop erase i) hp
    b.body b.bodyResultDests
  cases b with
  | mk params body dests term tdests =>
    simp only [EvalContext.resolveBlock, eraseDropsBlock] at hbody hterm hdests ⊢
    simp only [List.length_map, hbody, hterm, hdests]

/-- On a CFG (amendment S's `eraseDropsCfg`): erasing and resolving commute,
    when no erased type has a glue row. -/
theorem resolveCfg_eraseDrops (ctx : EvalContext) (erase : Ty → Bool)
    (hglue : ∀ ty, erase ty = true → ctx.dropGlue ty = none) (cfg : CFG) :
    ctx.resolveCfg (eraseDropsCfg erase cfg) = eraseDropsCfg erase (ctx.resolveCfg cfg) := by
  funext pc
  simp only [EvalContext.resolveCfg, eraseDropsCfg]
  cases cfg pc with
  | none => rfl
  | some b => simp [resolveBlock_eraseDropsBlock ctx erase hglue b]

end TrustIr

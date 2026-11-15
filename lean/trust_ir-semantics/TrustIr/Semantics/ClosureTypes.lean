-- Copyright 2026 Andrew Yates | Author: Andrew Yates | Apache-2.0
import TrustIr.Basic
import TrustIr.CompilerCompat

namespace TrustIr

/- The legacy derived recursive BEq for Ty is opaque to the Lean 4.8 kernel.
   Closure call contracts need executable, kernel-reducible structural equality.
   This comparator preserves every constructor and nominal ID; it performs no
   alias expansion, width coercion or layout equivalence. -/
trustIrDenseMatch
mutual
  def closureTyEq (lhs rhs : Ty) : Bool :=
    match lhs with
    | .I8 => match rhs with | .I8 => true | _ => false
    | .I16 => match rhs with | .I16 => true | _ => false
    | .I32 => match rhs with | .I32 => true | _ => false
    | .I64 => match rhs with | .I64 => true | _ => false
    | .I128 => match rhs with | .I128 => true | _ => false
    | .U8 => match rhs with | .U8 => true | _ => false
    | .U16 => match rhs with | .U16 => true | _ => false
    | .U32 => match rhs with | .U32 => true | _ => false
    | .U64 => match rhs with | .U64 => true | _ => false
    | .U128 => match rhs with | .U128 => true | _ => false
    | .Isize => match rhs with | .Isize => true | _ => false
    | .Usize => match rhs with | .Usize => true | _ => false
    | .Char => match rhs with | .Char => true | _ => false
    | .Error => match rhs with | .Error => true | _ => false
    | .F16 => match rhs with | .F16 => true | _ => false
    | .F32 => match rhs with | .F32 => true | _ => false
    | .F64 => match rhs with | .F64 => true | _ => false
    | .Bool => match rhs with | .Bool => true | _ => false
    | .Ptr => match rhs with | .Ptr => true | _ => false
    | .Unit => match rhs with | .Unit => true | _ => false
    | .Never => match rhs with | .Never => true | _ => false
    | .FatPtr a => match rhs with | .FatPtr b => decide (a = b) | _ => false
    | .Struct a => match rhs with | .Struct b => a.index == b.index | _ => false
    | .Array a n => match rhs with | .Array b m => a.index == b.index && n == m | _ => false
    | .Func a => match rhs with | .Func b => a.index == b.index | _ => false
    | .Tuple a => match rhs with | .Tuple b => closureTyListEq a b | _ => false
    | .Enum a => match rhs with | .Enum b => a.index == b.index | _ => false
    | .Vector n a => match rhs with | .Vector m b => n == m && closureTyEq a b | _ => false
    | .Ref a => match rhs with | .Ref b => closureTyEq a b | _ => false
    | .RefMut a => match rhs with | .RefMut b => closureTyEq a b | _ => false
    | .PtrConst a => match rhs with | .PtrConst b => closureTyEq a b | _ => false
    | .PtrMut a => match rhs with | .PtrMut b => closureTyEq a b | _ => false
    | .Rc a => match rhs with | .Rc b => closureTyEq a b | _ => false
    | .Set a r => match rhs with | .Set b s => a.index == b.index && decide (r = s) | _ => false
    | .Sequence a => match rhs with | .Sequence b => a.index == b.index | _ => false
    | .Record a => match rhs with | .Record b => a.index == b.index | _ => false
    | .Closure a => match rhs with | .Closure b => a.index == b.index | _ => false
    | .Refine a p => match rhs with | .Refine b q => a.index == b.index && p.index == q.index | _ => false
    | .Dialect a n v => match rhs with | .Dialect b m w => a == b && n == m && v == w | _ => false
    | .Storage a n => match rhs with | .Storage b m => a == b && n == m | _ => false
    | .Handle a n => match rhs with | .Handle b m => a == b && n == m | _ => false
  def closureTyListEq : List Ty → List Ty → Bool
    | [], [] => true
    | a :: as, b :: bs => closureTyEq a b && closureTyListEq as bs
    | _, _ => false
end

set_option maxHeartbeats 4000000 in
mutual
  theorem closureTyEq_refl : (ty : Ty) → closureTyEq ty ty = true
    | .Tuple ts => by
      rw [closureTyEq]
      exact closureTyListEq_refl ts
    | .Vector _ t => by
      rw [closureTyEq, closureTyEq_refl t]
      simp
    | .Ref t => by
      rw [closureTyEq]
      exact closureTyEq_refl t
    | .RefMut t => by
      rw [closureTyEq]
      exact closureTyEq_refl t
    | .PtrConst t => by
      rw [closureTyEq]
      exact closureTyEq_refl t
    | .PtrMut t => by
      rw [closureTyEq]
      exact closureTyEq_refl t
    | .Rc t => by
      rw [closureTyEq]
      exact closureTyEq_refl t
    | .I8 | .I16 | .I32 | .I64 | .I128 | .U8 | .U16 | .U32 | .U64 | .U128
    | .Isize | .Usize | .Char | .Error | .F16 | .F32 | .F64 | .Bool | .Ptr
    | .Unit | .Never => rfl
    | .FatPtr _ | .Struct _ | .Array _ _ | .Func _ | .Enum _ | .Set _ _
    | .Sequence _ | .Record _ | .Closure _ | .Refine _ _ | .Dialect _ _ _ | .Storage _ _ | .Handle _ _ =>
      by rw [closureTyEq]; simp
  theorem closureTyListEq_refl : (tys : List Ty) → closureTyListEq tys tys = true
    | [] => rfl
    | t :: ts => by
      rw [closureTyListEq, closureTyEq_refl t, closureTyListEq_refl ts]
      rfl
end

/-- Nominal closure types never collapse merely because their captures match. -/
theorem closureTyEq_closure_iff (a b : ClosureTyId) :
    closureTyEq (.Closure a) (.Closure b) = true ↔ a = b := by
  cases a; cases b
  rw [closureTyEq]
  simp

set_option maxHeartbeats 4000000 in
mutual
  theorem closureTyEq_sound : (a b : Ty) → closureTyEq a b = true → a = b := by
    intro a b h
    cases a <;> cases b <;> simp only [closureTyEq] at h <;> try contradiction
    all_goals first | rfl | skip
    case FatPtr.FatPtr a b =>
      have hh : a = b := by simpa using h
      cases hh
      rfl
    case Struct.Struct a b => cases a; cases b; simp_all
    case Array.Array a n b m => cases a; cases b; simp_all
    case Func.Func a b => cases a; cases b; simp_all
    case Tuple.Tuple a b => exact congrArg Ty.Tuple (closureTyListEq_sound a b h)
    case Enum.Enum a b => cases a; cases b; simp_all
    case Vector.Vector n a m b =>
      have hh : n = m ∧ closureTyEq a b = true := by simpa using h
      cases hh.1
      exact congrArg (Ty.Vector n) (closureTyEq_sound a b hh.2)
    case Ref.Ref a b => exact congrArg Ty.Ref (closureTyEq_sound a b h)
    case RefMut.RefMut a b => exact congrArg Ty.RefMut (closureTyEq_sound a b h)
    case PtrConst.PtrConst a b => exact congrArg Ty.PtrConst (closureTyEq_sound a b h)
    case PtrMut.PtrMut a b => exact congrArg Ty.PtrMut (closureTyEq_sound a b h)
    case Rc.Rc a b => exact congrArg Ty.Rc (closureTyEq_sound a b h)
    case Set.Set a n b m => cases a; cases b; simp_all
    case Sequence.Sequence a b => cases a; cases b; simp_all
    case Record.Record a b => cases a; cases b; simp_all
    case Closure.Closure a b => cases a; cases b; simp_all
    case Refine.Refine a p b q => cases a; cases b; cases p; cases q; simp_all
    case Dialect.Dialect a n v b m w => simp_all
    case Storage.Storage a n b m => simp_all
    case Handle.Handle a n b m => simp_all
  theorem closureTyListEq_sound : (a b : List Ty) → closureTyListEq a b = true → a = b := by
    intro a b h
    cases a with
    | nil => cases b <;> simp_all [closureTyListEq]
    | cons x xs =>
      cases b with
      | nil => simp [closureTyListEq] at h
      | cons y ys =>
        rw [closureTyListEq] at h
        have hh : closureTyEq x y = true ∧ closureTyListEq xs ys = true := by simpa using h
        rw [closureTyEq_sound x y hh.1, closureTyListEq_sound xs ys hh.2]
end

/-- The executable comparison accepts exactly structural type equality. -/
theorem closureTyEq_iff (a b : Ty) : closureTyEq a b = true ↔ a = b := by
  constructor
  · exact closureTyEq_sound a b
  · intro h
    cases h
    exact closureTyEq_refl a

/-- Physical parameter lists have the same exact equality contract. -/
theorem closureTyListEq_iff (a b : List Ty) : closureTyListEq a b = true ↔ a = b := by
  constructor
  · exact closureTyListEq_sound a b
  · intro h
    cases h
    exact closureTyListEq_refl a

end TrustIr

#trustIrAxiomsPinned TrustIr.closureTyEq == [propext, Classical.choice, Quot.sound] modern []
#trustIrAxiomsPinned TrustIr.closureTyListEq == [propext, Classical.choice, Quot.sound] modern []

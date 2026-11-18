-- Copyright 2026 Andrew Yates
-- Author: Andrew Yates <andrewyates.name@gmail.com>
-- Licensed under the Apache License, Version 2.0
--
-- Amendment S (`docs/SPEC_RATIFICATIONS.md` §22): level-S syntax, its
-- substitution, and the drop rewrite on a CFG.
--
-- A template's type is a `Ty` that may also name a type PARAMETER or a type
-- HOLE (the host answers holes at instantiation). `TemplateTy` mirrors every
-- `Ty` constructor with `TemplateTy` children, plus `param` and `hole`
-- (`crates/trust-ir/tests/lean_schema_parity.rs` holds the mirror to Rust's
-- `TyG`). A template constant is a level-R `Constant` or, at its root only, a
-- parameter or a hole (Rust's `ConstantG` children are level R).
--
-- What is modelled here is instantiation's FORMAT side: substitution
-- (`substTy`, `substConst`) and the drop rewrite (`eraseDropsBlock`). That an
-- instance means what the source means is the host's claim (Trust's
-- TEMPLATE-HOST row), and nothing here models it.

import TrustIr.Basic
import TrustIr.Constant
import TrustIr.ModuleSyntax

namespace TrustIr

/-- A level-S type: every `Ty` constructor over `TemplateTy`, plus a type
    parameter and a type hole (Rust `TyG<TemplateRef>`). -/
inductive TemplateTy where
  | I8 : TemplateTy
  | I16 : TemplateTy
  | I32 : TemplateTy
  | I64 : TemplateTy
  | I128 : TemplateTy
  | U8 : TemplateTy
  | U16 : TemplateTy
  | U32 : TemplateTy
  | U64 : TemplateTy
  | U128 : TemplateTy
  | Isize : TemplateTy
  | Usize : TemplateTy
  | Char : TemplateTy
  | Error : TemplateTy
  | F16 : TemplateTy
  | F32 : TemplateTy
  | F64 : TemplateTy
  | Bool : TemplateTy
  | Ptr : TemplateTy
  | FatPtr : FatPtrKind -> TemplateTy
  | Struct : StructId -> TemplateTy
  | Array : TyId -> Nat -> TemplateTy
  | Func : FuncTyId -> TemplateTy
  | Unit : TemplateTy
  | Never : TemplateTy
  | Tuple : List TemplateTy -> TemplateTy
  | Enum : EnumId -> TemplateTy
  | Vector : Nat -> TemplateTy -> TemplateTy
  | Ref : TemplateTy -> TemplateTy
  | RefMut : TemplateTy -> TemplateTy
  | PtrConst : TemplateTy -> TemplateTy
  | PtrMut : TemplateTy -> TemplateTy
  | Rc : TemplateTy -> TemplateTy
  | Set : TyId -> SetRepr -> TemplateTy
  | Sequence : TyId -> TemplateTy
  | Record : RecordId -> TemplateTy
  | Closure : ClosureTyId -> TemplateTy
  | Refine : TyId -> PredId -> TemplateTy
  | Dialect : String -> String -> UInt32 -> TemplateTy
  | Storage : Nat -> Nat -> TemplateTy
  | Handle : String -> String -> TemplateTy
  /-- Type parameter `$i`. -/
  | param : Nat -> TemplateTy
  /-- Type hole `?h`, answered by the host. -/
  | hole : Nat -> TemplateTy
  /-- Exact nominal zero-byte function item, not a reified pointer. -/
  | FnItem : FuncId -> TemplateTy
  deriving Repr

mutual
/-- Substitute parameters (`σ`) and hole answers (`η`) to a level-R type;
    `none` when a name has no image. -/
def substTy (σ η : Nat → Option Ty) : TemplateTy → Option Ty
  | .I8 => some (.I8)
  | .I16 => some (.I16)
  | .I32 => some (.I32)
  | .I64 => some (.I64)
  | .I128 => some (.I128)
  | .U8 => some (.U8)
  | .U16 => some (.U16)
  | .U32 => some (.U32)
  | .U64 => some (.U64)
  | .U128 => some (.U128)
  | .Isize => some (.Isize)
  | .Usize => some (.Usize)
  | .Char => some (.Char)
  | .Error => some (.Error)
  | .F16 => some (.F16)
  | .F32 => some (.F32)
  | .F64 => some (.F64)
  | .Bool => some (.Bool)
  | .Ptr => some (.Ptr)
  | .FatPtr a0 => some (.FatPtr a0)
  | .Struct a0 => some (.Struct a0)
  | .Array a0 a1 => some (.Array a0 a1)
  | .Func a0 => some (.Func a0)
  | .Unit => some (.Unit)
  | .Never => some (.Never)
  | .Tuple a0 => (substTys σ η a0).bind fun a0' => some (.Tuple a0')
  | .Enum a0 => some (.Enum a0)
  | .Vector a0 a1 => (substTy σ η a1).bind fun a1' => some (.Vector a0 a1')
  | .Ref a0 => (substTy σ η a0).bind fun a0' => some (.Ref a0')
  | .RefMut a0 => (substTy σ η a0).bind fun a0' => some (.RefMut a0')
  | .PtrConst a0 => (substTy σ η a0).bind fun a0' => some (.PtrConst a0')
  | .PtrMut a0 => (substTy σ η a0).bind fun a0' => some (.PtrMut a0')
  | .Rc a0 => (substTy σ η a0).bind fun a0' => some (.Rc a0')
  | .Set a0 a1 => some (.Set a0 a1)
  | .Sequence a0 => some (.Sequence a0)
  | .Record a0 => some (.Record a0)
  | .Closure a0 => some (.Closure a0)
  | .Refine a0 a1 => some (.Refine a0 a1)
  | .Dialect a0 a1 a2 => some (.Dialect a0 a1 a2)
  | .Storage a0 a1 => some (.Storage a0 a1)
  | .Handle a0 a1 => some (.Handle a0 a1)
  | .FnItem id => some (.FnItem id)
  | .param i => σ i
  | .hole h => η h
/-- `substTy` over a list. -/
def substTys (σ η : Nat → Option Ty) : List TemplateTy → Option (List Ty)
  | [] => some []
  | t :: ts => (substTy σ η t).bind fun t' => (substTys σ η ts).bind fun ts' => some (t' :: ts')
end

mutual
/-- The level-R types inside level S (the ground inclusion). -/
def embed : Ty → TemplateTy
  | .I8 => .I8
  | .I16 => .I16
  | .I32 => .I32
  | .I64 => .I64
  | .I128 => .I128
  | .U8 => .U8
  | .U16 => .U16
  | .U32 => .U32
  | .U64 => .U64
  | .U128 => .U128
  | .Isize => .Isize
  | .Usize => .Usize
  | .Char => .Char
  | .Error => .Error
  | .F16 => .F16
  | .F32 => .F32
  | .F64 => .F64
  | .Bool => .Bool
  | .Ptr => .Ptr
  | .FatPtr a0 => .FatPtr a0
  | .Struct a0 => .Struct a0
  | .Array a0 a1 => .Array a0 a1
  | .Func a0 => .Func a0
  | .Unit => .Unit
  | .Never => .Never
  | .Tuple a0 => .Tuple (embeds a0)
  | .Enum a0 => .Enum a0
  | .Vector a0 a1 => .Vector a0 (embed a1)
  | .Ref a0 => .Ref (embed a0)
  | .RefMut a0 => .RefMut (embed a0)
  | .PtrConst a0 => .PtrConst (embed a0)
  | .PtrMut a0 => .PtrMut (embed a0)
  | .Rc a0 => .Rc (embed a0)
  | .Set a0 a1 => .Set a0 a1
  | .Sequence a0 => .Sequence a0
  | .Record a0 => .Record a0
  | .Closure a0 => .Closure a0
  | .Refine a0 a1 => .Refine a0 a1
  | .Dialect a0 a1 a2 => .Dialect a0 a1 a2
  | .Storage a0 a1 => .Storage a0 a1
  | .Handle a0 a1 => .Handle a0 a1
  | .FnItem id => .FnItem id
/-- `embed` over a list. -/
def embeds : List Ty → List TemplateTy
  | [] => []
  | t :: ts => embed t :: embeds ts
end

mutual
/-- Every parameter and hole `t` names has an image (T1's scope rule, at
    instantiation). -/
def refsOk (σ η : Nat → Option Ty) : TemplateTy → Bool
  | .I8 => true
  | .I16 => true
  | .I32 => true
  | .I64 => true
  | .I128 => true
  | .U8 => true
  | .U16 => true
  | .U32 => true
  | .U64 => true
  | .U128 => true
  | .Isize => true
  | .Usize => true
  | .Char => true
  | .Error => true
  | .F16 => true
  | .F32 => true
  | .F64 => true
  | .Bool => true
  | .Ptr => true
  | .FatPtr _ => true
  | .Struct _ => true
  | .Array _ _ => true
  | .Func _ => true
  | .Unit => true
  | .Never => true
  | .Tuple a0 => refsOks σ η a0
  | .Enum _ => true
  | .Vector _ a1 => refsOk σ η a1
  | .Ref a0 => refsOk σ η a0
  | .RefMut a0 => refsOk σ η a0
  | .PtrConst a0 => refsOk σ η a0
  | .PtrMut a0 => refsOk σ η a0
  | .Rc a0 => refsOk σ η a0
  | .Set _ _ => true
  | .Sequence _ => true
  | .Record _ => true
  | .Closure _ => true
  | .Refine _ _ => true
  | .Dialect _ _ _ => true
  | .Storage _ _ => true
  | .Handle _ _ => true
  | .FnItem _ => true
  | .param i => (σ i).isSome
  | .hole h => (η h).isSome
/-- `refsOk` over a list. -/
def refsOks (σ η : Nat → Option Ty) : List TemplateTy → Bool
  | [] => true
  | t :: ts => refsOk σ η t && refsOks σ η ts
end

/-- A level-S constant: a level-R constant, or (at the root only) a const
    parameter or const hole (Rust `ConstantG<TemplateRef>`). -/
inductive TemplateConst where
  | ground : Constant -> TemplateConst
  | param : Nat -> TemplateConst
  | hole : Nat -> TemplateConst

/-- Substitute a template constant. -/
def substConst (σ η : Nat → Option Constant) : TemplateConst → Option Constant
  | .ground c => some c
  | .param i => σ i
  | .hole h => η h

/-- The level-R constants inside level S. -/
def embedConst (c : Constant) : TemplateConst := .ground c

-- ---------------------------------------------------------------------------
-- The drop rewrite (amendment S, S7; reviews R1, R2)
-- ---------------------------------------------------------------------------

/-- Whether a body instruction is a `Drop` the rewrite erases (`erase ty`:
    its instantiated type is trivially droppable, or has no destructor). -/
def isErasedDrop (erase : Ty → Bool) : Inst → Bool
  | .Drop ty _ => erase ty
  | _ => false

/-- The rewrite of a terminator: an erased `DropInvoke` is `Br` to its normal
    destination with its normal-edge arguments. -/
def eraseTerminator (erase : Ty → Bool) : Inst → Inst
  | .DropInvoke ty p nd na ud => if erase ty then .Br nd na else .DropInvoke ty p nd na ud
  | t => t

/-- The drop rewrite on one block: erased drops deleted (with their result
    destinations, when the block carries them positionally), an erased
    `DropInvoke` terminator replaced by its normal edge. -/
def eraseDropsBlock (erase : Ty → Bool) (b : BasicBlock) : BasicBlock :=
  { b with
    body := b.body.filter (fun i => !isErasedDrop erase i)
    bodyResultDests :=
      if b.bodyResultDests.length == b.body.length then
        ((b.body.zip b.bodyResultDests).filter (fun p => !isErasedDrop erase p.1)).map Prod.snd
      else b.bodyResultDests
    terminator := eraseTerminator erase b.terminator }

/-- The drop rewrite on a CFG. -/
def eraseDropsCfg (erase : Ty → Bool) (cfg : CFG) : CFG :=
  fun pc => (cfg pc).map (eraseDropsBlock erase)

end TrustIr


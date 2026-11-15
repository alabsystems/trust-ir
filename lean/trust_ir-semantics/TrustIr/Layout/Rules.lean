-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Layout.Graph
import TrustIr.Semantics.TypedInteger

namespace TrustIr.SourceLayout

abbrev Result := Except Error

def checked (value : Nat) : Result Nat :=
  if value ≤ word64Max then .ok value else .error .sizeOverflow

theorem checked_ok (input output : Nat) (success : checked input = .ok output) :
    output = input ∧ input ≤ word64Max := by
  unfold checked at success
  split at success
  · cases success; exact ⟨rfl, by assumption⟩
  · cases success

def alignUp (offset align : Nat) : Result Nat :=
  if align = 0 then .error (.incoherent "alignment" 0)
  else checked (offset + (align - offset % align) % align)

def powerOfTwo (n : Nat) : Bool := n != 0 && n &&& (n - 1) == 0

def finish (mode : Mode) (value : Summary) : Result Summary := do
  let _ ← checked value.size
  if let some align := value.align then let _ ← checked align; pure ()
  if mode == .shape then
    let _ ← checked (8 * value.size)
    if let some align := value.align then let _ ← checked (8 * align); pure ()
  pure value

def overlap (leftOffset leftSize rightOffset rightSize : Nat) : Bool :=
  leftSize != 0 && rightSize != 0 &&
    (leftOffset < rightOffset + rightSize && rightOffset < leftOffset + leftSize)

def hasOverlap (fields : List Field) : Bool :=
  match fields with
  | [] => false
  | first :: rest => rest.any (fun other => overlap first.offset first.size other.offset other.size) || hasOverlap rest

private def fieldAlign (kind : String) (id clamp : Nat) (summary : Summary) : Result Nat := do
  let natural ← match summary.align with
    | some align => pure align
    | none => throw (.incoherent kind id)
  pure (min (max 1 natural) clamp)

def canonicalFields (mode : Mode) (kind : String) (id : Nat) (fields : List (Ty × Nat)) : Equation :=
  { kind := .placements
    initial := .ok {}
    steps := fields.map (fun (ty, child) => .child child fun summary state => do
      let align ← fieldAlign kind id word64Max summary
      let offset ← alignUp state.cursor align
      let cursor ← checked (offset + summary.size)
      pure { cursor, align := max state.align align, fields := { ty, offset, size := summary.size, align } :: state.fields })
    finish := fun state => do
      let size ← alignUp state.cursor state.align
      finish mode { size, align := some state.align, fields := state.fields.reverse } }

/-- Every producer position is retained. Only an omitted zero-sized struct
    field is information-free; tuples and closures supply all positions. -/
def declaredFields (mode : Mode) (kind : String) (id size align clamp : Nat)
    (transparent : Bool) (fields : List (Ty × Option Nat × Nat)) : Equation :=
  { kind := .placements
    initial := if !powerOfTwo align || size % align != 0 || align > clamp then
      .error (.incoherent kind id) else .ok {}
    steps := fields.map (fun (ty, declared, child) => .child child fun summary state => do
      let fieldAlign ← fieldAlign kind id clamp summary
      let offset ← match declared with
        | some offset => pure offset
        | none => if summary.size == 0 then pure 0 else throw (.incoherent kind id)
      let limit ← checked (offset + summary.size)
      if (declared.isSome || mode == .shape || kind != "struct") &&
          (offset % fieldAlign != 0 || fieldAlign > align || limit > size) then
        throw (.incoherent kind id)
      pure { state with fields := { ty, offset, size := summary.size, align := fieldAlign } :: state.fields })
    finish := fun state => do
      if hasOverlap state.fields then throw (.incoherent kind id)
      if transparent then
        let carriers := state.fields.filter (fun field => field.size != 0 || field.align != 1)
        match carriers with
        | [] => if size != 0 || align != 1 then throw (.incoherent kind id)
        | [carrier] =>
          if size != carrier.size || align != carrier.align || carrier.offset != 0 then
            throw (.incoherent kind id)
        | _ => throw (.incoherent kind id)
      finish mode { size, align := some align, fields := state.fields.reverse } }

def scaled (mode : Mode) (count child : Nat) : Equation :=
  { kind := .summary
    initial := .ok { size := 0, align := none }
    steps := [.child child fun summary _ => do
      let size ← checked (summary.size * count)
      finish mode { size, align := summary.align }]
    finish := Except.ok }

def alias := Equation.alias
def sequence := Equation.sequence

end TrustIr.SourceLayout

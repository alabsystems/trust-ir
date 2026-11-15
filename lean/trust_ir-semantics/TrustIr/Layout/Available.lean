-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Semantics.NatIndex

namespace TrustIr.SourceLayout.Available

/-- Exact domain of an equation index, retaining its sparse radix structure. -/
def domain {α : Type} : NatIndexTree α → NatIndexTree Unit
  | .empty => .empty
  | .node value even odd => .node (value.map (fun _ => ())) (domain even) (domain odd)

def size : NatIndexTree Unit → Nat
  | .empty => 0
  | .node value even odd => (if value.isSome then 1 else 0) + size even + size odd

/-- Removing a key changes only its value slot. Empty routing nodes can stay;
    cardinality, rather than numeric key size or a chosen fuel, is the rank. -/
def erase : NatIndexTree Unit → Nat → NatIndexTree Unit
  | .empty, _ => .empty
  | .node value even odd, key =>
    if key = 0 then .node none even odd
    else if key % 2 = 0 then .node value (erase even (key / 2)) odd
    else .node value even (erase odd (key / 2))

theorem find_domain {α : Type} (tree : NatIndexTree α) (key : Nat) :
    (domain tree).find key = (tree.find key).map (fun _ => ()) := by
  induction tree generalizing key with
  | empty => rfl
  | node value even odd evenIH oddIH =>
    by_cases zero : key = 0
    · simp [domain, NatIndexTree.find, zero]
    · by_cases parity : key % 2 = 0 <;>
        simp [domain, NatIndexTree.find, zero, parity, evenIH, oddIH]

theorem erase_size_lt (tree : NatIndexTree Unit) (key : Nat)
    (present : (tree.find key).isSome = true) : size (erase tree key) < size tree := by
  induction tree generalizing key with
  | empty => cases present
  | node value even odd evenIH oddIH =>
    by_cases zero : key = 0
    · subst key
      cases value <;> simp_all [erase, size, NatIndexTree.find] <;> omega
    · by_cases parity : key % 2 = 0
      · have child : (even.find (key / 2)).isSome = true := by
          simpa [NatIndexTree.find, zero, parity] using present
        have smaller := evenIH (key / 2) child
        simp only [erase, zero, ↓reduceIte, parity, size]
        omega
      · have child : (odd.find (key / 2)).isSome = true := by
          simpa [NatIndexTree.find, zero, parity] using present
        have smaller := oddIH (key / 2) child
        simp only [erase, zero, ↓reduceIte, parity, size]
        omega

end TrustIr.SourceLayout.Available

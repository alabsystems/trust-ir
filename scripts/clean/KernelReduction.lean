-- Copyright 2026 Andrew Yates | Apache-2.0
namespace CleanReductionProbe
universe u v
inductive PolyStep (α : Type u) (β : Type v) where
  | yield : α → β → PolyStep α β
  | skip : α → PolyStep α β
  | done : PolyStep α β
inductive MonoStep (α β : Type) where
  | yield : α → β → MonoStep α β
  | skip : α → MonoStep α β
  | done : MonoStep α β
inductive OneParam (α : Type u) where
  | some : α → OneParam α
  | none : OneParam α
 theorem directAppend : String.append "Load" ": use after dealloc" = "Load: use after dealloc" := rfl
 theorem emptyAppend : String.append "" "Load" = "Load" := rfl
 theorem toStringLiteral : toString ("Load" : String) = "Load" := rfl
 theorem natBeta : (fun x : Nat => x + 1) 2 = 3 := rfl
 theorem charListLiteral : String.ofList ['L', 'o', 'a', 'd'] = "Load" := rfl
end CleanReductionProbe

-- Copyright 2026 Andrew Yates | Apache-2.0
-- Independent replay probes: every statement is checked by Lean with rfl.
-- Export the five declarations with the official lean4export. A rejected
-- export is a regression reproducer, never evidence of Clean acceptance.
namespace CleanReplayProbe
 theorem natControl : (fun x : Nat => x + 1) 2 = 3 := rfl
 theorem stringControl : ("Load" : String) = "Load" := rfl
 theorem appendLoad : "Load" ++ ": use after dealloc" = "Load: use after dealloc" := rfl
 theorem appendStore : "Store" ++ ": use after dealloc" = "Store: use after dealloc" := rfl
 theorem interpolateLoad : s!"{"Load"}: use after dealloc" = "Load: use after dealloc" := rfl
end CleanReplayProbe

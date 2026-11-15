-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIrEval.DecodePlanKinds
import TrustIr.Proofs.SourceLayoutDeterminism

namespace TrustIrEval
open TrustIr SourceLayout AggregateMemory

/-- Actual decoded source association and complete successful query histories
supply the original memo's coherence with the precise returned typed root.
Neither an arbitrary memo-validity oracle nor a reset between queries is used. -/
theorem decoded_layout_query_prior_memo (document : Lean.Json) (decoded : Module)
    (parsed : module document = .ok decoded) (maxDepth : Nat) (ctx : EvalContext)
    (prepared : contextOf decoded maxDepth = .ok ctx)
    (earlier current next : Session)
    (startChain : Session.QueryChain (SourceLayout.prepare (decodedCaptureSource decoded ctx.byteModel)) earlier)
    (continuation : Session.QueryChain earlier current)
    (mode : Mode) (ty : Ty) (value : Summary)
    (run : current.query mode ty = .ok (value,next)) :
    CaptureSource (decodedCaptureSource decoded ctx.byteModel) ctx ∧
      ∃ root, Session.CompiledRoot (decodedCaptureSource decoded ctx.byteModel) mode ty root next.graph ∧
        ∀ old, earlier.memo.find root = some old → old = value :=
  ⟨decoded_context_capture_source document decoded parsed maxDepth ctx prepared,
   continuation.query_agrees_with_prior_memo (startChain.reachable .prepared) mode ty value run⟩

end TrustIrEval

/-- info: 'TrustIrEval.decoded_layout_query_prior_memo' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIrEval.decoded_layout_query_prior_memo

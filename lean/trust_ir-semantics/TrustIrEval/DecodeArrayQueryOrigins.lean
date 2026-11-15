-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIrEval.DecodeLayoutDeterminism
import TrustIr.Proofs.SourceLayoutArrayOrigin

namespace TrustIrEval
open TrustIr SourceLayout AggregateMemory

/-- Actual decoded source histories supply source-array child derivations and
slot bounds. The child is the original source node, not an arbitrary equal-size
layout, and no physical parent bound is supplied by the caller. -/
theorem decoded_layout_array_geometry (document : Lean.Json) (decoded : Module)
    (parsed : module document = .ok decoded) (maxDepth : Nat) (ctx : EvalContext)
    (prepared : contextOf decoded maxDepth = .ok ctx) (session next : Session)
    (history : Session.QueryChain (SourceLayout.prepare (decodedCaptureSource decoded ctx.byteModel)) session)
    (mode : Mode) (id : TyId) (count : Nat) (value : Summary)
    (run : session.query mode (.Array id count) = .ok (value,next)) :
    CaptureSource (decodedCaptureSource decoded ctx.byteModel) ctx ∧
      ∃ child, NodeDerivation next.graph
        ((Index.ofEnvironment (decodedCaptureSource decoded ctx.byteModel)).node mode id.index) child ∧
        value.size = child.size * count ∧ value.align = child.align ∧
        ∀ slot, slot < count → ∀ offset width, offset + width ≤ child.size →
          slot * child.size + offset + width ≤ value.size :=
  ⟨decoded_context_capture_source document decoded parsed maxDepth ctx prepared,
   (history.reachable .prepared).query_array_geometry mode id count value run⟩

end TrustIrEval

/-- info: 'TrustIrEval.decoded_layout_array_geometry' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIrEval.decoded_layout_array_geometry

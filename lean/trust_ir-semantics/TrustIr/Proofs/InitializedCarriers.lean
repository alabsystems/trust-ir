-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.SourceValueMembership
import TrustIr.Proofs.FrameValueValidity

namespace TrustIr.InitializedCarriers

/-- Initialization retains the exact nominal identity, without asserting that
    its original declaration exists or that any ABI ignores the value. -/
theorem function_item_initialized (target : FuncId) :
    (Value.fnItem target).Initialized := .fnItem target

theorem initialized_item_still_checks_original_declaration (ctx : EvalContext) (target : FuncId)
    (missing : ctx.functionItems target = none) :
    (Value.fnItem target).Initialized ∧
      functionItemDeclaration ctx target =
        .error (.typeError "FnItem: original function declaration is absent") := by
  refine ⟨.fnItem target, ?_⟩
  trustIrCompilerProof { rw [functionItemDeclaration, missing] } {
    exact congrArg (fun declaration : Option (Except String FunctionItemHeader) =>
      match declaration with
      | some (.ok header) => Except.ok (ε := SemError) header
      | some (.error message) => .error (.typeError message)
      | none => .error (.typeError "FnItem: original function declaration is absent")) missing
  }

/-- Arbitrary source labels cannot turn an unwritten captured slot into an
    initialized source frame, even when no bytes would be carried by an ABI. -/
theorem source_frame_unwritten_not_initialized (lineage : Nat) (function : FuncId)
    (declaration : BindingFrameDef) :
    ¬ (Value.sourceFrame lineage function declaration [.uninit]).Initialized := by
  intro initialized
  have impossible := initialized.sourceFrame_child .uninit (trustIrListMemConsSelf _ _)
  cases impossible

theorem source_frame_poison_not_initialized (lineage : Nat) (function : FuncId)
    (declaration : BindingFrameDef) (ty : Ty) :
    ¬ (Value.sourceFrame lineage function declaration [.undef ty]).Initialized := by
  intro initialized
  have impossible := initialized.sourceFrame_child (.undef ty) (trustIrListMemConsSelf _ _)
  cases impossible

/-- Capture initialization is deep, rather than a top-level frame label test. -/
theorem source_frame_nested_unwritten_not_initialized (lineage : Nat) (function : FuncId)
    (declaration : BindingFrameDef) :
    ¬ (Value.sourceFrame lineage function declaration [.aggregate [.uninit]]).Initialized := by
  intro initialized
  have aggregate := initialized.sourceFrame_child (.aggregate [.uninit])
    (trustIrListMemConsSelf _ _)
  have impossible := aggregate.aggregate_child .uninit (trustIrListMemConsSelf _ _)
  cases impossible

/-- An initialized capture list supplies no minted-frame identity. This is an
    actual source-frame counterexample, retaining all its original metadata. -/
theorem initialized_source_frame_need_not_be_minted (function target : FuncId)
    (declaration : BindingFrameDef) :
    (Value.sourceFrame 0 function declaration [.fnItem target]).Initialized ∧
      ¬ FrameLifetime.MintedValue 0 (.sourceFrame 0 function declaration [.fnItem target]) := by
  constructor
  · apply Value.Initialized.sourceFrame
    intro value member
    cases member with
    | head => exact .fnItem target
    | tail _ impossible => cases impossible
  · intro minted
    have impossible := minted 0 (FrameLifetime.FrameOccurs.sourceRoot function declaration _)
    exact Nat.not_lt_zero 0 impossible

/-- Conversely, recursive frame-identity validity deliberately permits poison;
    it must never be used as an initialization or source-NoUB witness. -/
theorem frame_identity_validity_is_not_initialization (bound : Nat) (ty : Ty) :
    FrameLifetime.MintedValue bound (.undef ty) ∧ ¬ (Value.undef ty).Initialized := by
  refine ⟨FrameLifetime.mintedValue_undef bound ty, ?_⟩
  intro impossible
  cases impossible

end TrustIr.InitializedCarriers

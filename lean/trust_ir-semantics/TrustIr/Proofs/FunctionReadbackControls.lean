-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.SourceRecursiveReadback

run_cmd do
  if Lean.versionString == "4.30.0-rc2" then
    let env ← Lean.getEnv
    let mut registered := 0
    for (n, _) in env.constants.map₁.toList do
      if n.toString.endsWith "TrustIr.SourceLayout.compileTy.eq_def" ||
         n.toString.endsWith "TrustIr.SourceLayout.compileTypes.eq_def" then
        Lean.Elab.Command.elabCommand (← `(command| attribute [local cbv_eval] $(Lean.mkIdent n):ident))
        registered := registered + 1
    unless registered == 2 do
      Lean.throwError "expected the two original layout compiler equations"
  else if Lean.versionString != "4.8.0" then
    Lean.throwError "unsupported compiler for layout equation reduction"

namespace TrustIr.AggregateMemory.FunctionReadbackControls
open SourceLayout

private def code : Plan := .leaf (.Func ⟨0⟩) ⟨8,8⟩
private def codes : Plan := .array (.Array ⟨0⟩ 2) ⟨16,8⟩ 2 code
private def rootTy : Ty := .Tuple [.Func ⟨0⟩,.Array ⟨0⟩ 2,.U8]
private def fields : List (Nat × Plan) := [(0,code),(8,codes),(24,.leaf .U8 ⟨1,1⟩)]
private def plan : Plan := .fields rootTy ⟨32,8⟩ fields
private def source : Environment := { types := [some (.Func ⟨0⟩)], enums := [] }
private def ids : List FuncId := [⟨42⟩,⟨7⟩,⟨42⟩]
private def function : Value := .fnDef ⟨0⟩ ⟨42⟩
private def input : Value := .aggregate [function,.array (.uniform 2 function),.int 8 257]
private def stored : Image := match encode .le64 (some ids) plan input false with
  | .ok image => image
  | .error _ => { bytes := ByteImage.empty }
private theorem prepared : (prepare source []).query rootTy = .ok plan := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact (by trustIrReduce)
  }

private theorem encoded : encode .le64 (some ids) plan input false = .ok stored := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact (by trustIrReduce)
  }

private theorem functionReady : ReadbackInput .le64 (some ids) Memory.empty code function := by
  trustIrCompilerProof {
    exact .function (.registered ids ⟨0⟩ ⟨42⟩ 0 ⟨8,8⟩ rfl (by decide) rfl)
  } {
    exact .function (.registered ids ⟨0⟩ ⟨42⟩ 0 ⟨8,8⟩ (by trustIrReduce) (by decide) (by trustIrReduce))
  }

private theorem ready : ReadbackInput .le64 (some ids) Memory.empty plan input := by
  trustIrCompilerProof {
    exact ReadbackInput.fields_of_pairs rootTy ⟨32,8⟩ fields _ (.cons functionReady (.cons (.array_uniform _ _ _ _ _ functionReady) (.cons
      (.scalar (.integer .U8 ⟨1,1⟩ 8 257 rfl rfl rfl)) .nil)))
  } {
    exact ReadbackInput.fields_of_pairs rootTy ⟨32,8⟩ fields _ (.cons functionReady (.cons (.array_uniform _ _ _ _ _ functionReady) (.cons
      (.scalar (.integer .U8 ⟨1,1⟩ 8 257 (by trustIrReduce) (by trustIrReduce) (by trustIrReduce))) .nil)))
  }

theorem prepared_record_and_function_array :
    ∃ output, decode .le64 (some ids) Memory.empty plan stored.bytes = .ok output ∧
      ValueReadback .le64 Memory.empty input output :=
  prepared_recursive_readback source [] rootTy plan prepared .le64 (some ids) Memory.empty input ready
    (by intro layout width raw impossible; cases impossible) stored encoded

theorem target32_function_readback (memory : Memory) :
    (encode .le32 (some ids) (.leaf (.Func ⟨0⟩) ⟨4,4⟩) function false).bind
      (fun image => decode .le32 (some ids) memory (.leaf (.Func ⟨0⟩) ⟨4,4⟩) image.bytes) = .ok function := by
  trustIrCompilerProof {
    exact function_aggregate_leaf_roundtrip .le32 ids memory ⟨0⟩ ⟨42⟩ 0 ⟨4,4⟩ rfl (by decide) rfl
  } {
    exact function_aggregate_leaf_roundtrip .le32 ids memory ⟨0⟩ ⟨42⟩ 0 ⟨4,4⟩ (by trustIrReduce) (by decide) (by trustIrReduce)
  }

theorem duplicate_table_uses_first_position :
    encodeMemoryWithFunctions .le64 (some ids) (.Func ⟨0⟩) function = .ok [1,0,0,0,0,0,0,0] := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact (by trustIrReduce)
  }

theorem changed_table_changes_target :
    decode .le64 (some [⟨99⟩]) Memory.empty code (ByteImage.ofList [some 1,some 0,some 0,some 0,some 0,some 0,some 0,some 0]) =
      .ok (.fnDef ⟨0⟩ ⟨99⟩) := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact (by trustIrReduce)
  }

theorem missing_table_refuses_store :
    encode .le64 none code function false =
      .error (.unsupported .layout "function pointer Store requires a source function table") := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact (by trustIrReduce)
  }

theorem missing_target_refuses_store :
    encode .le64 (some []) code function false = .error (.typeError "Store: undefined function pointer") := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact (by trustIrReduce)
  }

theorem mismatched_signature_refuses_store :
    encode .le64 (some ids) code (.fnDef ⟨1⟩ ⟨42⟩) false =
      .error (.typeError "Store: function pointer signature does not match type") := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact (by trustIrReduce)
  }

theorem unknown_word_refuses_load :
    decode .le64 (some ids) Memory.empty code (ByteImage.ofList [some 4,some 0,some 0,some 0,some 0,some 0,some 0,some 0]) =
      .error (.typeError "Load: unregistered function pointer address") := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact (by trustIrReduce)
  }

theorem null_without_table_readback :
    (encode .le64 none code .nullPtr false).bind (fun image => decode .le64 none Memory.empty code image.bytes) = .ok .nullPtr := by
  trustIrCompilerProof {
    exact null_function_aggregate_leaf_roundtrip .le64 none Memory.empty ⟨0⟩ ⟨8,8⟩ rfl
  } {
    exact null_function_aggregate_leaf_roundtrip .le64 none Memory.empty ⟨0⟩ ⟨8,8⟩ (by trustIrReduce)
  }

theorem missing_table_has_no_function_certificate :
    ¬ FunctionReadbackInput .le64 none code function := by
  intro admitted
  cases admitted

end TrustIr.AggregateMemory.FunctionReadbackControls

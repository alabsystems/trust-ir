-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.GenericCoroModuleFactory
import TrustIr.Proofs.GenericCoroAllBlocksControls

namespace TrustIr.GenericCoro.ModuleFactory.Controls
open TrustIrEval GenericCoroAllBlocksPlanner

def declaration : Function :=
  { id := ⟨65537⟩, name := "external", ty := ⟨0⟩, entry := ⟨99⟩,
    isDeclaration := true, callingConvention := .Cold, blocks := .ok [] }

def coroutine (id : Nat) (name : String) : Function :=
  { id := ⟨id⟩, name, ty := ⟨0⟩, entry := ⟨0⟩,
    isDeclaration := false, callingConvention := .Rust,
    blocks := .ok (AllBlocks.Controls.graph false) }

def ordinary : Function :=
  { id := ⟨3⟩, name := "identity", ty := ⟨1⟩, entry := ⟨7⟩,
    isDeclaration := false, callingConvention := .Fast,
    blocks := .ok [(⟨7⟩, {params := [(⟨9⟩, .I32)], body := [], terminator := .Return [⟨9⟩]})] }

def source : Module :=
  { byteModel := .ok .le32, hasTargetInfo := true,
    functions := [declaration, coroutine 4294967295 "first", ordinary, coroutine 17 "second"],
    funcTys := [{params := [.Ptr, .I32], returns := [.I32], isVararg := false},
      {params := [.I32], returns := [.I32], isVararg := false}],
    globals := [], enums := [], structs := [], types := [some .I32, none],
    records := [(⟨31⟩, none)], dropGlue := [(⟨65537⟩, some .I32)] }

def emitted : Function :=
  { coroutine 4294967295 "first" with blocks := .ok [(⟨0⟩, AllBlocks.Controls.entry),
     (⟨1⟩, expandedEntry ⟨⟨4⟩, ⟨6⟩, ⟨7⟩⟩ AllBlocks.Controls.first),
     (⟨2⟩, expandedEntry ⟨⟨8⟩, ⟨9⟩, ⟨10⟩⟩ AllBlocks.Controls.second)] }

def target : Module :=
  { source with functions := [declaration, emitted, ordinary,
    { emitted with id := ⟨17⟩, name := "second" }] }

/-- Two changed definitions share no cursor: both use the same actual fresh
    triples within their own lexical namespaces. Source order is not id order. -/
theorem actual_multifunction_ast : transform source = .ready target := rfl

theorem actual_ast_headers_and_order : target.functions.map functionHeader = source.functions.map functionHeader :=
  transform_headers source target actual_multifunction_ast

theorem actual_all_other_fields : {target with functions := source.functions} = source :=
  (transform_ready source target actual_multifunction_ast).1

theorem actual_no_suspend_terminators :
    ∀ function ∈ target.functions, ∀ blocks, function.blocks = .ok blocks → suspendCount blocks = 0 :=
  transform_noSuspends source target actual_multifunction_ast

theorem actual_produced_not_assumed :
    Produced source.funcTys.toArray (directHeaders (headerIndex source.funcTys.toArray source.functions))
      source.functions target.functions :=
  transform_produced source target actual_multifunction_ast

/-- A later body failure discards the earlier transformed body. The exact
    decoder payload remains available to the caller. -/
theorem retained_decode_failure_rolls_back :
    transform {source with functions := [coroutine 17 "processed", {ordinary with blocks := .error (.unsupported "inst.future_opcode")}, declaration]} =
      .rejected {source with functions := [coroutine 17 "processed", {ordinary with blocks := .error (.unsupported "inst.future_opcode")}, declaration]}
        (.decode ⟨3⟩ (.unsupported "inst.future_opcode")) := rfl

theorem inference_failure_rolls_back :
    transform {source with functions := [coroutine 17 "processed",
      {ordinary with blocks := .ok AllBlocks.Controls.cyclicGraph}]} =
      .rejected {source with functions := [coroutine 17 "processed",
        {ordinary with blocks := .ok AllBlocks.Controls.cyclicGraph}]}
        (.inference ⟨3⟩ (.typeError "SSA types: cyclic borrow declarations")) := rfl

theorem malformed_payload_is_not_relabelled :
    lowerFunction source.funcTys.toArray (fun _ => none)
      {ordinary with blocks := .error (.malformed "original schema diagnostic")} =
      .error (.decode ⟨3⟩ (.malformed "original schema diagnostic")) := rfl

theorem forged_declaration_has_explicit_error :
    lowerFunction source.funcTys.toArray (fun _ => none) {ordinary with isDeclaration := true} =
      .error (.decode ⟨3⟩ (.malformed "function identity: declaration has a body")) := rfl

theorem absent_function_signature_refuses :
    lowerFunction source.funcTys.toArray (fun _ => none) {ordinary with ty := ⟨42⟩} =
      .error (.decode ⟨3⟩ (.malformed "function identity: func type 42 not in table")) := rfl

def preparationTag {domain : Nat} {blocks : Rows} : Except SemError (RowExpansion domain blocks) → Nat
  | .error _ => 0
  | .ok (.unchanged _) => 1
  | .ok (.capacity _ _) => 2
  | .ok (.expanded _ _ _) => 3

theorem real_partial_capacity_certificate :
    preparationTag (prepareRows 10 (fun _ => none) (fun _ => none) (AllBlocks.Controls.graph false)) = 2 := rfl

theorem source_error_precedes_zero_capacity :
    preparationTag (prepareRows 0 (fun _ => none) (fun _ => none) AllBlocks.Controls.cyclicGraph) = 0 := rfl

theorem no_suspend_needs_no_capacity :
    preparationTag (prepareRows 0 (fun _ => none) (fun _ => none) []) = 1 := rfl

theorem duplicate_id_first_missing_signature_stays_missing :
    directHeaders (headerIndex source.funcTys.toArray
      [{ordinary with ty := ⟨999⟩}, ordinary]) ⟨3⟩ = none := rfl

theorem duplicate_id_first_signature_stays_first :
    directHeaders (headerIndex source.funcTys.toArray
      [ordinary, {ordinary with ty := ⟨0⟩}]) ⟨3⟩ = (trustIrArrayGet? source.funcTys.toArray 1) := rfl

theorem declarations_keep_bodyless_status :
    lowerFunction source.funcTys.toArray (fun _ => none) declaration = .ok declaration := rfl

theorem empty_module_identity :
    transform {source with functions := []} = .ready {source with functions := []} := rfl

def callPrefix : BasicBlock :=
  { params := [(⟨0⟩, .Ptr), (⟨1⟩, .I32)],
    body := [.Call ⟨65537⟩ [⟨0⟩, ⟨1⟩]], bodyResultDests := [[⟨9⟩]],
    terminator := .CoroSuspend ⟨0⟩ 0 17 ⟨9⟩ }

def caller : Function :=
  {coroutine 17 "caller" with blocks := .ok [(⟨0⟩, callPrefix)]}

def expandedCaller : Function :=
  {caller with blocks := .ok [(⟨0⟩, expandedEntry ⟨⟨2⟩, ⟨3⟩, ⟨4⟩⟩ callPrefix)]}

/-- A bodyless declaration still supplies the original direct-call result
    types. No invented executable body participates in inference. -/
theorem declaration_header_types_real_call_prefix :
    lowerFunction source.funcTys.toArray
      (directHeaders (headerIndex source.funcTys.toArray source.functions)) caller = .ok expandedCaller := rfl

theorem actual_call_prefix_preparation_provenance :
    PreparedAt source.funcTys.toArray
      (directHeaders (headerIndex source.funcTys.toArray source.functions)) caller expandedCaller :=
  lowerFunction_prepared _ _ _ _ declaration_header_types_real_call_prefix

theorem duplicate_function_occurrences_both_emitted :
    transform {source with functions := [coroutine 17 "first", coroutine 17 "second"]} =
      .ready {source with functions := [{emitted with id := ⟨17⟩},
        {emitted with id := ⟨17⟩, name := "second"}]} := rfl

end TrustIr.GenericCoro.ModuleFactory.Controls

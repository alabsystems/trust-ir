-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.DecodedContext
import TrustIr.Proofs.FunctionMemoryProps
import TrustIr.Proofs.GenericCoroPrefixLayer

-- Generated smart equations duplicate the complete contextual evaluator.
-- Direct reduction keeps the same kernel judgment and resource budgets.
set_option smartUnfolding false

namespace TrustIr.FunctionItemProps

open SourceLayout

/-- Nominal equality preserves the function identifier independently of bytes. -/
theorem nominal_equality (first second : FuncId) :
    closureTyEq (.FnItem first) (.FnItem second) = (first.index == second.index) := by
  rw [closureTyEq]

theorem item_is_not_unit (target : FuncId) :
    closureTyEq (.FnItem target) .Unit = false := by rw [closureTyEq] <;> (intros; contradiction)

theorem item_is_not_a_pointer (target : FuncId) (signature : FuncTyId) :
    closureTyEq (.FnItem target) (.Func signature) = false := by rw [closureTyEq] <;> (intros; contradiction)

theorem runtime_retains_nominal_type (target : FuncId) :
    Value.ty (.fnItem target) = .FnItem target := rfl

/-- Prepared nominal storage emits neither a code word nor a scalar callback. -/
theorem prepared_item_encoder (model : ByteModel) (order : FunctionAddressOrder) (target : FuncId) :
    AggregateMemory.encode model order (.fnItem target ⟨0,1⟩) (.fnItem target) false =
      .ok { bytes := ByteImage.empty } := by
  rw [AggregateMemory.encode_fnItem,Value.isUninit,Value.isPoison]
  change (if decide (target = target) then
    (Except.ok { bytes := ByteImage.empty } : Except SemError AggregateMemory.Image)
    else .error (.typeError "memory image: function item identity does not match its source type")) = _
  rw [decide_eq_true (Eq.refl target)]
  rfl
  all_goals (intros; contradiction)

/-- The requested prepared type determines the singleton independently of bytes. -/
theorem prepared_item_decoder (model : ByteModel) (order : FunctionAddressOrder)
    (memory : Memory) (target : FuncId) :
    AggregateMemory.decode model order memory (.fnItem target ⟨0,1⟩) ByteImage.empty =
      .ok (.fnItem target) := by
  rw [AggregateMemory.decode_fnItem]
  rfl

theorem prepared_item_wrong_identity :
    AggregateMemory.encode .le64 none (.fnItem ⟨11⟩ ⟨0,1⟩) (.fnItem ⟨53⟩) false =
      .error (.typeError "memory image: function item identity does not match its source type") := by
  rw [AggregateMemory.encode_fnItem]
  rfl

theorem prepared_item_wrong_carrier :
    AggregateMemory.encode .le64 none (.fnItem ⟨11⟩ ⟨0,1⟩) (.aggregate []) false =
      .error (.typeError "memory image: expected a nominal function item") := by
  rw [AggregateMemory.encode_fnItem]
  rfl

theorem prepared_item_wrong_size :
    AggregateMemory.encode .le64 none (.fnItem ⟨11⟩ ⟨1,1⟩) (.fnItem ⟨11⟩) false =
      .error (.typeError "memory image: function item layout is not zero-sized/alignment-one") := by
  rw [AggregateMemory.encode_fnItem]
  rfl

theorem prepared_item_wrong_alignment :
    AggregateMemory.encode .le64 none (.fnItem ⟨11⟩ ⟨0,2⟩) (.fnItem ⟨11⟩) false =
      .error (.typeError "memory image: function item layout is not zero-sized/alignment-one") := by
  rw [AggregateMemory.encode_fnItem]
  rfl

theorem prepared_item_poison :
    AggregateMemory.encode .le64 none (.fnItem ⟨11⟩ ⟨0,1⟩) (.undef (.FnItem ⟨11⟩)) false =
      .error (.ub "memory image: inspecting poison") := by
  rw [AggregateMemory.encode_fnItem]
  rfl

theorem prepared_item_layout_precedes_poison :
    AggregateMemory.encode .le64 none (.fnItem ⟨11⟩ ⟨1,1⟩) (.undef (.FnItem ⟨11⟩)) false =
      .error (.typeError "memory image: function item layout is not zero-sized/alignment-one") := by
  rw [AggregateMemory.encode_fnItem]
  rfl

theorem prepared_item_unwritten :
    AggregateMemory.encode .le64 none (.fnItem ⟨11⟩ ⟨0,1⟩) .uninit false =
      .error (.ub "memory image: inspecting an unwritten lane") := by
  rw [AggregateMemory.encode_fnItem]
  rfl

theorem prepared_item_allowed_unwritten :
    AggregateMemory.encode .le64 none (.fnItem ⟨11⟩ ⟨0,1⟩) .uninit true =
      .ok { bytes := ByteImage.fill 0 none, unwritten := [(0,0)] } := by
  rw [AggregateMemory.encode_fnItem]
  rfl

theorem prepared_item_image_extent :
    AggregateMemory.decode .le64 none Memory.empty (.fnItem ⟨11⟩ ⟨0,1⟩)
      (ByteImage.fill 1 (some 0)) =
      .error (.typeError "Load: image size does not match source layout") := by
  rw [AggregateMemory.decode_fnItem]
  rfl

theorem prepared_item_decode_alignment :
    AggregateMemory.decode .le64 none Memory.empty (.fnItem ⟨11⟩ ⟨0,2⟩) ByteImage.empty =
      .error (.typeError "Load: function item layout is not zero-sized/alignment-one") := by
  rw [AggregateMemory.decode_fnItem]
  rfl

/-- Forging an ordinary scalar plan never waives its original codec obligation. -/
theorem ordinary_item_encoder_refuses (model : ByteModel) (order : FunctionAddressOrder)
    (target : FuncId) (layout : MemoryTypeLayout) (value : Value) (image : AggregateMemory.Image) :
    AggregateMemory.encode model order (.leaf (.FnItem target) layout) value false ≠ .ok image :=
  AggregateMemory.encode_fnItem_as_scalar_leaf_refuses model order target layout value image

theorem ordinary_item_decoder_refuses (model : ByteModel) (order : FunctionAddressOrder)
    (memory : Memory) (target : FuncId) (layout : MemoryTypeLayout) (image : ByteImage) (value : Value) :
    AggregateMemory.decode model order memory (.leaf (.FnItem target) layout) image ≠ .ok value :=
  AggregateMemory.decode_fnItem_as_scalar_leaf_refuses model order memory target layout image value

/-- Declaration lookup does not inspect an executable body. -/
theorem declaration_only (context : EvalContext) (target : FuncId)
    (header : FunctionItemHeader)
    (present : context.functionItems target = some (.ok header)) :
    functionItemDeclaration context target = .ok header := by
  simp only [functionItemDeclaration, present]

theorem no_declaration_no_item (context : EvalContext) (target : FuncId)
    (absent : context.functionItems target = none) :
    functionItemDeclaration context target =
      .error (.typeError "FnItem: original function declaration is absent") := by
  simp only [functionItemDeclaration, absent]

private def signature : FuncTyDef :=
  { params := [], returns := [.U32], isVararg := false }

/-- Sparse, distinct identities share a signature and carry no runtime bytes. -/
private def source (model : ByteModel) : SourceLayout.Environment :=
  { model,
    types := [some (.FnItem ⟨11⟩)],
    functions := [(⟨53⟩, ⟨0⟩), (⟨11⟩, ⟨0⟩)],
    funcTypes := [signature] }

private def geometry (result : SourceLayout.Result SourceLayout.Summary) :
    Option (Nat × Option Nat) :=
  match result with
  | .ok summary => some (summary.size, summary.align)
  | .error _ => none

private theorem item_inhabit (index : Index) (target : FuncId) :
    inhabitFormula index (.FnItem target) = .no := by simp [inhabitFormula]

private theorem insert_zero {α : Type} (tree : NatIndexTree α) (value : α) :
    tree.insert 0 value = .node (some value) tree.even tree.odd := by
  rw [NatIndexTree.insert_unfold]
  rfl

private theorem find_empty {α : Type} (key : Nat) :
    (NatIndexTree.empty : NatIndexTree α).find key = none := rfl

private theorem find_zero {α : Type} (tree : NatIndexTree α) :
    tree.find 0 = tree.value := by rw [NatIndexTree.find_unfold]; rfl

macro "item_source_compute" : tactic =>
  `(tactic| trustIrReduce)

theorem item32 :
    geometry (SourceLayout.query (source .le32) .execution (.FnItem ⟨11⟩)) =
      some (0, some 1) := by item_source_compute

theorem item64 :
    geometry (SourceLayout.query (source .le64) .execution (.FnItem ⟨53⟩)) =
      some (0, some 1) := by item_source_compute

theorem huge_zero_byte_array32 :
    geometry (SourceLayout.query (source .le32) .execution (.Array ⟨0⟩ (2 ^ 40))) =
      some (0, some 1) := by item_source_compute

theorem huge_zero_byte_array64 :
    geometry (SourceLayout.query (source .le64) .execution (.Array ⟨0⟩ (2 ^ 40))) =
      some (0, some 1) := by item_source_compute

theorem missing_identity_refuses :
    geometry (SourceLayout.query (source .le64) .execution (.FnItem ⟨12⟩)) = none := by item_source_compute

theorem duplicate_identity_refuses :
    geometry (SourceLayout.query
      { source .le64 with functions := [(⟨11⟩, ⟨0⟩), (⟨11⟩, ⟨0⟩)] }
      .execution (.FnItem ⟨11⟩)) = none := by item_source_compute

theorem missing_signature_refuses :
    geometry (SourceLayout.query
      { source .le64 with functions := [(⟨11⟩, ⟨1⟩)] }
      .execution (.FnItem ⟨11⟩)) = none := by item_source_compute

private def target (id : FuncId) (answer : Int) : TrustIrEval.Function :=
  { id, name := "pick", ty := ⟨0⟩, entry := ⟨0⟩, isDeclaration := false,
    blocks := .ok [(⟨0⟩,
      { params := [], body := [.Const .U32 (.int answer)],
        bodyResultDests := [[⟨0⟩]], terminator := .Return [⟨0⟩] })] }

private def applyItem (id item : FuncId) (sig : FuncTyId) : TrustIrEval.Function :=
  { id, name := "apply", ty := sig, entry := ⟨0⟩, isDeclaration := false,
    blocks := .ok [(⟨0⟩,
      { params := [(⟨0⟩, .FnItem item)],
        body := [.CallIndirect ⟨0⟩ ⟨0⟩ [] .C],
        bodyResultDests := [[⟨1⟩]], terminator := .Return [⟨1⟩] })] }

private def pairEntry : TrustIrEval.Function :=
  { id := ⟨0⟩, name := "entry", ty := ⟨0⟩, entry := ⟨0⟩,
    isDeclaration := false,
    blocks := .ok [(⟨0⟩,
      { params := [],
        body := [
          .Const (.Tuple [.FnItem ⟨11⟩, .FnItem ⟨53⟩])
            (.aggregate [.fnItem ⟨11⟩, .fnItem ⟨53⟩]),
          .ExtractField (.FnItem ⟨11⟩) ⟨0⟩ 0,
          .ExtractField (.FnItem ⟨53⟩) ⟨0⟩ 1,
          .Call ⟨30⟩ [⟨1⟩], .Call ⟨31⟩ [⟨2⟩],
          .Const .U32 (.int 10), .BinOp .Mul .U32 ⟨3⟩ ⟨5⟩,
          .BinOp .Add .U32 ⟨6⟩ ⟨4⟩],
        bodyResultDests := [[⟨0⟩], [⟨1⟩], [⟨2⟩], [⟨3⟩], [⟨4⟩],
          [⟨5⟩], [⟨6⟩], [⟨7⟩]], terminator := .Return [⟨7⟩] })] }

private def itemModule : TrustIrEval.Module :=
  { functions := [pairEntry, target ⟨53⟩ 2, applyItem ⟨30⟩ ⟨11⟩ ⟨1⟩,
      target ⟨11⟩ 1, applyItem ⟨31⟩ ⟨53⟩ ⟨2⟩],
    funcTys := [signature,
      { signature with params := [.FnItem ⟨11⟩] },
      { signature with params := [.FnItem ⟨53⟩] }, signature],
    globals := [], enums := [], structs := [], types := [] }

/-- Build the original decoded module's indexes and execute its actual entry.
    A failed context construction remains separate from a semantic refusal. -/
private def decodedRun (module : TrustIrEval.Module) (arguments : List Value := []) :
    Option (Except SemError (List Value)) :=
  match TrustIrEval.contextOf module 8 with
  | .error _ => none
  | .ok context => some ((Sem.run
      (evalFunctionInContext context ⟨0⟩ arguments 8) MachineState.empty).map Prod.fst)

-- Keep the original entry and all eight production rows. Splitting at their
-- actual call boundaries lets both kernels check the same run at the original
-- resource indices without reducing both nested calls in one proof traversal.
-- Ordinary rows publish their fresh value again at the named SSA destination;
-- the states below retain that exact representation instead of identifying maps.

private def pairContext : EvalContext :=
  (TrustIrEval.contextOf itemModule 8).toOption.get (by trustIrReduce)
private theorem pair_context_ok : TrustIrEval.contextOf itemModule 8 = .ok pairContext := by trustIrReduce
private def pairView : EvalFunction := (pairContext.functions ⟨0⟩).get (by trustIrReduce)
private def pairActive : EvalContext := pairContext.forFunction pairView
private def pairRecurse : GenericCoro.Prefix.Recurse :=
  fun ctx depth cfg pc args strat => stepNWithContext ctx 7 depth cfg pc args strat
private def pairRow0 : Inst × List ValueId := (.Const (.Tuple [.FnItem ⟨11⟩, .FnItem ⟨53⟩]) (.aggregate [.fnItem ⟨11⟩, .fnItem ⟨53⟩]), [⟨0⟩])
private def pairRow1 : Inst × List ValueId := (.ExtractField (.FnItem ⟨11⟩) ⟨0⟩ 0, [⟨1⟩])
private def pairRow2 : Inst × List ValueId := (.ExtractField (.FnItem ⟨53⟩) ⟨0⟩ 1, [⟨2⟩])
private def pairRow3 : Inst × List ValueId := (.Call ⟨30⟩ [⟨1⟩], [⟨3⟩])
private def pairRow4 : Inst × List ValueId := (.Call ⟨31⟩ [⟨2⟩], [⟨4⟩])
private def pairRow5 : Inst × List ValueId := (.Const .U32 (.int 10), [⟨5⟩])
private def pairRow6 : Inst × List ValueId := (.BinOp .Mul .U32 ⟨3⟩ ⟨5⟩, [⟨6⟩])
private def pairRow7 : Inst × List ValueId := (.BinOp .Add .U32 ⟨6⟩ ⟨4⟩, [⟨7⟩])
private def pairRows : List (Inst × List ValueId) :=
  [pairRow0, pairRow1, pairRow2, pairRow3, pairRow4, pairRow5, pairRow6, pairRow7]
private def pairBind (state : MachineState) (id : Nat) (value : Value) : MachineState :=
  { state with locals := state.locals.set ⟨id⟩ value, nextValueId := id + 1 }
private def pairBindTwice (state : MachineState) (id : Nat) (value : Value) : MachineState :=
  { state with locals := (state.locals.set ⟨id⟩ value).set ⟨id⟩ value, nextValueId := id + 1 }
private def pairState0 : MachineState := MachineState.empty
private def pairState1 := pairBindTwice pairState0 0 (.aggregate [.fnItem ⟨11⟩, .fnItem ⟨53⟩])
private def pairState2 := pairBindTwice pairState1 1 (.fnItem ⟨11⟩)
private def pairState3 := pairBindTwice pairState2 2 (.fnItem ⟨53⟩)
private def pairState4 := pairBind pairState3 3 (.int 32 1)
private def pairState5 := pairBind pairState4 4 (.int 32 2)
private def pairState6 := pairBindTwice pairState5 5 (.int 32 10)
private def pairState7 := pairBindTwice pairState6 6 (.int 32 10)
private def pairState8 := pairBindTwice pairState7 7 (.int 32 12)

private theorem pair_row0 :
    Sem.run (GenericCoro.Prefix.evalBodyStep pairRecurse pairActive 8 .abort
      pairRow0) pairState0 =
        .ok (.yield (), pairState1) := by trustIrReduce

private theorem pair_row1 :
    Sem.run (GenericCoro.Prefix.evalBodyStep pairRecurse pairActive 8 .abort
      pairRow1) pairState1 =
        .ok (.yield (), pairState2) := by trustIrReduce

private theorem pair_row2 :
    Sem.run (GenericCoro.Prefix.evalBodyStep pairRecurse pairActive 8 .abort
      pairRow2) pairState2 =
        .ok (.yield (), pairState3) := by trustIrReduce

private theorem pair_row3 :
    Sem.run (GenericCoro.Prefix.evalBodyStep pairRecurse pairActive 8 .abort
      pairRow3) pairState3 =
        .ok (.yield (), pairState4) := by trustIrReduce

private theorem pair_row4 :
    Sem.run (GenericCoro.Prefix.evalBodyStep pairRecurse pairActive 8 .abort
      pairRow4) pairState4 =
        .ok (.yield (), pairState5) := by trustIrReduce

private theorem pair_row5 :
    Sem.run (GenericCoro.Prefix.evalBodyStep pairRecurse pairActive 8 .abort
      pairRow5) pairState5 =
        .ok (.yield (), pairState6) := by trustIrReduce

private theorem pair_row6 :
    Sem.run (GenericCoro.Prefix.evalBodyStep pairRecurse pairActive 8 .abort
      pairRow6) pairState6 =
        .ok (.yield (), pairState7) := by trustIrReduce

private theorem pair_row7 :
    Sem.run (GenericCoro.Prefix.evalBodyStep pairRecurse pairActive 8 .abort
      pairRow7) pairState7 =
        .ok (.yield (), pairState8) := by trustIrReduce

private theorem pair_cons_run {recurse : GenericCoro.Prefix.Recurse} {ctx : EvalContext}
    {depth : Nat} {strat : PanicStrategy} {row : Inst × List ValueId}
    {rows : List (Inst × List ValueId)} {state next : MachineState}
    (first : Sem.run (GenericCoro.Prefix.evalBodyStep recurse ctx depth strat row) state =
      .ok (.yield (), next)) :
    Sem.run (GenericCoro.Prefix.evalBody recurse ctx depth strat (row :: rows)) state =
      Sem.run (GenericCoro.Prefix.evalBody recurse ctx depth strat rows) next := by
  unfold GenericCoro.Prefix.evalBody
  rw [List.forIn_cons, Sem.run_bind, first]
  rfl

private theorem pair_body_run :
    Sem.run (GenericCoro.Prefix.evalBody pairRecurse pairActive 8 .abort pairRows)
      MachineState.empty = .ok ((), pairState8) := by
  change Sem.run (GenericCoro.Prefix.evalBody pairRecurse pairActive 8 .abort pairRows)
    pairState0 = .ok ((), pairState8)
  unfold pairRows
  rw [pair_cons_run pair_row0, pair_cons_run pair_row1, pair_cons_run pair_row2,
    pair_cons_run pair_row3, pair_cons_run pair_row4, pair_cons_run pair_row5,
    pair_cons_run pair_row6, pair_cons_run pair_row7]
  rfl

private theorem pair_context_entry : pairContext.functions ⟨0⟩ = some pairView := by trustIrReduce
private theorem pair_entry_body : pairView.body =
    { paramTys := [], returnTys := [.U32], isVararg := false, abi := none } := by trustIrReduce
private theorem pair_context_depth : pairContext.maxCallDepth = 8 := by trustIrReduce
private def pairSourceBlock : BasicBlock :=
  (trustIrListGet? (pairEntry.blocks.toOption.get (by trustIrReduce)) 0).get (by trustIrReduce) |>.snd
private theorem pair_entry_cfg : pairView.cfg pairView.entryBlock = some pairSourceBlock := by trustIrReduce
private theorem pair_resolved_block : pairActive.resolveBlock pairSourceBlock = pairSourceBlock := by trustIrReduce

private theorem pair_application_composed :
    decodedRun itemModule = some (.ok [.int 32 12]) := by
  have empty_items (ctx : EvalContext) : checkFunctionItemValues ctx [] [] = .ok () := rfl
  have empty_poison : Sem.rejectPoisonValues [] "Call arguments" = pure () := rfl
  have noABI : requireUntypedAbi none = (pure () : Sem Unit) := rfl
  have noArity : checkCallArity [] [] = .ok () := rfl
  simp only [decodedRun, pair_context_ok, evalFunctionInContext, pair_context_entry,
    pair_entry_body, pair_context_depth, noABI, noArity,
    empty_items, empty_poison, pure_bind, exitUnwinding]
  rw [GenericCoro.Prefix.stepNWithContext_succ_layer]
  change some ((Sem.run (do
    let values ← GenericCoro.Prefix.evalLayer pairRecurse pairActive 8
      pairView.cfg pairView.entryBlock [] .abort
    Sem.rejectPoisonValues values "Call returns"
    let _ ← Sem.fromMemoryExcept (checkFunctionItemValues pairContext [.U32] values)
    pure values) MachineState.empty).map Prod.fst) = _
  simp only [GenericCoro.Prefix.evalLayer, pair_entry_cfg, pair_resolved_block]
  have params : pairSourceBlock.params = [] := by trustIrReduce
  have term : pairSourceBlock.terminator = .Return [⟨7⟩] := rfl
  simp only [params, term, List.map_nil, empty_items, pure_bind]
  have return_term (ctx : EvalContext) (depth : Nat) (cfg : CFG) :
      stepTermWithContext ctx depth cfg (.Return [⟨7⟩]) .abort = (do
        let values ← [⟨7⟩].mapM Sem.lookupValue
        pure (.terminator (.Ret values))) := by
    simp only [stepTermWithContext, closureTermWithContext, stepInst, semReturn, bind_assoc, pure_bind]
  have active_returns : pairActive.functionReturnTypes = some [.U32] := rfl
  have empty_bind : bindBlockParamsChecked [] [] = pure () := rfl
  have empty_sem : (Sem.fromMemoryExcept (.ok ()) : Sem Unit) = pure () := rfl
  simp only [return_term, bind_assoc, pure_bind, active_returns, empty_bind, empty_sem]
  have rows : bodyInstsWithResultDests pairSourceBlock.body pairSourceBlock.bodyResultDests = pairRows := rfl
  rw [rows, Sem.run_bind, pair_body_run]
  trustIrReduce

/-- Two zero-byte values of different nominal types survive tuple transport,
    typed monomorphic parameters and indirect application. -/
theorem decoded_pair_application :
    decodedRun itemModule = some (.ok [.int 32 12]) := by
  trustIrCompilerProof { rfl } { exact pair_application_composed }

private def entryWith (body : List Inst) (dests : List (List ValueId))
    (returns : List ValueId) : TrustIrEval.Function :=
  { pairEntry with blocks := .ok [(⟨0⟩,
      { params := [], body, bodyResultDests := dests,
        terminator := .Return returns })] }

private def singleEntryModule (entry : TrustIrEval.Function) : TrustIrEval.Module :=
  { itemModule with functions := [entry, target ⟨53⟩ 2, target ⟨11⟩ 1] }

private def isTypeError : Option (Except SemError (List Value)) → Bool
  | some (.error (.typeError _)) => true
  | _ => false

private def isUB : Option (Except SemError (List Value)) → Bool
  | some (.error (.ub _)) => true
  | _ => false

private def simpleCall (sig : FuncTyId) (conv : CallingConv) : TrustIrEval.Function :=
  entryWith [.Const (.FnItem ⟨11⟩) (.fnItem ⟨11⟩),
    .CallIndirect ⟨0⟩ sig [] conv] [[⟨0⟩], [⟨1⟩]] [⟨1⟩]

theorem decoded_signature_identity_refuses :
    isTypeError (decodedRun (singleEntryModule (simpleCall ⟨3⟩ .C))) = true := by trustIrReduce

theorem decoded_calling_convention_refuses :
    isTypeError (decodedRun (singleEntryModule (simpleCall ⟨0⟩ .Rust))) = true := by trustIrReduce

theorem decoded_forged_constant_refuses :
    isTypeError (decodedRun (singleEntryModule
      (entryWith [.Const (.FnItem ⟨11⟩) (.fnItem ⟨53⟩)] [[⟨0⟩]] []))) = true := by rfl

theorem decoded_missing_header_refuses :
    isTypeError (decodedRun { itemModule with
      functions := [simpleCall ⟨0⟩ .C, target ⟨53⟩ 2] }) = true := by rfl

theorem decoded_duplicate_header_refuses :
    isTypeError (decodedRun { itemModule with
      functions := [simpleCall ⟨0⟩ .C, target ⟨11⟩ 1, target ⟨11⟩ 1] }) = true := by rfl

/-- An explicit zero-byte cast reconstructs the destination singleton. -/
theorem decoded_cross_item_cast :
    decodedRun (singleEntryModule (entryWith
      [.Const (.FnItem ⟨11⟩) (.fnItem ⟨11⟩),
       .Cast .Transmute (.FnItem ⟨11⟩) (.FnItem ⟨53⟩) ⟨0⟩,
       .CallIndirect ⟨1⟩ ⟨0⟩ [] .C]
      [[⟨0⟩], [⟨1⟩], [⟨2⟩]] [⟨2⟩])) = some (.ok [.int 32 2]) := by trustIrReduce

/-- Reifying the same authenticated IR row keeps the existing pointer call
    contract; source shim selection is a separate producer obligation. -/
theorem decoded_same_row_reification :
    decodedRun (singleEntryModule (entryWith
      [.Const (.FnItem ⟨11⟩) (.fnItem ⟨11⟩),
       .Cast .ReifyFnPointer (.FnItem ⟨11⟩) (.Func ⟨0⟩) ⟨0⟩,
       .CallIndirect ⟨1⟩ ⟨0⟩ [] .C]
      [[⟨0⟩], [⟨1⟩], [⟨2⟩]] [⟨2⟩])) = some (.ok [.int 32 1]) := by trustIrReduce

/-- A valid zero-byte memory image reconstructs its declared item. -/
theorem decoded_zero_byte_load :
    decodedRun (singleEntryModule (entryWith
      [.Alloca (.FnItem ⟨11⟩) none none,
       .Load (.FnItem ⟨11⟩) ⟨0⟩ false none,
       .CallIndirect ⟨1⟩ ⟨0⟩ [] .C]
      [[⟨0⟩], [⟨1⟩], [⟨2⟩]] [⟨2⟩])) = some (.ok [.int 32 1]) := by trustIrReduce

/-- Scalar Undef remains immediately undefined behavior even when its result
    is unused; zero-byte image decoding does not authorize this instruction. -/
theorem decoded_unused_undef_is_ub :
    isUB (decodedRun (singleEntryModule
      (entryWith [.Undef (.FnItem ⟨11⟩)] [[⟨0⟩]] []))) = true := by rfl

theorem decoded_inspected_undef_is_ub :
    isUB (decodedRun (singleEntryModule
      (entryWith [.Undef (.FnItem ⟨11⟩), .CallIndirect ⟨0⟩ ⟨0⟩ [] .C]
        [[⟨0⟩], [⟨1⟩]] [⟨1⟩]))) = true := by rfl

private def argumentModule (ty : Ty) (rows : FunctionItemPresence.Source := {}) :
    TrustIrEval.Module :=
  { itemModule with
    functions := [
      { pairEntry with ty := ⟨4⟩, blocks := .ok [(⟨0⟩,
          { params := [(⟨0⟩, ty)], body := [.Const .U32 (.int 9)],
            bodyResultDests := [[⟨1⟩]], terminator := .Return [⟨1⟩] })] },
      target ⟨11⟩ 1, target ⟨53⟩ 2],
    funcTys := itemModule.funcTys ++ [{ signature with params := [ty] }],
    types := rows.types, structs := rows.structs, enums := rows.enums,
    records := rows.records, closureTys := rows.closures }

/-- The expected source fields cannot disappear from a malformed boundary
    value even when the entry body never inspects its argument. -/
theorem decoded_missing_tuple_item_refuses :
    isTypeError (decodedRun (argumentModule (.Tuple [.FnItem ⟨11⟩]))
      [.aggregate []]) = true := by trustIrReduce

theorem decoded_nested_missing_tuple_item_refuses :
    isTypeError (decodedRun (argumentModule (.Tuple [.Tuple [.FnItem ⟨11⟩]]))
      [.aggregate [.aggregate []]]) = true := by trustIrReduce

/-- A declared unwritten field is retained as a transport marker. -/
theorem decoded_matching_unwritten_item_transports :
    decodedRun (argumentModule (.Tuple [.FnItem ⟨11⟩]))
      [.aggregate [.uninit]] = some (.ok [.int 32 9]) := by trustIrReduce

private def recordRows : FunctionItemPresence.Source :=
  { records := [(⟨0⟩, some
      { id := ⟨0⟩, name := "Pair", fields :=
        [{ name := "unit", ty := .Unit, offset := none },
         { name := "held", ty := .FnItem ⟨11⟩, offset := none }] })] }

theorem decoded_duplicate_record_label_cannot_hide_item :
    isTypeError (decodedRun (argumentModule (.Record ⟨0⟩) recordRows)
      [.record [("unit", .aggregate []), ("unit", .aggregate [])]]) = true := by trustIrReduce

theorem decoded_declared_record_item_transports :
    decodedRun (argumentModule (.Record ⟨0⟩) recordRows)
      [.record [("unit", .aggregate []), ("held", .fnItem ⟨11⟩)]] =
      some (.ok [.int 32 9]) := by trustIrReduce

private def hugeType : Ty := .Array ⟨0⟩ (2 ^ 40)

private def hugeModule : TrustIrEval.Module :=
  { singleEntryModule (entryWith
      [.Alloca hugeType none none,
       .Load hugeType ⟨0⟩ false none,
       .Const .U64 (.int (2 ^ 40 - 1)),
       .ExtractElement (.FnItem ⟨11⟩) ⟨1⟩ ⟨2⟩,
       .CallIndirect ⟨3⟩ ⟨0⟩ [] .C]
      [[⟨0⟩], [⟨1⟩], [⟨2⟩], [⟨3⟩], [⟨4⟩]] [⟨4⟩]) with
      types := [some (.FnItem ⟨11⟩)] }

private def hugeSource : SourceLayout.Environment :=
  { model := .le64, canonicalScalars := true,
    hasTargetInfo := hugeModule.hasTargetInfo,
    types := hugeModule.types, structs := hugeModule.structs, enums := hugeModule.enums,
    records := hugeModule.records.filterMap (·.2), closures := hugeModule.closureTys,
    tupleLayouts := hugeModule.tupleLayouts, closureLayouts := hugeModule.closureLayouts,
    functions := hugeModule.functions.map (fun function => (function.id, function.ty)),
    funcTypes := hugeModule.funcTys }

private def hugePlan : AggregateMemory.Plan :=
  .array hugeType ⟨0, 1⟩ (2 ^ 40) (.fnItem ⟨11⟩ ⟨0, 1⟩)

private def hugeService : AggregateMemory.Service :=
  AggregateMemory.prepare hugeSource [hugeType, hugeType]

/-- Project only a genuinely successful assembly of the original module. -/
private def hugeBaseContext : EvalContext :=
  (TrustIrEval.contextOf hugeModule 8).toOption.get (by rfl)

private theorem huge_context_ok :
    TrustIrEval.contextOf hugeModule 8 = .ok hugeBaseContext := by rfl

private def hugeEntryView : EvalFunction :=
  (hugeBaseContext.functions ⟨0⟩).get (by rfl)

private theorem huge_entry_present :
    hugeBaseContext.functions ⟨0⟩ = some hugeEntryView := by rfl

private theorem huge_entry_returns : hugeEntryView.body.returnTys = [.U32] := by rfl

private theorem huge_entry_body :
    hugeEntryView.body =
      { paramTys := [], returnTys := [.U32], isVararg := false, abi := none } := by rfl

private def hugeSourceEntry : TrustIrEval.Function :=
  (trustIrListGet? hugeModule.functions 0).get (by trustIrReduce)

private def hugeSourceBlock : BasicBlock :=
  (trustIrListGet? (hugeSourceEntry.blocks.toOption.get (by trustIrReduce)) 0).get (by trustIrReduce) |>.snd

private theorem huge_entry_cfg :
    hugeEntryView.cfg hugeEntryView.entryBlock = some hugeSourceBlock := by trustIrReduce

private theorem huge_context_budget : hugeBaseContext.maxCallDepth = 8 := by rfl

private def hugeContextUsing (service : AggregateMemory.Service) : EvalContext :=
  { hugeBaseContext with memoryService := some service }

private theorem huge_context_entry (service : AggregateMemory.Service) :
    (hugeContextUsing service).functions ⟨0⟩ = some hugeEntryView := by
  change hugeBaseContext.functions ⟨0⟩ = some hugeEntryView
  exact huge_entry_present

private theorem huge_context_depth (service : AggregateMemory.Service) :
    (hugeContextUsing service).maxCallDepth = 8 := by
  change hugeBaseContext.maxCallDepth = 8
  exact huge_context_budget

private def hugeRunUsing (service : AggregateMemory.Service) :
    Option (Except SemError (List Value)) :=
  some ((Sem.run (evalFunctionInContext (hugeContextUsing service) ⟨0⟩ [] 8)
    MachineState.empty).map Prod.fst)

private theorem huge_resolved_block (service : AggregateMemory.Service) :
    ((hugeContextUsing service).forFunction hugeEntryView).resolveBlock hugeSourceBlock =
      hugeSourceBlock := by trustIrReduce

/-- This service comes from the unchanged decoded module's two memory roots. -/
private theorem huge_context_service :
    (TrustIrEval.contextOf hugeModule 8).map (·.memoryService) =
      .ok (some hugeService) := by
  simp only [TrustIrEval.contextOf, TrustIrEval.memoryServiceOf_eq]
  rfl

private theorem huge_source_layout :
    SourceLayout.query hugeSource .execution hugeType =
      .ok { size := 0, align := some 1 } := by
  simp only [hugeSource, hugeModule, singleEntryModule, itemModule, entryWith,
    pairEntry, target, applyItem, hugeType]
  item_source_compute

macro "huge_service_compute" : tactic =>
  `(tactic| trustIrCompilerProof {
    simp only [hugeService, hugePlan, hugeType, AggregateMemory.prepare,
    AggregateMemory.Service.query, AggregateMemory.Service.queryLayout,
    AggregateMemory.Service.queryLayoutWithWork, AggregateMemory.Service.model,
    AggregateMemory.runCompile_eq,
    AggregateMemory.compile_array, AggregateMemory.compile_fnItem,
    AggregateMemory.summary_eq, SourceLayout.prepare, SourceLayout.Session.query,
    compileTy_array, compileTy_fnItem,
    List.forIn, List.forIn.loop, List.length, List.range, List.range.loop,
    ForIn.forIn, List.instForIn, Bind.bind, Pure.pure, Id.instMonad, Id.run,
    StateT.instMonad, StateT.bind, StateT.pure]
    rfl
  } {
    simp only [hugeService, hugePlan, hugeType, AggregateMemory.prepare,
      AggregateMemory.Service.query, AggregateMemory.Service.queryLayout,
      AggregateMemory.Service.queryLayoutWithWork, AggregateMemory.Service.model,
      AggregateMemory.runCompile_eq,
      AggregateMemory.compile_array, AggregateMemory.compile_fnItem,
      AggregateMemory.summary_eq, SourceLayout.prepare, SourceLayout.Session.query,
      compileTy_array, compileTy_fnItem] <;> trustIrReduce
  })

private theorem huge_service_plan :
    hugeService.query hugeType = .ok hugePlan := by huge_service_compute

private theorem huge_service_layout :
    hugeService.queryLayout hugeType = .ok ⟨0, 1⟩ := by huge_service_compute

private theorem huge_service_model :
    hugeService.model = .le64 := by huge_service_compute

private theorem huge_context_using_self :
    hugeContextUsing hugeService = hugeBaseContext := by
  have service := huge_context_service
  rw [huge_context_ok] at service
  have same : hugeBaseContext.memoryService = some hugeService := Except.ok.inj service
  unfold hugeContextUsing
  rw [← same]

private theorem decoded_huge_service :
    decodedRun hugeModule = hugeRunUsing hugeService := by
  simp only [decodedRun, hugeRunUsing, huge_context_ok, huge_context_using_self]


/-- Closed operational checkpoints preserve the actual allocation and declarations. -/
private def hugeAllocation : Sem ValueId :=
  semAllocaUsing (fun _ => .ok ⟨0, 1⟩) unknownIntegerOperand hugeType none none .le64
private def hugeAllocated : ValueId × MachineState :=
  (Sem.run hugeAllocation MachineState.empty).toOption.get (by rfl)
private theorem huge_allocation_run :
    Sem.run hugeAllocation MachineState.empty = .ok hugeAllocated := rfl
private theorem huge_allocated_id : hugeAllocated.1 = ⟨0⟩ := rfl
private def hugeAllocationPublication : Sem Unit :=
  (hugeBaseContext.forFunction hugeEntryView).bindInstructionResults
    (.Alloca hugeType none none) (.value (some ⟨0⟩)) [⟨0⟩]
private def hugePublished : Unit × MachineState :=
  (Sem.run hugeAllocationPublication hugeAllocated.2).toOption.get (by trustIrReduce)
private theorem huge_publication_run :
    Sem.run hugeAllocationPublication hugeAllocated.2 = .ok hugePublished := by trustIrReduce
private theorem huge_publication_using (service : AggregateMemory.Service) :
    ((hugeContextUsing service).forFunction hugeEntryView).bindInstructionResults
      (.Alloca hugeType none none) (.value (some ⟨0⟩)) [⟨0⟩] =
        hugeAllocationPublication := rfl
private def hugeFetched : Value × MachineState :=
  (Sem.run (Sem.lookupValue ⟨0⟩) hugePublished.2).toOption.get (by trustIrReduce)
private theorem huge_fetch_run :
    Sem.run (Sem.lookupValue ⟨0⟩) hugePublished.2 = .ok hugeFetched := by trustIrReduce
private theorem huge_fetched_pointer : hugeFetched.1 = .ptr 1024 (some ⟨0⟩) := by trustIrReduce
private theorem huge_fetched_state : hugeFetched.2 = hugePublished.2 := by trustIrReduce
private theorem huge_safety_run :
    Sem.run (Sem.checkedAccess "Load" 1024 ⟨0⟩ 0 1 .le64) hugePublished.2 =
      .ok (1024, hugePublished.2) := by trustIrReduce
private theorem huge_empty_image :
    hugePublished.2.memory.readImage 1024 0 = ByteImage.empty := by trustIrReduce
private def hugeHeld : Value :=
  .array (CompactArray.Packed.uniform (2 ^ 40) (.fnItem ⟨11⟩))
private def hugeLoaded : ValueId × MachineState :=
  (Sem.run (Sem.bindFresh hugeHeld) hugePublished.2).toOption.get (by rfl)
private theorem huge_loaded_run :
    Sem.run (Sem.bindFresh hugeHeld) hugePublished.2 = .ok hugeLoaded := rfl
private theorem huge_loaded_id : hugeLoaded.1 = ⟨1⟩ := by trustIrReduce
private def hugeLoadPublication : Sem Unit :=
  (hugeBaseContext.forFunction hugeEntryView).bindInstructionResults
    (.Load hugeType ⟨0⟩ false none) (.value (some ⟨1⟩)) [⟨1⟩]
private def hugeLoadBound : Unit × MachineState :=
  (Sem.run hugeLoadPublication hugeLoaded.2).toOption.get (by trustIrReduce)
private theorem huge_load_publication_run :
    Sem.run hugeLoadPublication hugeLoaded.2 = .ok hugeLoadBound := by trustIrReduce
private theorem huge_load_publication_using (service : AggregateMemory.Service) :
    ((hugeContextUsing service).forFunction hugeEntryView).bindInstructionResults
      (.Load hugeType ⟨0⟩ false none) (.value (some ⟨1⟩)) [⟨1⟩] =
        hugeLoadPublication := rfl

private theorem huge_decode_value (order : FunctionAddressOrder) (memory : Memory) :
    AggregateMemory.decode .le64 order memory hugePlan ByteImage.empty = .ok hugeHeld := by
  change AggregateMemory.decode .le64 order memory
    (.array (.Array ⟨0⟩ (2 ^ 40)) ⟨0, 1⟩ (2 ^ 40) (.fnItem ⟨11⟩ ⟨0, 1⟩))
    ByteImage.empty = .ok hugeHeld
  rw [AggregateMemory.decode_fnItem_array]
  rfl

private theorem huge_held_load (service : AggregateMemory.Service)
    (model : service.model = .le64)
    (plan : service.query hugeType = .ok hugePlan) (order : FunctionAddressOrder) :
    Sem.run (AggregateMemory.loadValue service order hugeType hugeFetched.1 false none .le64)
      hugePublished.2 = .ok (hugeHeld, hugePublished.2) := by
  rw [AggregateMemory.loadValue_run_empty service order hugeType hugePlan hugeFetched.1
    hugePublished.2 1024 ⟨0⟩ .le64 model.symm plan (by rfl)
    huge_fetched_pointer huge_safety_run huge_empty_image]
  rw [huge_decode_value]
  rfl

private theorem huge_load_run (service : AggregateMemory.Service)
    (model : service.model = .le64)
    (plan : service.query hugeType = .ok hugePlan) (order : FunctionAddressOrder) :
    Sem.run (AggregateMemory.load service order hugeType ⟨0⟩ false none .le64) hugePublished.2 =
      .ok hugeLoaded := by
  unfold AggregateMemory.load
  rw [Sem.run_bind, huge_fetch_run]
  simp only [Except.bind]
  rw [huge_fetched_state, Sem.run_bind, huge_held_load service model plan]
  simp only [Except.bind]
  exact huge_loaded_run

private theorem huge_run_using (service : AggregateMemory.Service)
    (model : service.model = .le64)
    (plan : service.query hugeType = .ok hugePlan)
    (layout : service.queryLayout hugeType = .ok ⟨0, 1⟩) :
    hugeRunUsing service = some (.ok [.int 32 1]) := by
  have empty_items (ctx : EvalContext) :
      checkFunctionItemValues ctx [] [] = .ok () := rfl
  have empty_poison : Sem.rejectPoisonValues [] "Call arguments" = pure () := rfl
  have noABI : requireUntypedAbi none = (pure () : Sem Unit) := rfl
  have noArity : checkCallArity [] [] = .ok () := rfl
  simp only [hugeRunUsing, evalFunctionInContext, huge_context_entry,
    huge_entry_body, huge_context_depth, noABI, noArity,
    empty_items, empty_poison, pure_bind, exitUnwinding]
  rw [GenericCoro.Prefix.stepNWithContext_succ_layer]
  simp only [GenericCoro.Prefix.evalLayer, huge_entry_cfg, huge_resolved_block, empty_items]
  have params : hugeSourceBlock.params = [] := by trustIrReduce
  have term : hugeSourceBlock.terminator = .Return [⟨4⟩] := rfl
  simp only [params, term, List.map_nil, empty_items, pure_bind]
  have return_term (ctx : EvalContext) (depth : Nat) (cfg : CFG) :
      stepTermWithContext ctx depth cfg (.Return [⟨4⟩]) .abort = (do
        let values ← [⟨4⟩].mapM Sem.lookupValue
        pure (.terminator (.Ret values))) := by
    simp only [stepTermWithContext, closureTermWithContext, stepInst, semReturn, bind_assoc, pure_bind]
  have active_returns : ((hugeContextUsing service).forFunction hugeEntryView).functionReturnTypes =
      some [.U32] := rfl
  have empty_bind : bindBlockParamsChecked [] [] = pure () := rfl
  have empty_sem : (Sem.fromMemoryExcept (.ok ()) : Sem Unit) = pure () := rfl
  simp only [return_term, bind_assoc, pure_bind, active_returns, empty_bind, empty_sem]
  have rows : bodyInstsWithResultDests hugeSourceBlock.body hugeSourceBlock.bodyResultDests =
      [(.Alloca hugeType none none, [⟨0⟩]),
       (.Load hugeType ⟨0⟩ false none, [⟨1⟩]),
       (.Const .U64 (.int (2 ^ 40 - 1)), [⟨2⟩]),
       (.ExtractElement (.FnItem ⟨11⟩) ⟨1⟩ ⟨2⟩, [⟨3⟩]),
       (.CallIndirect ⟨3⟩ ⟨0⟩ [] .C, [⟨4⟩])] := rfl
  have alloca_step (recurse : GenericCoro.Prefix.Recurse) (ctx : EvalContext)
      (depth : Nat) (ty : Ty) (count : Option ValueId) (alignment : Option Nat)
      (dests : List ValueId) :
      GenericCoro.Prefix.evalBodyStep recurse ctx depth .abort
        (.Alloca ty count alignment, dests) = (do
          let id ← semAllocaUsing ctx.memoryLayout ctx.carrierIntegerOperand
            ty count alignment ctx.byteModel
          ctx.bindInstructionResults (.Alloca ty count alignment) (.value (some id)) dests
          pure (.yield ())) := by
    simp only [GenericCoro.Prefix.evalBodyStep, stepInstWithContext, bind_assoc, pure_bind]
  have active_layout :
      ((hugeContextUsing service).forFunction hugeEntryView).memoryLayout hugeType = .ok ⟨0, 1⟩ := by
    change AggregateMemory.layoutQuery service .le64 hugeType = .ok ⟨0, 1⟩
    unfold AggregateMemory.layoutQuery
    rw [model]
    exact layout
  rw [rows]
  unfold GenericCoro.Prefix.evalBody
  rw [List.forIn_cons]
  simp only [alloca_step, bind_assoc, pure_bind]
  have active_model :
      ((hugeContextUsing service).forFunction hugeEntryView).byteModel = .le64 := rfl
  have zero_alloca (query : MemoryLayoutQuery) (reader : IntegerOperandReader) (ty : Ty)
      (geometry : query ty = .ok ⟨0, 1⟩) :
      semAllocaUsing query reader ty none none .le64 =
        semAllocaUsing (fun _ => .ok ⟨0, 1⟩) unknownIntegerOperand ty none none .le64 := by
    simp only [semAllocaUsing, semAllocateUsing, geometry, pure_bind]
  rw [active_model, zero_alloca _ _ _ active_layout]
  have allocation_run := huge_allocation_run
  unfold hugeAllocation at allocation_run
  rw [Sem.run_bind, allocation_run]
  simp only [Except.bind]
  rw [huge_allocated_id, huge_publication_using, Sem.run_bind, huge_publication_run]
  simp only [Except.bind, pure_bind]
  have load_step (recurse : GenericCoro.Prefix.Recurse) (ctx : EvalContext)
      (depth : Nat) (ty : Ty) (pointer : ValueId) (strict : Bool) (alignment : Option Nat)
      (dests : List ValueId) (chosen : ctx.memoryServiceFor ty = some service) :
      GenericCoro.Prefix.evalBodyStep recurse ctx depth .abort
        (.Load ty pointer strict alignment, dests) = (do
          let id ← AggregateMemory.load service ctx.functionOrder ty pointer strict alignment ctx.byteModel
          ctx.bindInstructionResults (.Load ty pointer strict alignment) (.value (some id)) dests
          pure (.yield ())) := by
    simp only [GenericCoro.Prefix.evalBodyStep, stepInstWithContext, chosen, bind_assoc, pure_bind]
  have active_service :
      ((hugeContextUsing service).forFunction hugeEntryView).memoryServiceFor hugeType =
        some service := rfl
  rw [List.forIn_cons]
  simp only [load_step _ _ _ _ _ _ _ _ active_service, bind_assoc, pure_bind, active_model]
  rw [Sem.run_bind, huge_load_run service model plan]
  simp only [Except.bind]
  rw [huge_loaded_id, huge_load_publication_using, Sem.run_bind, huge_load_publication_run]
  simp only [Except.bind, pure_bind]
  trustIrReduce

/-- The logical length is not expanded during allocation, decoding or the
    last-element projection of a uniform zero-byte array. -/
theorem decoded_huge_zero_byte_array :
    decodedRun hugeModule = some (.ok [.int 32 1]) := by
  rw [decoded_huge_service]
  exact huge_run_using hugeService huge_service_model huge_service_plan huge_service_layout


end TrustIr.FunctionItemProps

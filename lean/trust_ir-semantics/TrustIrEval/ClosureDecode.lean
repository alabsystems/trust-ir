-- Copyright 2026 Andrew Yates | Apache-2.0
-- Total, bounded proof-input decoder for the canonical logical closure slice.
-- The general native oracle decoder remains unchanged except map API support.
-- This is no source-refinement, runtime/ABI, machine or admission certificate.
import TrustIrEval.Decode
import TrustIr.DecodedContext

namespace TrustIrEval.ClosureDecode
open Lean TrustIr

def tyFuel : Nat → Json → D Ty
  | 0, _ => unsupported "closure_subset.type_depth"
  | fuel + 1, j => do
    let (tag, p) ← tagged "Ty" j
    match tag with
    | "I8" => pure .I8
    | "I16" => pure .I16
    | "I32" => pure .I32
    | "I64" => pure .I64
    | "I128" => pure .I128
    | "U8" => pure .U8
    | "U16" => pure .U16
    | "U32" => pure .U32
    | "U64" => pure .U64
    | "U128" => pure .U128
    | "Isize" => pure .Isize
    | "Usize" => pure .Usize
    | "Char" => pure .Char
    | "Error" => pure .Error
    | "F16" => pure .F16
    | "F32" => pure .F32
    | "F64" => pure .F64
    | "Bool" => pure .Bool
    | "Ptr" => pure .Ptr
    | "FatPtr" => pure (.FatPtr (← fatPtrKind p))
    | "Struct" => pure (.Struct ⟨← nat "Struct" p⟩)
    | "Array" =>
      let (e, n) ← pair "Array" p
      pure (.Array ⟨← nat "Array.elem" e⟩ (← nat "Array.len" n))
    | "Func" => pure (.Func ⟨← nat "Func" p⟩)
    | "Unit" => pure .Unit
    | "Never" => pure .Never
    | "Tuple" => pure (.Tuple (← (← arr "Tuple" p).mapM (tyFuel fuel)))
    | "Enum" => pure (.Enum ⟨← nat "Enum" p⟩)
    | "Vector" =>
      -- Rust `Vector(Box<Ty>, u32)` is (elem, lanes); Lean is `Vector lanes elem`.
      let (e, n) ← pair "Vector" p
      pure (.Vector (← nat "Vector.lanes" n) (← tyFuel fuel e))
    | "Ref" => pure (.Ref (← tyFuel fuel p))
    | "RefMut" => pure (.RefMut (← tyFuel fuel p))
    | "PtrConst" => pure (.PtrConst (← tyFuel fuel p))
    | "PtrMut" => pure (.PtrMut (← tyFuel fuel p))
    | "Rc" => pure (.Rc (← tyFuel fuel p))
    | "Set" =>
      let (e, r) ← pair "Set" p
      pure (.Set ⟨← nat "Set.elem" e⟩ (← setRepr r))
    | "Sequence" => pure (.Sequence ⟨← nat "Sequence" p⟩)
    | "Record" => pure (.Record ⟨← nat "Record" p⟩)
    | "Closure" => pure (.Closure ⟨← nat "Closure" p⟩)
    | "Refine" =>
      let (b, q) ← pair "Refine" p
      pure (.Refine ⟨← nat "Refine.base" b⟩ ⟨← nat "Refine.pred" q⟩)
    | "Dialect" =>
      pure (.Dialect (← strField p "namespace") (← strField p "name")
        (← natField p "version").toUInt32)
    | "Handle" => pure (.Handle (← strField p "name") (← strField p "runtime"))
    | other => unsupported s!"ty.{other}"

def ty (j : Json) : D Ty := tyFuel 64 j

def tyList (j : Json) : D (List Ty) := do (← arr "types" j).mapM ty

def inst (j : Json) : D Inst := do
  let (tag, p) ← tagged "Inst" j
  let v := fun k => do valueId k (← field p k)
  let vs := fun k => do valueIds k (← field p k)
  match tag with
  | "BinOp" => pure (.BinOp (← binOp (← field p "op"))
      (← ty (← field p "ty")) (← v "lhs") (← v "rhs"))
  | "Call" => pure (.Call (← funcId "callee" (← field p "callee")) (← vs "args"))
  | "CallIndirect" => pure (.CallIndirect (← v "callee") ⟨← natField p "sig"⟩
      (← vs "args") (← callingConv (← field p "calling_conv")))
  | "MakeClosure" => pure (.MakeClosure ⟨← natField p "ty"⟩
      (← funcId "func" (← field p "func")) (← vs "captures"))
  | "Return" => pure (.Return (← vs "values"))
  | other => unsupported s!"closure_subset.inst.{other}"

def node (j : Json) : D Node := do
  pure { inst := ← inst (← field j "inst"), results := ← valueIds "results" (← field j "results") }

def block (j : Json) : D (BlockId × BasicBlock) := do
  let id ← blockId "id" (← field j "id")
  let params ← (← listField j "params").mapM (fun pj => do
    let (vid, tj) ← pair "params" pj
    pure (← valueId "param" vid, ← ty tj))
  let nodes ← (← listField j "body").mapM node
  match nodes.reverse with
  | [] => malformed s!"block {id.index}: empty body"
  | term :: reversed =>
    if !term.inst.isTerminator then
      malformed s!"block {id.index}: last node is not a terminator"
    else
      let body := reversed.reverse
      pure (id, { params := params
                  body := body.map (·.inst)
                  bodyResultDests := body.map (·.results)
                  terminator := term.inst
                  terminatorResultDests := term.results })

def function (j : Json) : D Function := do
  let rows ← listField j "blocks"
  pure { id := ← funcId "id" (← field j "id")
         name := ← strField j "name"
         ty := ⟨← natField j "ty"⟩
         entry := ← blockId "entry" (← field j "entry")
         isDeclaration := rows.isEmpty
         callingConvention := ← callingConv (← field j "calling_conv")
         blocks := rows.mapM block }

def funcTy (j : Json) : D FuncTyDef := do
  abiFields "FuncTy" j ["params", "returns", "is_vararg", "abi"]
  match j.getObjVal? "abi" with
  | .ok value => if !value.isNull then unsupported "signature_abi.transport_semantics"
  | .error _ => pure ()
  pure { params := ← tyList (← field j "params")
         returns := ← tyList (← field j "returns")
         isVararg := ← boolField j "is_vararg"
         abi := none }

/-- This slice has no memory, aggregate, destructor or global semantics.
    A nonempty unsupported table is refused, never replaced by an empty table. -/
def requireEmpty (j : Json) (key : String) (optionalField : Bool := false) : D Unit := do
  match j.getObjVal? key with
  | .error _ => if optionalField then pure () else malformed s!"missing {key}"
  | .ok value => if (← arr key value).isEmpty then pure () else unsupported s!"closure_subset.table.{key}"

/-- The proof-input slice is explicitly 64-bit. Other targets refuse rather
    than acquire a scalar/closure ABI assumption through a platform label. -/
def byteModel (j : Json) : D ByteModel := do
  match j.getObjVal? "target_info" with
  | .error _ | .ok .null => pure .le64
  | .ok target =>
    let bytes ← natField target "pointer_size"
    let endian ← strField target "endianness"
    if bytes = 8 ∧ endian = "Little" then pure .le64
    else unsupported "closure_subset.target.byte_model"

def module (j : Json) : D Module := do
  requireEmpty j "globals"
  requireEmpty j "enums"
  requireEmpty j "structs"
  for key in ["records", "tuple_layouts", "closure_layouts", "drop_glue"] do
    requireEmpty j key true
  pure { byteModel := byteModel j
         hasTargetInfo := match j.getObjVal? "target_info" with
           | .error _ | .ok .null => false | .ok _ => true
         functions := ← (← listField j "functions").mapM function
         funcTys := ← (← listField j "func_types").mapM funcTy
         closureTys := ← (← listField j "closure_types").mapM (fun row => do
           pure { func := ⟨← natField row "func"⟩
                  captures := ← tyList (← field row "captures") })
         globals := []
         enums := []
         structs := []
         types := (← tyList (← field j "types")).map some }

end TrustIrEval.ClosureDecode

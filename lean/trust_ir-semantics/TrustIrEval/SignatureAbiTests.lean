-- Copyright 2026 Andrew Yates | Author: Andrew Yates | Apache-2.0
-- Decoder and refusal regression checks; these do not prove ABI transport.
-- Run with the repository's pinned Lean: lake env lean --run TrustIrEval/SignatureAbiTests.lean
import TrustIrRuntime
import TrustIrEval.Run

open Lean (Json toJson)
open TrustIr TrustIrEval

private def attrs : AbiAttributes :=
  { extension := .Sign, inReg := true, noAlias := false, nonnull := true
    readonly := false, noUndef := true, writable := true, noFree := false
    capture := .Address, pointeeSize := 18446744073709551615, pointeeAlign := some 16 }
private def reg : AbiRegister := { regClass := .Integer, bytes := 8 }
private def scalar : AbiScalar :=
  { register := reg, sourceOffset := 3, sourceBytes := 5, valueBits := 13, attributes := attrs }
private def uniform : AbiUniform := { unit := reg, total := 17, consecutive := true }
private def binding : AbiBinding :=
  { place := .Parameter 7, sourceOffset := 5, sourceBytes := 11
    carrierOffset := 13, carrierBytes := 17 }
private def modes : List AbiPassMode :=
  [.Ignore, .Direct scalar, .Pair scalar scalar, .Cast true [reg] (some 11) uniform attrs,
   .Indirect attrs (some attrs) true false]
private def argument (mode : AbiPassMode) : AbiArgument :=
  { size := 32, align := 16, mode := mode, bindings := [binding] }
private def expected : SignatureAbi :=
  { target := { triple := "aarch64-apple-darwin", dataLayout := "e-p:64:64", abi := "darwinpcs"
                cpu := "apple-m5", features := ["+neon", "+fp-armv8"], targetSpec := "sha256:fixture"
                pointerBytes := 8, littleEndian := true }
    frontend := { name := "Trust", revision := "test-revision" }
    convention := "Aapcs", loweredConvention := .Aapcs, sourceAbi := "C"
    canUnwind := false, variadic := true, fixedCount := 4
    arguments := modes.map argument, result := argument (.Indirect attrs (some attrs) true false) }

private def fixture : String := r##"{"target":{"triple":"aarch64-apple-darwin","data_layout":"e-p:64:64","abi":"darwinpcs","cpu":"apple-m5","features":["+neon","+fp-armv8"],"target_spec":"sha256:fixture","pointer_bytes":8,"little_endian":true},"frontend":{"name":"Trust","revision":"test-revision"},"convention":"Aapcs","lowered_convention":"Aapcs","source_abi":"C","can_unwind":false,"variadic":true,"fixed_count":4,"arguments":[{"size":32,"align":16,"mode":"Ignore","bindings":[{"place":{"Parameter":7},"source_offset":5,"source_bytes":11,"carrier_offset":13,"carrier_bytes":17}]},{"size":32,"align":16,"mode":{"Direct":{"register":{"bytes":8,"class":"Integer"},"source_offset":3,"source_bytes":5,"value_bits":13,"attributes":{"extension":"Sign","in_reg":true,"no_alias":false,"nonnull":true,"readonly":false,"no_undef":true,"writable":true,"no_free":false,"capture":"Address","pointee_size":18446744073709551615,"pointee_align":16}}},"bindings":[{"place":{"Parameter":7},"source_offset":5,"source_bytes":11,"carrier_offset":13,"carrier_bytes":17}]},{"size":32,"align":16,"mode":{"Pair":[{"register":{"bytes":8,"class":"Integer"},"source_offset":3,"source_bytes":5,"value_bits":13,"attributes":{"extension":"Sign","in_reg":true,"no_alias":false,"nonnull":true,"readonly":false,"no_undef":true,"writable":true,"no_free":false,"capture":"Address","pointee_size":18446744073709551615,"pointee_align":16}},{"register":{"bytes":8,"class":"Integer"},"source_offset":3,"source_bytes":5,"value_bits":13,"attributes":{"extension":"Sign","in_reg":true,"no_alias":false,"nonnull":true,"readonly":false,"no_undef":true,"writable":true,"no_free":false,"capture":"Address","pointee_size":18446744073709551615,"pointee_align":16}}]},"bindings":[{"place":{"Parameter":7},"source_offset":5,"source_bytes":11,"carrier_offset":13,"carrier_bytes":17}]},{"size":32,"align":16,"mode":{"Cast":{"pad_i32":true,"prefix":[{"bytes":8,"class":"Integer"}],"rest_offset":11,"rest":{"unit":{"bytes":8,"class":"Integer"},"total":17,"consecutive":true},"attributes":{"extension":"Sign","in_reg":true,"no_alias":false,"nonnull":true,"readonly":false,"no_undef":true,"writable":true,"no_free":false,"capture":"Address","pointee_size":18446744073709551615,"pointee_align":16}}},"bindings":[{"place":{"Parameter":7},"source_offset":5,"source_bytes":11,"carrier_offset":13,"carrier_bytes":17}]},{"size":32,"align":16,"mode":{"Indirect":{"attributes":{"extension":"Sign","in_reg":true,"no_alias":false,"nonnull":true,"readonly":false,"no_undef":true,"writable":true,"no_free":false,"capture":"Address","pointee_size":18446744073709551615,"pointee_align":16},"metadata_attributes":{"extension":"Sign","in_reg":true,"no_alias":false,"nonnull":true,"readonly":false,"no_undef":true,"writable":true,"no_free":false,"capture":"Address","pointee_size":18446744073709551615,"pointee_align":16},"on_stack":true,"caller_copy":false}},"bindings":[{"place":{"Parameter":7},"source_offset":5,"source_bytes":11,"carrier_offset":13,"carrier_bytes":17}]}],"result":{"size":32,"align":16,"mode":{"Indirect":{"attributes":{"extension":"Sign","in_reg":true,"no_alias":false,"nonnull":true,"readonly":false,"no_undef":true,"writable":true,"no_free":false,"capture":"Address","pointee_size":18446744073709551615,"pointee_align":16},"metadata_attributes":{"extension":"Sign","in_reg":true,"no_alias":false,"nonnull":true,"readonly":false,"no_undef":true,"writable":true,"no_free":false,"capture":"Address","pointee_size":18446744073709551615,"pointee_align":16},"on_stack":true,"caller_copy":false}},"bindings":[{"place":{"Parameter":7},"source_offset":5,"source_bytes":11,"carrier_offset":13,"carrier_bytes":17}]}}"##

private def require (label : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError label)
private def parse (text : String) : IO Json :=
  match Json.parse text with
  | .ok value => pure value
  | .error error => throw (IO.userError error)
private def isRefused {α : Type} : D α → Bool
  | .error _ => true
  | .ok _ => false
private def hasValue {α : Type} [BEq α] (actual : D α) (expected : α) : Bool :=
  match actual with
  | .ok value => value == expected
  | .error _ => false

-- Every manually constructed typed descriptor is refused by the executable
-- guard. This theorem is about the refusal boundary, not its ABI correctness.
example (abi : SignatureAbi) (state : MachineState) :
    Sem.run (requireUntypedAbi (some abi)) state =
      .error (.unsupported .interproceduralCall "typed ABI transport semantics unsupported") := rfl

example (sig : FuncTyDef) (body : FuncBody) (abi : SignatureAbi) :
    checkIndirectSignature { sig with abi := some abi } body =
      .error "typed ABI transport semantics unsupported" := rfl

def main : IO Unit := do
  let value ← parse fixture
  require "full ABI descriptor retention" (hasValue (signatureAbi value) expected)
  let nonvariadic := fixture.replace "\"variadic\":true" "\"variadic\":false"
  let rustCall ← parse (nonvariadic.replace "\"fixed_count\":4" "\"fixed_count\":1")
  require "nonvariadic untupled tail excluded from fixed count"
    (hasValue (signatureAbi rustCall) { expected with variadic := false, fixedCount := 1 })
  let trackCaller ← parse nonvariadic
  require "nonvariadic appended caller location excluded from fixed count"
    (hasValue (signatureAbi trackCaller) { expected with variadic := false })
  let tooMany ← parse (fixture.replace "\"fixed_count\":4" "\"fixed_count\":6")
  require "fixed count beyond argument census refused" (isRefused (signatureAbi tooMany))
  let signature : FuncTyDef := { params := [.U64], returns := [], isVararg := false, abi := some expected }
  let encoded := Json.mkObj [("params", toJson (["U64"] : List String)),
    ("returns", toJson ([] : List String)), ("is_vararg", toJson false), ("abi", value)]
  require "FuncTy descriptor retention" (hasValue (funcTyDef encoded) signature)
  for key in ["Abi", "signature_abi", "abi_typo"] do
    let misspelled := Json.mkObj [("params", toJson (["U64"] : List String)),
      ("returns", toJson ([] : List String)), ("is_vararg", toJson false), (key, value)]
    require s!"FuncTy misspelled descriptor refused: {key}" (isRefused (funcTyDef misspelled))
  let future := Json.mkObj [("params", toJson (["U64"] : List String)),
    ("returns", toJson ([] : List String)), ("is_vararg", toJson false),
    ("abi", value), ("future_abi_contract", toJson true)]
  require "FuncTy future field refused with a retained ABI" (isRefused (funcTyDef future))
  let legacy ← parse r##"{"params":[],"returns":[],"is_vararg":false}"##
  require "legacy missing descriptor" (hasValue (funcTyDef legacy) { params := [], returns := [], isVararg := false })
  let nullAbi ← parse r##"{"params":[],"returns":[],"is_vararg":false,"abi":null}"##
  require "legacy null descriptor" (hasValue (funcTyDef nullAbi) { params := [], returns := [], isVararg := false })
  for (tag, expectedConv) in [("C", CallingConv.C), ("Fast", .Fast), ("Cold", .Cold),
      ("Rust", .Rust), ("Swift", .Swift), ("CUnwind", .CUnwind), ("SysV64", .SysV64),
      ("Win64", .Win64), ("Aapcs", .Aapcs), ("EfiApi", .EfiApi), ("VectorCall", .VectorCall), ("RustCold", .RustCold)] do
    require tag (hasValue (callingConv (.str tag)) expectedConv)
  for (tag, ext) in [("None", AbiExtension.None), ("Sign", .Sign), ("Zero", .Zero)] do
    require tag (hasValue (abiExtension (.str tag)) ext)
  for (tag, capture) in [("Any", AbiCapture.Any), ("ReadOnly", .ReadOnly), ("Address", .Address), ("None", .None)] do
    require tag (hasValue (abiCapture (.str tag)) capture)
  for (tag, cls) in [("Integer", AbiRegisterClass.Integer), ("Float", .Float), ("Vector", .Vector)] do
    require tag (hasValue (abiRegister (Json.mkObj [("class", .str tag), ("bytes", toJson (16 : Nat))])) { regClass := cls, bytes := 16 })
  for (tag, place) in [("Parameter", AbiBindingPlace.Parameter 7), ("Result", .Result 7), ("HiddenResult", .HiddenResult 7)] do
    let encoded := Json.mkObj [("place", Json.mkObj [(tag, toJson (7 : Nat))]),
      ("source_offset", toJson (5 : Nat)), ("source_bytes", toJson (11 : Nat)),
      ("carrier_offset", toJson (13 : Nat)), ("carrier_bytes", toJson (17 : Nat))]
    require tag (hasValue (abiBinding encoded) { binding with place := place })
  for bits in [8, 16, 32, 64] do
    require "largest bounded integer" (hasValue (abiNat bits "boundary" (toJson (2 ^ bits - 1))) (2 ^ bits - 1))
    require "overflow integer refused" (isRefused (abiNat bits "boundary" (toJson (2 ^ bits))))
    require "negative integer refused" (isRefused (abiNat bits "boundary" (toJson (-1 : Int))))
  let extra := Json.mkObj [("unexpected", toJson true)]
  require "unknown record field refused" (isRefused (signatureAbi extra))
  require "unknown nested field refused" (isRefused (abiAttributes extra))
  require "unknown enum variant refused" (isRefused (abiPassMode (.str "Future")))
  require "Ignore payload refused" (isRefused (abiPassMode (Json.mkObj [("Ignore", toJson true)])))
  let m : TrustIrEval.Module := { functions := [], funcTys := [signature], globals := [], enums := [], structs := [], types := [] }
  require "typed descriptor executable oracle refusal" (match contextOf m 10 with
    | .error (.unsupported "signature_abi.transport_semantics") => true
    | _ => false)
  require "untyped context accepted" (match contextOf { m with funcTys := [{ signature with abi := none }] } 10 with
    | .ok _ => true | _ => false)
  IO.println "Signature ABI decoder and refusal checks passed"

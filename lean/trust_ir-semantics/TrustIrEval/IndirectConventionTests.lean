-- Copyright 2026 Andrew Yates | Apache-2.0
-- Ordinary executable-model controls, without source, ABI or proof authority.
import TrustIrRuntime
import TrustIrEval.RawBoundary
import TrustIrEval.Observation

namespace TrustIrEval.IndirectConventionTests
open Lean (Json)
open TrustIr

private def obj (fields : List (String × Json)) : Json := Json.mkObj fields
private def arr (values : List Json) : Json := .arr values.toArray
private def nat (value : Nat) : Json := .num value
private def ids (values : List Nat) : Json := arr (values.map nat)
private def tag (name : String) (value : Json) : Json := obj [(name,value)]
private def pointer : Json := tag "Func" (nat 0)
private def tuple : Json := tag "Tuple" (arr [pointer])
private def node (name : String) (fields : List (String × Json))
    (results : List Nat := []) : Json :=
  obj [("inst",tag name (obj fields)),("results",ids results)]
private def constant (ty value : Json) (result : Nat) : Json :=
  node "Const" [("ty",ty),("value",value)] [result]
private def ret (value : Nat) : Json := node "Return" [("values",ids [value])]
private def block (params : List Json) (body : List Json) : Json :=
  obj [("id",nat 0),("params",arr params),("body",arr body)]
private def parameter (value : Nat) (ty : Json) : Json := arr [nat value,ty]
private def signature (params returns : List Json) : Json :=
  obj [("params",arr params),("returns",arr returns),
    ("is_vararg",.bool false),("abi",.null)]
private def function (id ty : Nat) (name : String) (body : Json) : Json :=
  obj [("id",nat id),("name",.str name),("ty",nat ty),("entry",nat 0),
    ("calling_conv",.str "Rust"),("blocks",arr [body])]

/-- The first four bodies match the measured Rust control's construction:
    leaf7, leaf9, real seed7/write9/return maker, dynamic tuple consumer.
    A fifth zero-argument entry transports the actual maker return internally.
    This added wrapper is not the same serialized source as the Rust fixture. -/
private def module (edge : String) (returnSeed : Bool := false) : Json :=
  let leaf (id answer : Nat) := function id 0 s!"leaf{answer}" (block [] [
    constant (.str "U64") (tag "Int" (nat answer)) 0, ret 0])
  let maker := function 2 1 "maker" (block [] [
    constant tuple (tag "Aggregate" (arr [tag "FnDef" (nat 0)])) 0,
    constant pointer (tag "FnDef" (nat 1)) 1,
    node "InsertField" [("ty",tuple),("aggregate",nat 0),("field",nat 0),("value",nat 1)] [2],
    ret (if returnSeed then 0 else 2)])
  let consumer := function 3 2 "consumer" (block [parameter 0 tuple] [
    node "ExtractField" [("ty",pointer),("aggregate",nat 0),("field",nat 0)] [1],
    node "CallIndirect" [("callee",nat 1),("sig",nat 0),("args",ids []),
      ("calling_conv",.str edge)] [2], ret 2])
  let root := function 4 0 "canonical_wrapper" (block [] [
    node "Call" [("callee",nat 2),("args",ids [])] [0],
    node "Call" [("callee",nat 3),("args",ids [0])] [1], ret 1])
  let direct := function 5 0 "direct_control" (block [] [
    node "Call" [("callee",nat 1),("args",ids [])] [0], ret 0])
  obj [("functions",arr [leaf 0 7,leaf 1 9,maker,consumer,root,direct]),
    ("func_types",arr [signature [] [.str "U64"],signature [] [tuple],
      signature [tuple] [.str "U64"]]),
    ("globals",arr []),("enums",arr []),("structs",arr []),("types",arr []),
    ("target_info",obj [("triple",.str "aarch64-apple-darwin"),("pointer_size",nat 8),
      ("endianness",.str "Little"),("abi",.null),("struct_passing",.str "Unclassified")])]

private def request (wire : Json) (entry : Nat) : Json :=
  obj [("fuel",nat 1000),("call_depth",nat 8),("batches",arr [obj [
    ("module",wire),("runs",arr [obj [("function",nat entry),("args",arr [])]])]])]

private def one (wire : Json) (entry : Nat) : Except String Json := do
  let answer := RawBoundary.runText (request wire entry).compress
  let batches ← answer.getArr?
  if batches.size != 1 then throw "one batch required"
  let rows ← batches[0]!.getArr?
  if rows.size != 1 then throw "one run required"
  pure rows[0]!

private def ok (value : Nat) : Json :=
  obj [("ok",Observation.renderGraph [.int 64 value])]

private def require (label : String) (condition : Bool) : IO Unit := do
  unless condition do throw (IO.userError s!"indirect convention: {label}")
  IO.println s!"INDIRECT_CONVENTION_PASS {label}"

private def expect (value : Except String Json) : IO Json :=
  match value with
  | .ok result => pure result
  | .error message => throw (IO.userError message)

def main : IO Unit := do
  let matched := module "Rust"
  let wrong := module "C"
  require "canonical real maker write9 return is called by matching Rust edge"
    ((← expect (one matched 4)) == ok 9)
  let wrongResult ← expect (one wrong 4)
  require "wrong C edge to actual Rust target is precise type error"
    (wrongResult == obj [("type_error",.str "CallIndirect: calling convention mismatch")])
  require "returning the seed calls leaf7 rather than actual written leaf9"
    ((← expect (one (module "Rust" true) 4)) == ok 7)
  require "direct Rust call remains executable beside rejected indirect edge"
    ((← expect (one wrong 5)) == ok 9)
  IO.println "INDIRECT_CONVENTION_CANONICAL_PASS controls=4"

end TrustIrEval.IndirectConventionTests

def main : IO Unit := TrustIrEval.IndirectConventionTests.main

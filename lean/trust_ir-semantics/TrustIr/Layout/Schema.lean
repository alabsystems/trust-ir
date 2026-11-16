-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Basic

namespace TrustIr.SourceLayout

/-- Source-owned capture order, which need not be physical byte order.
    This is layout evidence only; it grants no closure memory operation. -/
structure ClosureLayoutDescriptor where
  closure : ClosureTyId
  size : Nat
  align : Nat
  captureOffsets : List Nat
  deriving Repr

/-- The complete source tables used by pure layout. No function body, CFG,
    local-type table, value, memory state or execution resource occurs here.
    `canonicalScalars` records the existing canonical-target boundary;
    `hasTargetInfo` separately retains absence of source target metadata. -/
structure Environment where
  model : ByteModel := .le64
  canonicalScalars : Bool := true
  hasTargetInfo : Bool := false
  types : List (Option Ty) := []
  structs : List StructDef := []
  enums : List EnumDef := []
  records : List RecordDef := []
  closures : List ClosureTy := []
  tupleLayouts : List TupleLayoutDescriptor := []
  closureLayouts : List ClosureLayoutDescriptor := []
  /-- Original declaration headers only. Missing or duplicate item identities
      cannot acquire a layout from a body or an inferred function pointer. -/
  functions : List (FuncId × FuncTyId) := []
  funcTypes : List FuncTyDef := []

inductive Mode where
  | shape
  | execution
  deriving DecidableEq, BEq, Repr

inductive Error where
  | missingType (id : Nat)
  | missingStruct (id : Nat)
  | missingEnum (id : Nat)
  | missingClosure (id : Nat)
  | missingFunction (id : Nat)
  | ambiguousFunction (id : Nat)
  | missingFunctionSignature (id signature : Nat)
  | missingMetadata (kind : String) (id : Nat) (field : String)
  | incoherent (kind : String) (id : Nat)
  | missingTarget (kind : String)
  | scalarTarget
  | sizeOverflow
  | cycle (node : Nat)
  | unsupported (ty : Ty)
  deriving Repr

structure Field where
  ty : Ty
  offset : Nat
  size : Nat
  align : Nat
  deriving Repr

structure Enumeration where
  tag : EnumTagRepr
  discriminants : List Int
  encoding : EnumTagEncoding
  /-- Absolute byte offsets in each logical variant's source-field order. -/
  variants : List (List Field)
  uninhabited : List Bool
  deriving Repr

/-- `none` alignment is the shape-level Never carrier. Byte-layout consumers
    require an actual alignment. Field and enum positions are source-derived. -/
structure Summary where
  size : Nat
  align : Option Nat
  fields : List Field := []
  enumeration : Option Enumeration := none
  deriving Repr

end TrustIr.SourceLayout

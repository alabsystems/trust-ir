-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.SourceRecursiveReadbackCore

/- Shared ordinary DATA values for the recursive readback fixtures.
All values/types are the exact original fixture constructions; no solver or codec is changed. -/
namespace TrustIr.AggregateMemory.RecursiveReadbackControls.FixtureData
open SourceLayout
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

def oldAllocation : Allocation :=
  { id := ⟨7⟩, base := 1024, size := 8, alive := false, origin := .cleanHeap, requested := 8 }

def newAllocation : Allocation :=
  { id := ⟨9⟩, base := 1032, size := 8, alive := true, origin := .rustHeap, requested := 8 }

def memory : Memory := { Memory.empty with allocations := [newAllocation,oldAllocation] }

def byte : Plan := .leaf .U8 ⟨1,1⟩

def boolean : Plan := .leaf .Bool ⟨1,1⟩

def pointer : Plan := .leaf .Ptr ⟨8,8⟩

def character : Plan := .leaf .Char ⟨4,4⟩

def elementTy : Ty := .Tuple [.U8,.Bool,.Ptr]

def elementFields : List (Nat × Plan) := [(0,byte),(1,boolean),(8,pointer)]

def element : Plan := .fields elementTy ⟨16,8⟩ elementFields

def elementInput : Value := .aggregate [.int 8 513,.bool false,.ptr 1025 (some ⟨99⟩)]

def arrayTy : Ty := .Array ⟨0⟩ 3

def array : Plan := .array arrayTy ⟨48,8⟩ 3 element

def arrayValues : CompactArray.Packed Value := CompactArray.Packed.uniform 3 elementInput

def tailTy : Ty := .Tuple [.Ptr,.Char]

def tailFields : List (Nat × Plan) := [(0,pointer),(8,character)]

def tail : Plan := .fields tailTy ⟨16,8⟩ tailFields

def tailInput : Value := .aggregate [.ptr 0 (some ⟨99⟩),.int 32 55296]

def kind : FatPtrKind := .Slice ⟨0⟩

def fat : Plan := .leaf (.FatPtr kind) ⟨16,8⟩

def rootTy : Ty := .Tuple [.Bool,arrayTy,.FatPtr kind,tailTy]

def rootFields : List (Nat × Plan) := [(0,boolean),(8,array),(56,fat),(72,tail)]

def root : Plan := .fields rootTy ⟨88,8⟩ rootFields

def input : Value := .aggregate [.bool true,.array arrayValues,.fatPtr 1034 (some ⟨99⟩) (.int 64 (-1)),tailInput]

def enumInfo : Enumeration :=
  { tag := .u8, discriminants := [5], encoding := .untagged,
    variants := [[{ ty := rootTy, offset := 0, size := 88, align := 8 }]], uninhabited := [false] }

def enumVariants : List (Option (List (Nat × Plan))) := [some [(0,root)]]

def enumPlan : Plan := .enumeration (.Enum ⟨0⟩) ⟨88,8⟩ enumInfo enumVariants

def definition : EnumDef :=
  { id := ⟨0⟩, name := "Mixed", variants := [{ name := "Mixed", fields := [rootTy] }], discriminants := [some 5], tagRepr := some .u8,
    layout := some { encoding := .untagged, size := 88, align := 8, variantFieldOffsets := [[0]] } }

def enumSource : Environment := { types := [some elementTy], enums := [definition] }

end TrustIr.AggregateMemory.RecursiveReadbackControls.FixtureData

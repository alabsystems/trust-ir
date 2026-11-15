/- Copyright 2026 Andrew Yates. Apache-2.0. -/
import SemR
namespace SemR.Storage
open SemR
/-- Geometry never grants initialized-value transport. -/
theorem no_value (pointerBits size align : Nat) (v : Val) :
    expectTy pointerBits v (.storage size align) =
      tyR "TypeError: storage-only type has no value" := rfl
/-- Typed access remains refused even after all bytes have been written. -/
theorem no_scalar_access (pointerBits size align : Nat) :
    scalarLayout pointerBits (.storage size align) = unsupR "mem.access.ty" := rfl
/-- Accepted geometry is exact, without a chosen active field. -/
theorem exact_geometry (pointerBits size align : Nat)
    (h : storageGeometry pointerBits size align = true) :
    layoutOf pointerBits (.storage size align) = .ok (size, align) := by
  simp [layoutOf, h]
theorem invalid_geometry (pointerBits size align : Nat)
    (h : storageGeometry pointerBits size align = false) :
    layoutOf pointerBits (.storage size align) =
      tyR "TypeError: invalid storage geometry" := by simp [layoutOf, h]
example : layoutOf 64 (.storage 80 8) = .ok (80,8) := rfl
example : layoutOf 32 (.storage 80 8) = .ok (80,8) := rfl
example : storageGeometry 32 (2^32) 8 = false := rfl
example : storageGeometry 64 79 8 = false := rfl
example : storageGeometry 64 80 0 = false := rfl
example : storageGeometry 64 0 8 = true := rfl
example : Ty.beq (.storage 80 8) (.storage 88 8) = false := rfl
example : Ty.beq (.storage 80 8) (.storage 80 16) = false := rfl
/-- Wire parsing preserves the geometry-only admission boundary. -/
theorem wire_storage_refused :
    ty 64 #[] [40, 80, 8] = .err (.unsupported "ty.storage") := rfl
theorem wire_storage_before_v64_malformed :
    ty 63 #[] [40, 80, 8] = .err (.malformed "invalid Ty tag") := rfl
theorem wire_invalid_geometry_malformed :
    ty 64 #[] [40, 79, 8] = .err (.malformed "invalid storage geometry") := rfl
end SemR.Storage

/-- info: 'SemR.Storage.no_value' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SemR.Storage.no_value
/-- info: 'SemR.Storage.no_scalar_access' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SemR.Storage.no_scalar_access
/-- info: 'SemR.Storage.exact_geometry' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SemR.Storage.exact_geometry
/-- info: 'SemR.Storage.invalid_geometry' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SemR.Storage.invalid_geometry

/-- info: 'SemR.Storage.wire_storage_refused' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SemR.Storage.wire_storage_refused
/-- info: 'SemR.Storage.wire_storage_before_v64_malformed' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SemR.Storage.wire_storage_before_v64_malformed
/-- info: 'SemR.Storage.wire_invalid_geometry_malformed' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SemR.Storage.wire_invalid_geometry_malformed

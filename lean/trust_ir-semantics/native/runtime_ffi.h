/* Copyright 2026 Andrew Yates | Apache-2.0
 * Actual boxed Lean provider export ABI, including erased type placeholders.
 * Runtime correspondence remains UNPROVED. Checked against runtime-boundary.json.
 */
#ifndef TRUST_IR_RUNTIME_FFI_H
#define TRUST_IR_RUNTIME_FFI_H
#include <lean/lean.h>

LEAN_EXPORT lean_object* l_TrustIr_CompactArray_Leaf_checkStored(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_TrustIr_CompactArray_Tree_checkStored(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_TrustIr_CompactArray_Leaf_checkRange(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_TrustIr_CompactArray_Tree_checkRange(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_TrustIr_CompactArray_Tree_eqByM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_TrustIr_Value_depth(lean_object*);
LEAN_EXPORT lean_object* l_TrustIr_valueListDepth(lean_object*);
LEAN_EXPORT lean_object* l_TrustIr_valueFieldDepth(lean_object*);
LEAN_EXPORT lean_object* l_TrustIr_arrayTreeDepth(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_TrustIr_arrayLeafDepth(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_TrustIr_ByteImage_map(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_TrustIr_ByteImage_firstWhere(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_TrustIr_ByteImage_mapBlocks(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_TrustIr_ByteImage_checkBlocks(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_TrustIr_Semantics_AggregateImages_0__TrustIr_AggregateMemory_encodeArrayImage(lean_object*, lean_object*, lean_object*);

#endif

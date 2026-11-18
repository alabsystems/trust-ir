-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.MemorySafetyCore
import TrustIr.Proofs.MemorySafetyLifetime
import TrustIr.Proofs.MemorySafetyProvenance

#trustIrAxiomsExact TrustIr.semDealloc_twice_is_ub_example == []
#trustIrAxiomsExact TrustIr.semRelease_after_last_release_is_ub == []
#trustIrAxiomsExact TrustIr.semDealloc_cleanHeap_is_ub_example == []
#trustIrAxiomsExact TrustIr.semDealloc_swiftHeap_is_ub_example == []
#trustIrAxiomsExact TrustIr.requireArcRef_non_arcRef_is_ub == []
#trustIrAxiomsExact TrustIr.semRetain_alloca_is_ub_example == []
#trustIrAxiomsExact TrustIr.semRelease_rustHeap_is_ub_example == []
#trustIrAxiomsExact TrustIr.semIsUnique_cMalloc_is_ub_example == []
#trustIrAxiomsExact TrustIr.semRetain_globalAddr_is_ub_example == []
#trustIrAxiomsExact TrustIr.arc_at_object_base_ok_example == []
#trustIrAxiomsExact TrustIr.semDealloc_under_borrow_is_ub_example == []
#trustIrAxiomsExact TrustIr.semDealloc_under_borrowMut_is_ub_example == []
#trustIrAxiomsExact TrustIr.semDealloc_one_of_two_borrows_live_is_ub_example == []
#trustIrAxiomsExact TrustIr.semDealloc_after_every_endBorrow_ok_example == []

#trustIrAxiomsExact TrustIr.semRetain_non_arcRef_is_ub == [propext]
#trustIrAxiomsExact TrustIr.semRelease_non_arcRef_is_ub == [propext]
#trustIrAxiomsExact TrustIr.semIsUnique_non_arcRef_is_ub == [propext]

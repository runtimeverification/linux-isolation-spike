-- Axiom audit for every top-level result. Run via ./axioms.sh
--
-- Phase 3 step 2: only the Aeneas-generated model exists so far, so this
-- audits the generated definitions. Theorems are added from step 3 onward.
--
-- This matters more than it looks: `lake build` reports that the Aeneas
-- standard library itself carries `sorry` in Aeneas/Std/Slice.lean:363,
-- Aeneas/Std/Slice.lean:586 and Aeneas/Std/StringIter.lean:13 (the
-- `get_unchecked` unchecked-slice-access specs). The audit below is what
-- establishes -- empirically, not by assumption -- that our model does not
-- reach them: it uses `Array _ 5#usize` / `Array _ 340#usize` with checked
-- indexing, and never a `Slice`.
import Uidmap
import Safety
import Spec
import Algebra
import WritePath
open uidmap

#print axioms cmp_map_id
#print axioms bsearch_extent
#print axioms map_id_range_down_base
#print axioms map_id_range_down_max
#print axioms map_id_range_down
#print axioms map_id_down
#print axioms map_id_range_up_base
#print axioms map_id_range_up_max
#print axioms map_id_range_up
#print axioms map_id_up
#print axioms make_kuid
#print axioms from_kuid
#print axioms insert_extent
#print axioms UidGidMap.zeroed
#print axioms UidGidMap.init_user_ns_map

/-! ## Phase 3 step 3: the safety theorems (Safety.lean) -/
open UidmapSafety

-- S1
#print axioms total_safety
#print axioms map_id_down_total_safety
#print axioms map_id_up_total_safety
#print axioms map_id_range_down_total_safety
#print axioms map_id_range_up_total_safety
#print axioms insert_extent_total_safety
-- helpers
#print axioms spec_true_iff_ok
#print axioms cmp_map_id_spec
-- S4 arithmetic bridge
#print axioms last_val
#print axioms id2_val
-- S2 + S3
#print axioms map_id_range_down_base_loop_spec
#print axioms map_id_range_up_base_loop_spec
#print axioms map_id_range_down_base_spec
#print axioms map_id_range_up_base_spec
#print axioms bsearch_extent_loop_spec
#print axioms bsearch_extent_spec
#print axioms map_id_range_down_spec
#print axioms map_id_range_up_spec
#print axioms map_id_down_spec
#print axioms map_id_up_spec
#print axioms make_kuid_spec
#print axioms from_kuid_spec
-- S2 + S3, write path
#print axioms insert_extent_loop_spec
#print axioms insert_extent_spec
-- S5
#print axioms no_stale_read_down
#print axioms no_stale_read_up
#print axioms base_arm_only_down

/-! ## Phase 3 step 4: the abstract map and the functional lookups -/
open UidmapSpec UidmapAlgebra

-- Spec.lean: the algebra and the initial map
#print axioms apDown_inL
#print axioms apUp_apDown
#print axioms apDown_injective
#print axioms inL_ne_sentinel
#print axioms WellFormed.mem_absRev_iff
#print axioms WellFormed.apDown_ne_sentinel
#print axioms WellFormed.abs_injective
#print axioms WellFormed.abs_roundtrip
#print axioms init_user_ns_map_wf
-- Algebra.lean: F1 soundness
#print axioms id2_one_val
#print axioms down_result_val
#print axioms up_result_val
#print axioms cmp_map_id_zero_down
#print axioms cmp_map_id_zero_up
#print axioms base_loop_down_fun
#print axioms base_loop_up_fun
#print axioms bsearch_loop_sound
#print axioms cmp_zero_inU
#print axioms cmp_zero_inL
#print axioms down_sound
#print axioms up_sound
-- F2
#print axioms down_injective
-- F3
#print axioms roundtrip_sound
#print axioms roundtrip_complete_le5
-- the two step-5 gaps: expect sorryAx on BOTH of these, and nowhere else
#print axioms bsearch_complete
#print axioms roundtrip_complete

/-! ## Phase 3 step 4: the write path (WritePath.lean) -/
open UidmapWritePath
-- proved
#print axioms inL_remap
#print axioms remap_disjoint
#print axioms take_set_of_le
#print axioms take_add_one_of_getElem
#print axioms take_set_succ
#print axioms forall_take_succ'
#print axioms insert_extent_loop_fun
#print axioms insert_extent_fun
#print axioms overlapsU_iff
#print axioms overlapsL_iff
#print axioms dispatch_read
#print axioms mappings_overlap_loop_fun
#print axioms mappings_overlap_fun
#print axioms preserve_lower_list
#print axioms cmp_zero_inU_range
#print axioms down_range_sound
#print axioms nowrap_check_iff
#print axioms overlaps_self
#print axioms preRemap_append
#print axioms nodup_append_of_disjoint
-- named gaps: expect sorryAx on these two, and on the three that inherit from them
#print axioms sort_idmaps_fun
#print axioms remap_install_fun
#print axioms lines_loop_fun
#print axioms write_preserves_wf
#print axioms reachable_wf

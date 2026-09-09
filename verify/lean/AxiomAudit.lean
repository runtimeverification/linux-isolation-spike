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

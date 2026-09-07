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

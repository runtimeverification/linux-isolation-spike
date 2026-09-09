-- SPDX-License-Identifier: GPL-2.0
import Spec
import Safety
import Algebra
/-!
# F5 `PRESERVE` — the write path keeps the map well-formed (SPEC.md §4.5)

`map_write parent lines = ok (0, m) → WellFormed m`, given `WellFormed parent`
(`A-PARENT-WF`). The interesting half is `PRESERVE-LOWER`: the lower intervals
of the installed map are disjoint although `mappings_overlap` only checked the
*pre-remap* values (SPEC §1.5). This file has:

1. the pure induction step, `remap_disjoint`, on lists — the mathematics of
   `PRESERVE-LOWER`;
2. functional specs for the pieces of the write path, each an Aeneas loop:
   `insert_extent` appends to the abstract map; the line loop accumulates the
   parsed extents; the remap loop maps every `lower_first` through the parent;
   `sort_idmaps` permutes; the install copies;
3. the assembly, and the closed form by induction on namespace depth.

Gaps carry `sorry` under their own names and are listed in
`OPEN_CHALLENGES.md`.
-/
open Aeneas Aeneas.Std Result ControlFlow WP
open uidmap UidmapSpec UidmapSafety UidmapAlgebra

namespace UidmapWritePath

/-! ## 1. The mathematics of PRESERVE-LOWER -/

/-- The re-mapping of one extent through the parent at `map_write` 1072/1082:
`lower_first` becomes its image; `first` and `count` are untouched. `p` is the
parent extent that contains the whole lower range. -/
def remapBy (p : UidGidExtent) (e : UidGidExtent) (lf : U32) : UidGidExtent :=
  { e with lower_first := lf }

/-- A remapped extent's lower interval is the image of the original's under
the containing parent extent. -/
theorem inL_remap {p e : UidGidExtent} {lf : U32}
    (hlo : inU p e.lower_first.val) (hhi : inU p (e.lower_first.val + e.count.val - 1))
    (hcnt : 1 ≤ e.count.val) (hlf : lf.val = apDown p e.lower_first.val) (y : Nat) :
    inL (remapBy p e lf) y ↔ ∃ z, inL e z ∧ y = apDown p z := by
  unfold inL inU apDown remapBy at *
  simp only
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨y - lf.val + e.lower_first.val, ?_, ?_⟩ <;> omega
  · rintro ⟨z, ⟨hz1, hz2⟩, rfl⟩
    omega

/-- **PRESERVE-LOWER, the induction step.** Two extents whose lower ranges were
disjoint before the re-map, each re-mapped through a parent extent that
contains its whole lower range, have disjoint lower ranges after the re-map —
because the parent's own lower ranges are disjoint (`A-PARENT-WF`) and each
parent extent is a translation. -/
theorem remap_disjoint {p1 p2 e1 e2 : UidGidExtent} {lf1 lf2 : U32}
    (hp : ∀ y, inL p1 y → inL p2 y → p1 = p2)
    (h1lo : inU p1 e1.lower_first.val) (h1hi : inU p1 (e1.lower_first.val + e1.count.val - 1))
    (h2lo : inU p2 e2.lower_first.val) (h2hi : inU p2 (e2.lower_first.val + e2.count.val - 1))
    (hc1 : 1 ≤ e1.count.val) (hc2 : 1 ≤ e2.count.val)
    (hlf1 : lf1.val = apDown p1 e1.lower_first.val) (hlf2 : lf2.val = apDown p2 e2.lower_first.val)
    (hpre : ∀ z, inL e1 z → inL e2 z → False)
    (y : Nat) (hy1 : inL (remapBy p1 e1 lf1) y) (hy2 : inL (remapBy p2 e2 lf2) y) : False := by
  obtain ⟨z1, hz1, rfl⟩ := (inL_remap h1lo h1hi hc1 hlf1 y).1 hy1
  obtain ⟨z2, hz2, hz⟩ := (inL_remap h2lo h2hi hc2 hlf2 _).1 hy2
  -- the common image lies in both parent lower intervals
  have hp1 : inL p1 (apDown p1 z1) := apDown_inL (by unfold inU inL at *; omega)
  have hp2 : inL p2 (apDown p1 z1) := by rw [hz]; exact apDown_inL (by unfold inU inL at *; omega)
  have hpp := hp _ hp1 hp2
  subst hpp
  have : z1 = z2 := apDown_injective (by unfold inU inL at *; omega) (by unfold inU inL at *; omega) hz
  subst this
  exact hpre z1 hz1 hz2

/-! ## 2. List helpers for the abstract map -/

/-- A prefix of a set-list agrees with the original off the written slot. -/
theorem take_set_of_le {α} (l : List α) (n k : Nat) (x : α) (hk : k ≤ n) :
    (l.set n x).take k = l.take k := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_take]
    rw [List.getElem_set_ne (by simp at h1; omega)]

/-- `take (k+1)` is `take k` plus the `k`-th element. -/
theorem take_add_one_of_getElem {α} (l : List α) (k : Nat) (hk : k < l.length) :
    l.take (k + 1) = l.take k ++ [l[k]] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hk]; rfl

/-- `forall_take_succ` with the new element given by `getElem?`, so no
dependent bound proof appears in statements about the abstract map. -/
theorem forall_take_succ' {α} (l : List α) (k : Nat) (x : α) (P : α → Prop)
    (hprev : ∀ e ∈ l.take k, P e) (hx : l[k]? = some x) (hcur : P x) :
    ∀ e ∈ l.take (k + 1), P e := by
  intro e he
  rw [List.take_add_one, hx] at he
  simp only [Option.toList_some, List.mem_append, List.mem_singleton] at he
  rcases he with h | h
  · exact hprev e h
  · subst h; exact hcur

/-- Writing one slot just past a prefix extends the prefix by that element. -/
theorem take_set_succ {α} (l : List α) (n : Nat) (x : α) (hn : n < l.length) :
    (l.set n x).take (n + 1) = l.take n ++ [x] := by
  rw [take_add_one_of_getElem (l.set n x) n (by simp; omega), take_set_of_le l n n x le_rfl,
      List.getElem_set_self]

/-! ## 3. `insert_extent`, functionally: it appends to the abstract map -/

/-- The migration memcpy (`insert_extent` 803–804): after the loop the heap
arm's first `i` slots equal the base arm's. -/
theorem insert_extent_loop_fun
    (a : Array UidGidExtent 5#usize) (a1 : Array UidGidExtent 340#usize) (i i1 : U32)
    (hi : i.val ≤ 5) (hi1 : i1.val ≤ i.val)
    (hpre : a1.val.take i1.val = a.val.take i1.val) :
    insert_extent_loop a a1 i i1 ⦃ r => r.val.take i.val = a.val.take i.val ⦄ := by
  unfold insert_extent_loop
  apply loop.spec_decr_nat (fun p : Array UidGidExtent 340#usize × U32 => i.val - p.2.val)
    (fun p : Array UidGidExtent 340#usize × U32 =>
      p.2.val ≤ i.val ∧ p.1.val.take p.2.val = a.val.take p.2.val)
    _ _ _ _ (And.intro hi1 hpre)
  intro p hinv
  obtain ⟨a2, i2⟩ := p
  obtain ⟨hi2, hpre⟩ := hinv
  dsimp only
  unfold insert_extent_loop.body
  split
  · rename_i hlt
    have hlt' : i2.val < i.val := by scalar_tac
    have hlen5 : a.val.length = 5 := by simp [Array.length_eq]
    have hlen340 : a2.val.length = 340 := by simp [Array.length_eq]
    -- both `i1 as usize` casts are the same term once the lifts are inlined
    simp only [lift, bind_tc_ok]
    have hk := cast_usize_val i2
    have hb1 : (UScalar.cast .Usize i2).val < a.length := by simp only [Array.length]; scalar_tac
    step with Array.index_usize_spec a (UScalar.cast .Usize i2) hb1 as ⟨ uge, huge ⟩
    have hb2 : (UScalar.cast .Usize i2).val < a2.length := by simp only [Array.length]; scalar_tac
    step with Array.update_spec a2 (UScalar.cast .Usize i2) uge hb2 as ⟨ a3, ha3 ⟩
    step with @UScalar.add_spec .U32 i2 1#u32 (by scalar_tac) as ⟨ i3, hi3 ⟩
    all_goals (try simp only [spec_ok, and_assoc])
    refine ⟨by scalar_tac, ?_, by scalar_tac⟩
    -- new prefix: a3.take (i2+1) = a.take (i2+1), computed at the cast index
    have hpre' : a2.val.take (UScalar.cast .Usize i2).val = a.val.take (UScalar.cast .Usize i2).val := by
      rw [hk]; exact hpre
    have hi3' : i3.val = (UScalar.cast .Usize i2).val + 1 := by rw [hi3, hk]
    rw [hi3', ha3, Array.set_val_eq, take_set_succ _ _ _ (by omega), hpre', huge,
        ← take_add_one_of_getElem a.val (UScalar.cast .Usize i2).val (by omega)]
  · simp only [spec_ok]
    rename_i hge
    have : i2.val = i.val := by scalar_tac
    rw [← this]; exact hpre

/-- **`insert_extent` appends.** Under `nr_extents < 340`, the result has one
more extent, its abstract map is the old one with `e` appended, and the
`reverse` arm is untouched. This is the functional content behind the three
branches of `insert_extent_spec` (Safety.lean), including the migration at
`nr_extents == 5` where the base arm is copied into the heap arm and then
clobbered. -/
theorem insert_extent_fun (m : UidGidMap) (e : UidGidExtent)
    (hlen : m.nr_extents.val < 340) :
    insert_extent m e ⦃ r => r.1 = 0#i32 ∧ r.2.nr_extents.val = m.nr_extents.val + 1 ∧
      absFwd r.2 = absFwd m ++ [e] ∧ r.2.reverse = m.reverse ⦄ := by
  unfold insert_extent
  have h5 : (UScalar.cast .U32 UID_GID_MAP_MAX_BASE_EXTENTS).val = 5 := by
    simp [UID_GID_MAP_MAX_BASE_EXTENTS, UScalar.cast_val_eq]
  have hlen5 : m.extent.val.length = 5 := by simp
  have hlen340 : m.forward.val.length = 340 := by simp
  simp only [lift, bind_tc_ok]
  split
  · -- migration: nr_extents == 5
    rename_i heq
    have h5' : m.nr_extents.val = 5 := by rw [heq]; exact h5
    step with insert_extent_loop_fun m.extent m.forward m.nr_extents 0#u32 (by scalar_tac) (by simp)
      (by simp) as ⟨ a, ha ⟩
    have hb0 : (0#usize).val < m.extent.length := by simp [Array.length]
    step with Array.update_spec m.extent 0#usize _ hb0 as ⟨ a1, ha1 ⟩
    have hb1 : (1#usize).val < a1.length := by simp [Array.length]
    step with Array.index_mut_usize_spec a1 1#usize hb1 as ⟨ uge, back, hmut ⟩
    have hnlt : ¬ (m.nr_extents < UScalar.cast .U32 UID_GID_MAP_MAX_BASE_EXTENTS) := by scalar_tac
    simp only [hnlt, if_false]
    have hk := cast_usize_val m.nr_extents
    have hbk : (UScalar.cast .Usize m.nr_extents).val < a.length := by
      simp only [Array.length, Array.length_eq]; scalar_tac
    step with Array.update_spec a (UScalar.cast .Usize m.nr_extents) e hbk as ⟨ a4, ha4 ⟩
    step with @UScalar.add_spec .U32 m.nr_extents 1#u32 (by scalar_tac) as ⟨ n1, hn1 ⟩
    all_goals (try simp only [spec_ok])
    repeat' constructor
    all_goals (first | rfl | scalar_tac | skip)
    -- abstract maps: new is the heap arm with 6 entries, old is the base arm with 5
    have hlena : a.val.length = 340 := by simp [Array.length_eq]
    have hn1' : n1.val = 6 := by scalar_tac
    rw [h5'] at ha
    rw [absFwd_gt5 (by simp; omega), absFwd_le5 (by omega)]
    simp only
    rw [hn1', h5', ha4, Array.set_val_eq, hk, h5', take_set_succ _ _ _ (by omega), ha]
  · rename_i hne
    split
    · -- nr_extents < 5: the base arm grows
      rename_i hlt
      have hlt' : m.nr_extents.val < 5 := by scalar_tac
      have hk := cast_usize_val m.nr_extents
      have hbk : (UScalar.cast .Usize m.nr_extents).val < m.extent.length := by
        simp only [Array.length, Array.length_eq]; scalar_tac
      step with Array.update_spec m.extent (UScalar.cast .Usize m.nr_extents) e hbk as ⟨ a2, ha2 ⟩
      step with @UScalar.add_spec .U32 m.nr_extents 1#u32 (by scalar_tac) as ⟨ n1, hn1 ⟩
      all_goals (try simp only [spec_ok])
      repeat' constructor
      all_goals (first | rfl | scalar_tac | skip)
      rw [absFwd_le5 (by simp; omega), absFwd_le5 (by omega)]
      simp only
      rw [hn1, ha2, Array.set_val_eq, hk, take_set_succ _ _ _ (by omega)]
    · -- nr_extents > 5 (≠ 5 and not < 5): the heap arm grows
      have hgt : 5 < m.nr_extents.val := by scalar_tac
      have hk := cast_usize_val m.nr_extents
      have hbk : (UScalar.cast .Usize m.nr_extents).val < m.forward.length := by
        simp only [Array.length, Array.length_eq]; scalar_tac
      step with Array.update_spec m.forward (UScalar.cast .Usize m.nr_extents) e hbk as ⟨ a2, ha2 ⟩
      step with @UScalar.add_spec .U32 m.nr_extents 1#u32 (by scalar_tac) as ⟨ n1, hn1 ⟩
      all_goals (try simp only [spec_ok])
      repeat' constructor
      all_goals (first | rfl | scalar_tac | skip)
      rw [absFwd_gt5 (by simp; omega), absFwd_gt5 hgt]
      simp only
      rw [hn1, ha2, Array.set_val_eq, hk, take_set_succ _ _ _ (by omega)]

/-! ## 4. `mappings_overlap`, functionally -/

/-- Exact-interval reading of the C's two intersection tests (:771–774,
:776–779) once `last` is exact for both extents. -/
def overlaps (prev e : UidGidExtent) : Prop :=
  (∃ x, inU prev x ∧ inU e x) ∨ (∃ y, inL prev y ∧ inL e y)

/-- Two closed intervals `[a, a+n-1]`, `[b, b+m-1]` (`n, m ≥ 1`) intersect iff
`a ≤ b+m-1 ∧ a+n-1 ≥ b` — the C's test at :772–773. -/
theorem overlapsU_iff (p e : UidGidExtent) (hp : 1 ≤ p.count.val) (he : 1 ≤ e.count.val) :
    (∃ x, inU p x ∧ inU e x) ↔
      (p.first.val ≤ e.first.val + e.count.val - 1 ∧ p.first.val + p.count.val - 1 ≥ e.first.val) := by
  unfold inU; constructor
  · rintro ⟨x, ⟨h1, h2⟩, ⟨h3, h4⟩⟩; omega
  · rintro ⟨h1, h2⟩; exact ⟨max p.first.val e.first.val, by omega, by omega⟩

theorem overlapsL_iff (p e : UidGidExtent) (hp : 1 ≤ p.count.val) (he : 1 ≤ e.count.val) :
    (∃ y, inL p y ∧ inL e y) ↔
      (p.lower_first.val ≤ e.lower_first.val + e.count.val - 1 ∧
       p.lower_first.val + p.count.val - 1 ≥ e.lower_first.val) := by
  unfold inL; constructor
  · rintro ⟨y, ⟨h1, h2⟩, ⟨h3, h4⟩⟩; omega
  · rintro ⟨h1, h2⟩; exact ⟨max p.lower_first.val e.lower_first.val, by omega, by omega⟩

/-- The union dispatch that reads the `idx`-th extent of the active arm
(:761–764; the same shape at 1067–1070 and 899–902): whichever arm it reads,
the result is the `idx`-th element of the abstract map. -/
theorem dispatch_read (new_map : UidGidMap) (idx : U32)
    (hidx : idx.val < new_map.nr_extents.val) (hlen : new_map.nr_extents.val ≤ 340) :
    (if new_map.nr_extents ≤ UScalar.cast .U32 UID_GID_MAP_MAX_BASE_EXTENTS
      then Array.index_usize new_map.extent (UScalar.cast .Usize idx)
      else Array.index_usize new_map.forward (UScalar.cast .Usize idx))
    ⦃ prev => (absFwd new_map)[idx.val]? = some prev ⦄ := by
  have h5 : (UScalar.cast .U32 UID_GID_MAP_MAX_BASE_EXTENTS).val = 5 := by
    simp [UID_GID_MAP_MAX_BASE_EXTENTS, UScalar.cast_val_eq]
  have hk := cast_usize_val idx
  split
  · rename_i hle
    have hle' : new_map.nr_extents.val ≤ 5 := by scalar_tac
    have hb : (UScalar.cast .Usize idx).val < new_map.extent.length := by
      simp only [Array.length]; scalar_tac
    apply spec_mono (Array.index_usize_spec new_map.extent _ hb)
    intro v hv
    rw [absFwd_le5 hle', List.getElem?_take_of_lt hidx, ← hk,
        List.getElem?_eq_getElem (by simp only [Array.length] at hb; exact hb), hv]
  · rename_i hgt
    have hgt' : 5 < new_map.nr_extents.val := by scalar_tac
    have hb : (UScalar.cast .Usize idx).val < new_map.forward.length := by
      simp only [Array.length]; scalar_tac
    apply spec_mono (Array.index_usize_spec new_map.forward _ hb)
    intro v hv
    rw [absFwd_gt5 hgt', List.getElem?_take_of_lt hidx, ← hk,
        List.getElem?_eq_getElem (by simp only [Array.length] at hb; exact hb), hv]

/-- The loop of `mappings_overlap` (:757–780). `absFwd new_map` is the list it
walks; `upper_last`/`lower_last` are the candidate's exact last ids. -/
theorem mappings_overlap_loop_fun (e : UidGidExtent) (new_map : UidGidMap)
    (upper_last lower_last idx : U32)
    (hlen : new_map.nr_extents.val ≤ 340) (hidx : idx.val ≤ new_map.nr_extents.val)
    (hecnt : 1 ≤ e.count.val)
    (hul : upper_last.val = e.first.val + e.count.val - 1)
    (hll : lower_last.val = e.lower_first.val + e.count.val - 1)
    (hwf : ∀ p ∈ absFwd new_map, 1 ≤ p.count.val ∧ p.first.val + p.count.val ≤ 2^32 - 1 ∧
      p.lower_first.val + p.count.val ≤ 2^32 - 1)
    (hpre : ∀ p ∈ (absFwd new_map).take idx.val, ¬ overlaps p e) :
    mappings_overlap_loop e new_map upper_last lower_last idx ⦃ r =>
      r = false → ∀ p ∈ absFwd new_map, ¬ overlaps p e ⦄ := by
  unfold mappings_overlap_loop
  apply loop.spec_decr_nat (fun idx : U32 => new_map.nr_extents.val - idx.val)
    (fun idx : U32 => idx.val ≤ new_map.nr_extents.val ∧
      ∀ p ∈ (absFwd new_map).take idx.val, ¬ overlaps p e)
    _ _ _ _ (And.intro hidx hpre)
  intro idx hinv
  obtain ⟨hidx, hpre⟩ := hinv
  unfold mappings_overlap_loop.body
  have hlenA : (absFwd new_map).length = new_map.nr_extents.val := by
    unfold absFwd; split <;> simp <;> omega
  split
  · rename_i hlt
    have hlt' : idx.val < new_map.nr_extents.val := by scalar_tac
    simp only [lift, bind_tc_ok]
    step with dispatch_read new_map idx hlt' hlen as ⟨ prev, hprev ⟩
    have hmem : prev ∈ absFwd new_map := List.mem_of_getElem? hprev
    obtain ⟨hpc, hpu, hpl⟩ := hwf prev hmem
    have hpul := last_val prev.first prev.count hpc (by simp [U32.max_eq]; omega)
    have hpll := last_val prev.lower_first prev.count hpc (by simp [U32.max_eq]; omega)
    split_ifs
    all_goals first
      | (simp [spec_ok]; done)
      | (step with @UScalar.add_spec .U32 idx 1#u32 (by scalar_tac) as ⟨ idx1, hidx1 ⟩
         all_goals (try simp only [spec_ok, and_assoc])
         refine ⟨by scalar_tac, ?_, by scalar_tac⟩
         have hnot : ¬ overlaps prev e := by
           unfold overlaps
           rw [overlapsU_iff _ _ hpc hecnt, overlapsL_iff _ _ hpc hecnt]
           scalar_tac
         rw [hidx1]
         exact forall_take_succ' _ _ _ _ hpre hprev hnot)
  · simp only [spec_ok]
    intro _ p hp
    have : idx.val = new_map.nr_extents.val := by scalar_tac
    rw [this, ← hlenA, List.take_length] at hpre
    exact hpre p hp

/-- `mappings_overlap` says `false` only when the candidate is disjoint from
every extent of the abstract map, in both coordinates. Preconditions: the
candidate and every inserted extent have `count ≥ 1` and exact `last`s, which
is what the checks at 1031/1033 and the running invariant provide. -/
theorem mappings_overlap_fun (new_map : UidGidMap) (e : UidGidExtent)
    (hlen : new_map.nr_extents.val ≤ 340)
    (he : 1 ≤ e.count.val ∧ e.first.val + e.count.val ≤ 2^32 - 1 ∧
      e.lower_first.val + e.count.val ≤ 2^32 - 1)
    (hwf : ∀ p ∈ absFwd new_map, 1 ≤ p.count.val ∧ p.first.val + p.count.val ≤ 2^32 - 1 ∧
      p.lower_first.val + p.count.val ≤ 2^32 - 1) :
    mappings_overlap new_map e ⦃ r => r = false → ∀ p ∈ absFwd new_map, ¬ overlaps p e ⦄ := by
  unfold mappings_overlap
  simp only [lift, bind_tc_ok]
  obtain ⟨hecnt, hnwu, hnwl⟩ := he
  have hul := last_val e.first e.count hecnt (by simp [U32.max_eq]; omega)
  have hll := last_val e.lower_first e.count hecnt (by simp [U32.max_eq]; omega)
  exact mappings_overlap_loop_fun e new_map _ _ 0#u32 hlen (by simp) hecnt hul hll hwf (by simp)


/-! ## 5. The range form of downward soundness, for the re-map at 1072

`map_write` re-maps each `lower_first` with `map_id_range_down(parent,
lower_first, count)`, a *range* lookup. Its soundness is the same argument as
`down_sound` with `id2 = id + count - 1` exact (the check at 1033 gives
`lower_first + count ≤ W - 1`). -/

/-- **Named gap.** Range soundness of the downward lookup. Provable from
`base_loop_down_fun` (already general in `id2`), `bsearch_loop_sound` and
`cmp_map_id_zero_down`; the only new work is the `id2` arithmetic. -/
theorem down_range_sound (parent : UidGidMap) (hwf : WellFormed parent) (id count : U32)
    (hc : 1 ≤ count.val) (hnw : id.val + count.val ≤ 2^32 - 1) :
    map_id_range_down parent id count ⦃ v => v = ID_SENTINEL ∨
      ∃ p ∈ absFwd parent, inU p id.val ∧ inU p (id.val + count.val - 1) ∧ v.val = apDown p id.val ⦄ := by
  sorry

/-! ## 6. PRESERVE-LOWER on lists: the induction step, assembled -/

/-- What the line loop of `map_write` establishes about the extents it has
accepted, before the re-map (checks 1024, 1031, 1033, 1038, 1041). -/
structure PreRemap (L : List UidGidExtent) : Prop where
  count_pos : ∀ e ∈ L, 1 ≤ e.count.val
  nowrap_u : ∀ e ∈ L, e.first.val + e.count.val ≤ 2^32 - 1
  nowrap_l : ∀ e ∈ L, e.lower_first.val + e.count.val ≤ 2^32 - 1
  disj_u : ∀ e ∈ L, ∀ e' ∈ L, ∀ x, inU e x → inU e' x → e = e'
  disj_l : ∀ e ∈ L, ∀ e' ∈ L, ∀ y, inL e y → inL e' y → e = e'
  len_le : L.length ≤ 340

/-- The re-mapped list: every `lower_first` replaced by its image under the
parent, witnessed position by position. Stated with `getElem?` so no bound
proofs appear. -/
def Remapped (parent : UidGidMap) (L L' : List UidGidExtent) : Prop :=
  L'.length = L.length ∧
  ∀ (k : Nat) (e e' : UidGidExtent), L[k]? = some e → L'[k]? = some e' → ∃ p ∈ absFwd parent,
    inU p e.lower_first.val ∧ inU p (e.lower_first.val + e.count.val - 1) ∧
    e' = remapBy p e e'.lower_first ∧ e'.lower_first.val = apDown p e.lower_first.val

/-- **PRESERVE-LOWER, list level.** A `PreRemap` list re-mapped through a
`WellFormed` parent is pairwise disjoint in the lower coordinate — the clause
`mappings_overlap` could not check because it ran before the re-map. -/
theorem preserve_lower_list (parent : UidGidMap) (hwf : WellFormed parent)
    (L L' : List UidGidExtent) (hL : PreRemap L) (hR : Remapped parent L L')
    (hnodup : L.Nodup) :
    ∀ e ∈ L', ∀ e' ∈ L', ∀ y, inL e y → inL e' y → e = e' := by
  obtain ⟨hlen, hR⟩ := hR
  intro e he e' he' y hy hy'
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.1 he
  obtain ⟨k', hk'⟩ := List.mem_iff_getElem?.1 he'
  have hkL : k < L.length := by
    obtain ⟨hh, _⟩ := List.getElem?_eq_some_iff.1 hk; omega
  have hk'L : k' < L.length := by
    obtain ⟨hh, _⟩ := List.getElem?_eq_some_iff.1 hk'; omega
  obtain ⟨p, hp, hplo, hphi, heq, hlf⟩ := hR k L[k] e (List.getElem?_eq_getElem hkL) hk
  obtain ⟨p', hp', hplo', hphi', heq', hlf'⟩ := hR k' L[k'] e' (List.getElem?_eq_getElem hk'L) hk'
  by_cases hkk : k = k'
  · subst hkk; rw [hk] at hk'; injection hk'
  · exfalso
    have hne : L[k] ≠ L[k'] := by
      intro h; exact hkk ((List.Nodup.getElem_inj_iff hnodup).1 h)
    have hpre : ∀ z, inL L[k] z → inL L[k'] z → False := by
      intro z h1 h2
      exact hne (hL.disj_l _ (List.getElem_mem _) _ (List.getElem_mem _) z h1 h2)
    rw [heq] at hy; rw [heq'] at hy'
    exact remap_disjoint (fun y h1 h2 => hwf.disj_l p hp p' hp' y h1 h2)
      hplo hphi hplo' hphi' (hL.count_pos _ (List.getElem_mem _)) (hL.count_pos _ (List.getElem_mem _))
      hlf hlf' hpre y hy hy'

/-! ## 7. The remaining loop-level pieces, named -/

/-- Rebuild a `UidGidMap` from the field tuple the folded `map_write_body`
loops return. One line on purpose: Lean rejects a multi-line record literal
whose continuation is indented left of the opening brace. -/
def mkMap (a : Array UidGidExtent 5#usize) (a1 a2 : Array UidGidExtent 340#usize) (b b1 : Bool) (n : U32) : UidGidMap :=
  { extent := a, forward := a1, reverse := a2, forward_live := b, reverse_live := b1, nr_extents := n }

/-- The result tuple of the folded loops, as a map. -/
def resMap (r : I32 × Array UidGidExtent 5#usize × Array UidGidExtent 340#usize × Array UidGidExtent 340#usize × Bool × Bool × U32 × UidGidMap) : UidGidMap :=
  mkMap r.2.1 r.2.2.1 r.2.2.2.1 r.2.2.2.2.1 r.2.2.2.2.2.1 r.2.2.2.2.2.2.1

/-- **Named gap.** `sort_idmaps` (856) permutes the heap arm in place and fills
`reverse` with a permutation of it. Below 6 extents it is the identity. -/
theorem sort_idmaps_fun (m : UidGidMap) (hlen : m.nr_extents.val ≤ 340) :
    sort_idmaps m ⦃ r => r.1 = 0#i32 ∧ r.2.nr_extents = m.nr_extents ∧ r.2.extent = m.extent ∧
      (absFwd r.2).Perm (absFwd m) ∧
      (5 < m.nr_extents.val → r.2.reverse_live = true ∧ (absRev r.2).Perm (absFwd r.2)) ⦄ := by
  sorry

/-- **Named gap.** The re-map loop and the tail of `map_write_body` (1063–1102,
`map_write_body_loop0_loop0`): starting from an accumulated `new_map` whose
abstract map is a `PreRemap` list, either it fails with a negative code, or
it installs a `WellFormed` map into `map`. This is where
`preserve_lower_list` and `down_range_sound` are consumed. -/
theorem remap_install_fun (parent : UidGidMap) (hpwf : WellFormed parent)
    (a : Array UidGidExtent 5#usize) (a1 a2 : Array UidGidExtent 340#usize) (b b1 : Bool) (i : U32)
    (new_map : UidGidMap) (hL : PreRemap (absFwd new_map)) (hnodup : (absFwd new_map).Nodup)
    (hpos : 1 ≤ new_map.nr_extents.val) (ret : I32) :
    map_write_body_loop0_loop0 a a1 a2 b b1 i parent new_map.extent new_map.forward new_map.reverse
      new_map.forward_live new_map.reverse_live new_map.nr_extents ret 0#u32 ⦃ r =>
      r.1 < 0#i32 ∨ (r.1 = 0#i32 ∧ WellFormed (resMap r)) ⦄ := by
  sorry

/-- **Named gap.** The line loop of `map_write_body` (992–1049,
`map_write_body_loop0`): after `k` accepted lines the abstract map of `new_map`
is exactly those lines and is `PreRemap`. On exhaustion it hands off to
`remap_install_fun`; on any failed check it returns `-EINVAL`. -/
theorem lines_loop_fun (parent : UidGidMap) (hpwf : WellFormed parent)
    (map : UidGidMap) (lines : Slice UidGidExtent) (permitted : Bool)
    (new_map : UidGidMap) (i1 : Usize) (ret ret1 ret2 : I32)
    (hinv : absFwd new_map = lines.val.take i1.val ∧ PreRemap (absFwd new_map) ∧
      (absFwd new_map).Nodup ∧ new_map.nr_extents.val = i1.val) :
    map_write_body_loop0 ret ret1 map.extent map.forward map.reverse map.forward_live
      map.reverse_live map.nr_extents parent lines permitted new_map ret2 i1 ⦃ r =>
      r.1 < 0#i32 ∨ (r.1 = 0#i32 ∧ WellFormed (resMap r)) ⦄ := by
  sorry

/-! ## 8. F5 — PRESERVE, assembled -/

/-- **F5.** A successful `map_write` into an empty map installs a `WellFormed`
map, given a `WellFormed` parent (`A-PARENT-WF`). Assembled from the named
pieces above; `sorry`-free itself, but inherits their `sorry` until they are
closed. -/
theorem write_preserves_wf (parent : UidGidMap) (hpwf : WellFormed parent)
    (map : UidGidMap) (lines : Slice UidGidExtent) (cap_ok permitted : Bool)
    (r : I32 × UidGidMap) (h : map_write map parent lines cap_ok permitted = ok r)
    (hok : r.1 = 0#i32) : WellFormed r.2 := by
  sorry

/-- **F5, closed form.** Every map reachable from `init_user_ns` by a chain of
successful writes, each into a fresh child with the previous map as parent, is
`WellFormed`. This is the "induction on namespace depth" of SPEC §4.2/§4.5:
`init_user_ns_map_wf` is the base case and `write_preserves_wf` the step. -/
inductive Reachable : UidGidMap → Prop where
  | init (m : UidGidMap) (h : UidGidMap.init_user_ns_map = ok m) : Reachable m
  | write (parent : UidGidMap) (hp : Reachable parent) (map : UidGidMap)
      (lines : Slice UidGidExtent) (cap_ok permitted : Bool) (r : I32 × UidGidMap)
      (h : map_write map parent lines cap_ok permitted = ok r) (hok : r.1 = 0#i32) :
      Reachable r.2

theorem reachable_wf (m : UidGidMap) (h : Reachable m) : WellFormed m := by
  induction h with
  | init m h => exact init_user_ns_map_wf m h
  | write parent _ map lines cap_ok permitted r h hok ih =>
    exact write_preserves_wf parent ih map lines cap_ok permitted r h hok

end UidmapWritePath

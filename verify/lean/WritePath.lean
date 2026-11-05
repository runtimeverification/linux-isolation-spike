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

/-- Range containment from `cmp_map_id = 0` in the downward polarity: both the
key's first id and its last id lie in the extent. -/
theorem cmp_zero_inU_range {key : IdmapKey} {e : UidGidExtent}
    (hup : key.map_up = false) (hc : 1 ≤ key.count.val) (hnw : key.id.val + key.count.val ≤ 2^32 - 1)
    (hecnt : 1 ≤ e.count.val) (henw : e.first.val + e.count.val ≤ 2^32 - 1)
    (h : cmp_map_id key e = ok 0#i32) :
    inU e key.id.val ∧ inU e (key.id.val + key.count.val - 1) := by
  have hz := cmp_map_id_zero_down key e hup h
  have hlast := last_val e.first e.count hecnt (by simp [U32.max_eq]; omega)
  have hid2 := id2_val key.id key.count hc (by simp [U32.max_eq]; omega)
  unfold inU; constructor <;> scalar_tac

/-- Range soundness of the downward lookup, both paths: the same argument as
`down_sound` with `id2 = id + count - 1` exact. Whatever the re-map at 1072
gets back, if it is not the sentinel, it is the image of `lower_first` under a
parent extent that contains the *whole* lower range. -/
theorem down_range_sound (parent : UidGidMap) (hwf : WellFormed parent) (id count : U32)
    (hc : 1 ≤ count.val) (hnw : id.val + count.val ≤ 2^32 - 1) :
    map_id_range_down parent id count ⦃ v => v = ID_SENTINEL ∨
      ∃ p ∈ absFwd parent, inU p id.val ∧ inU p (id.val + count.val - 1) ∧ v.val = apDown p id.val ⦄ := by
  unfold map_id_range_down
  have h5 : (UScalar.cast .U32 UID_GID_MAP_MAX_BASE_EXTENTS).val = 5 := by
    simp [UID_GID_MAP_MAX_BASE_EXTENTS, UScalar.cast_val_eq]
  have hid2 := id2_val id count hc (by simp [U32.max_eq]; omega)
  simp only [lift, bind_tc_ok]
  split
  · rename_i hle
    have hle' : parent.nr_extents.val ≤ 5 := by scalar_tac
    have habs := absFwd_le5 hle'
    unfold map_id_range_down_base
    simp only [lift, bind_tc_ok]
    have hwf' : ∀ e ∈ parent.extent.val.take parent.nr_extents.val,
        1 ≤ e.count.val ∧ e.first.val + e.count.val ≤ 2^32 - 1 := by
      intro e he; rw [← habs] at he; exact ⟨hwf.count_pos e he, hwf.nowrap_u e he⟩
    step with base_loop_down_fun parent.nr_extents parent id _ 0#u32 hle' (by simp) hwf' (by simp) as ⟨ ext, hext ⟩
    rcases ext with _ | e
    · simp [spec_ok]
    · simp only [spec_ok]
      right
      obtain ⟨hmem, hin, hin2⟩ := hext
      rw [← habs] at hmem
      rw [hid2] at hin2
      exact ⟨e, hmem, hin, hin2, down_result_val e id hin (hwf.nowrap_l e hmem)⟩
  · rename_i hgt
    have hgt' : 5 < parent.nr_extents.val := by scalar_tac
    have habs := absFwd_gt5 hgt'
    unfold map_id_range_down_max
    have hcst : parent.nr_extents.val ≤ UScalar.max .Usize := by scalar_tac
    step with UScalar.cast_inBounds_spec .Usize parent.nr_extents hcst as ⟨ n, hn ⟩
    unfold bsearch_extent
    step with bsearch_loop_sound { map_up := false, id := id, count := count } parent.forward 0#usize n
      parent.nr_extents.val hwf.len_le (by simp; omega) as ⟨ ext, hext ⟩
    rcases ext with _ | e
    · simp [spec_ok]
    · simp only [spec_ok]
      right
      obtain ⟨hmem, hzero⟩ := hext e rfl
      rw [← habs] at hmem
      obtain ⟨hin, hin2⟩ := cmp_zero_inU_range rfl hc hnw (hwf.count_pos e hmem) (hwf.nowrap_u e hmem) hzero
      exact ⟨e, hmem, hin, hin2, down_result_val e id hin (hwf.nowrap_l e hmem)⟩

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

/-! ## 6b. The checks of the line loop, as list and scalar lemmas -/

/-- The C's no-wrap test at 1031/1033 (`(first + count) <= first` in `u32`),
read exactly: it accepts `count ≥ 1 ∧ first + count ≤ W - 1` and nothing else
(SPEC §1.2.1). -/
theorem nowrap_check_iff (first count : U32) :
    ¬ (core.num.U32.wrapping_add first count ≤ first) ↔
      (1 ≤ count.val ∧ first.val + count.val ≤ 2^32 - 1) := by
  have hv : (core.num.U32.wrapping_add first count).val = (first.val + count.val) % 4294967296 := by
    simp only [core.num.U32.wrapping_add, UScalar.wrapping_add_val_eq, UScalar.size,
      UScalarTy.U32_numBits_eq, Nat.reducePow]
  constructor
  · intro h; constructor <;> scalar_tac
  · rintro ⟨hc, hnw⟩ hle; scalar_tac

/-- an extent always overlaps itself (count ≥ 1) -/
theorem overlaps_self (e : UidGidExtent) (hc : 1 ≤ e.count.val) : overlaps e e :=
  Or.inl ⟨e.first.val, by unfold inU; omega, by unfold inU; omega⟩

/-- `PreRemap` extends by an extent that passed the checks and is disjoint from all. -/
theorem preRemap_append (L : List UidGidExtent) (e : UidGidExtent) (hL : PreRemap L)
    (hc : 1 ≤ e.count.val) (hnwu : e.first.val + e.count.val ≤ 2^32 - 1)
    (hnwl : e.lower_first.val + e.count.val ≤ 2^32 - 1)
    (hdisj : ∀ p ∈ L, ¬ overlaps p e) (hlen : L.length + 1 ≤ 340) : PreRemap (L ++ [e]) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, by simp; omega⟩
  · intro x hx; simp at hx; rcases hx with hx | rfl; exact hL.count_pos x hx; exact hc
  · intro x hx; simp at hx; rcases hx with hx | rfl; exact hL.nowrap_u x hx; exact hnwu
  · intro x hx; simp at hx; rcases hx with hx | rfl; exact hL.nowrap_l x hx; exact hnwl
  · intro x hx x' hx' y hy hy'
    simp at hx hx'
    rcases hx with hx | rfl <;> rcases hx' with hx' | rfl
    · exact hL.disj_u x hx x' hx' y hy hy'
    · exact absurd (Or.inl ⟨y, hy, hy'⟩) (hdisj x hx)
    · exact absurd (Or.inl ⟨y, hy', hy⟩) (hdisj x' hx')
    · rfl
  · intro x hx x' hx' y hy hy'
    simp at hx hx'
    rcases hx with hx | rfl <;> rcases hx' with hx' | rfl
    · exact hL.disj_l x hx x' hx' y hy hy'
    · exact absurd (Or.inr ⟨y, hy, hy'⟩) (hdisj x hx)
    · exact absurd (Or.inr ⟨y, hy', hy⟩) (hdisj x' hx')
    · rfl

theorem nodup_append_of_disjoint (L : List UidGidExtent) (e : UidGidExtent) (hnd : L.Nodup)
    (hc : 1 ≤ e.count.val) (hdisj : ∀ p ∈ L, ¬ overlaps p e) : (L ++ [e]).Nodup := by
  rw [List.nodup_append]
  refine ⟨hnd, List.nodup_singleton e, ?_⟩
  intro a ha b hb hab
  have hb' : b = e := List.mem_singleton.1 hb
  subst hb'; subst hab
  exact hdisj a ha (overlaps_self a hc)


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
-- Proof below generated by Gemini 4 Argon (gemini-4-argon), attempt 4, 2026-11-05; checked with axioms.sh + leanchecker.
theorem sort_key_spec (e : UidGidExtent) (by_lower_first : Bool) :
    sort_key e by_lower_first ⦃ v => v = if by_lower_first then e.lower_first else e.first ⦄ := by
  unfold sort_key; split <;> simp [spec_ok]

theorem perm_adj_swap {α : Type _} (l : List α) (n i j : Nat) (x y : α)
    (hij : j = i + 1) (hj : j < n) (hn : n ≤ l.length)
    (hx : l[i]? = some x) (hy : l[j]? = some y) :
    ((l.set j x).set i y).take n |>.Perm (l.take n) := by
  subst hij
  have hi_l : i < l.length := by omega
  have hi1_l : i + 1 < l.length := by omega
  rw [List.getElem?_eq_getElem hi_l, Option.some.injEq] at hx
  rw [List.getElem?_eq_getElem hi1_l, Option.some.injEq] at hy
  subst hx; subst hy
  have hsplit : ∀ (m : List α) (hm : n ≤ m.length),
      m.take n = m.take i ++ (m.drop i).take 2 ++ (m.drop (i + 2)).take (n - (i + 2)) := by
    intro m hm
    have h1 : m.take (i + 2) = m.take i ++ (m.drop i).take 2 := List.take_add
    have h2 : m.take (i + 2 + (n - (i + 2))) = m.take (i + 2) ++ (m.drop (i + 2)).take (n - (i + 2)) :=
      List.take_add
    rw [show i + 2 + (n - (i + 2)) = n by omega] at h2
    rw [h2, h1, List.append_assoc]
  set s := (l.set (i + 1) l[i]).set i l[i + 1]
  have hslen : s.length = l.length := by simp [s]
  rw [hsplit s (by omega), hsplit l hn]
  have hpre : s.take i = l.take i := by
    simp only [s]
    rw [take_set_of_le _ i i _ le_rfl, take_set_of_le _ (i + 1) i _ (by omega)]
  have hsuf : (s.drop (i + 2)).take (n - (i + 2)) = (l.drop (i + 2)).take (n - (i + 2)) := by
    apply List.ext_getElem (by simp [hslen])
    intro k hk1 hk2
    simp only [List.getElem_take, List.getElem_drop, s]
    rw [List.getElem_set_ne (by omega), List.getElem_set_ne (by omega)]
  have htwo : ∀ (m : List α) (h : i + 1 < m.length), (m.drop i).take 2 = [m[i], m[i + 1]] := by
    intro m h
    apply List.ext_getElem (by simp; omega)
    intro k hk1 hk2
    rcases k with _ | ⟨_ | k⟩
    · simp
    · simp
    · simp at hk2
  have hmid_l : (l.drop i).take 2 = [l[i], l[i + 1]] := htwo l hi1_l
  have hmid_s : (s.drop i).take 2 = [l[i + 1], l[i]] := by
    rw [htwo s (by omega)]
    have h0 : s[i] = l[i + 1] := by simp [s]
    have h1 : s[i + 1] = l[i] := by
      simp only [s]
      rw [List.getElem_set_ne (by omega), List.getElem_set_self]
    rw [h0, h1]
  rw [hpre, hsuf, hmid_s, hmid_l]
  exact ((List.Perm.refl (l.take i)).append (List.Perm.swap l[i] l[i + 1] [])).append
    (List.Perm.refl _)

theorem sort_sink_loop_fun (arr0 arr : Array UidGidExtent 340#usize) (by_lower_first : Bool)
    (n : Nat) (hn : n ≤ 340) (j : U32) (hj : j.val < n)
    (hperm : (arr.val.take n).Perm (arr0.val.take n)) :
    sort_sink_loop arr by_lower_first j ⦃ r => (r.val.take n).Perm (arr0.val.take n) ⦄ := by
  unfold sort_sink_loop
  apply loop.spec_decr_nat (fun p : Array UidGidExtent 340#usize × U32 => p.2.val)
    (fun p : Array UidGidExtent 340#usize × U32 =>
      p.2.val < n ∧ (p.1.val.take n).Perm (arr0.val.take n))
    _ _ _ _ ⟨hj, hperm⟩
  rintro ⟨a, j1⟩ ⟨hj1, hperm1⟩
  have hj1' : j1.val < n := hj1
  have hperm1' : (a.val.take n).Perm (arr0.val.take n) := hperm1
  dsimp only
  unfold sort_sink_loop.body
  have hlena : a.val.length = 340 := by simp [Array.length_eq]
  split
  · rename_i hjpos
    have hjpos' : 0 < j1.val := by scalar_tac
    step with @UScalar.sub_spec .U32 j1 1#u32 (by scalar_tac) as ⟨ i, hi, _ ⟩
    simp only [lift, bind_tc_ok]
    have hki := cast_usize_val i
    have hkj := cast_usize_val j1
    have hbi : (UScalar.cast .Usize i).val < a.length := by simp only [Array.length]; scalar_tac
    have hbj : (UScalar.cast .Usize j1).val < a.length := by simp only [Array.length]; scalar_tac
    step with Array.index_usize_spec a (UScalar.cast .Usize i) hbi as ⟨ uge, huge ⟩
    step with sort_key_spec uge by_lower_first as ⟨ k1, hk1 ⟩
    step with Array.index_usize_spec a (UScalar.cast .Usize j1) hbj as ⟨ uge1, huge1 ⟩
    step with sort_key_spec uge1 by_lower_first as ⟨ k2, hk2 ⟩
    split
    · step with Array.index_usize_spec a (UScalar.cast .Usize j1) hbj as ⟨ tmp, htmp ⟩
      step with Array.index_usize_spec a (UScalar.cast .Usize i) hbi as ⟨ uge2, huge2 ⟩
      step with Array.update_spec a (UScalar.cast .Usize j1) uge2 hbj as ⟨ arr1, harr1 ⟩
      have hbi1 : (UScalar.cast .Usize i).val < arr1.length := by simp only [Array.length]; scalar_tac
      step with Array.update_spec arr1 (UScalar.cast .Usize i) tmp hbi1 as ⟨ a2, ha2 ⟩
      have hbi' : (UScalar.cast .Usize i).val < a.val.length := by omega
      have hbj' : (UScalar.cast .Usize j1).val < a.val.length := by omega
      have hswap : (a2.val.take n).Perm (a.val.take n) := by
        rw [ha2, harr1, Array.set_val_eq, Array.set_val_eq]
        exact perm_adj_swap a.val n (UScalar.cast .Usize i).val (UScalar.cast .Usize j1).val uge2 tmp
          (by omega) (by omega) (by omega)
          (by rw [List.getElem?_eq_getElem hbi', huge2])
          (by rw [List.getElem?_eq_getElem hbj', htmp])
      refine ⟨by scalar_tac, hswap.trans hperm1', by scalar_tac⟩
    · exact (spec_ok _).mpr hperm1'
  · exact (spec_ok _).mpr hperm1'

theorem sort_extents_loop_fun (arr0 arr : Array UidGidExtent 340#usize)
    (n : U32) (by_lower_first : Bool) (i : U32) (hn : n.val ≤ 340)
    (hperm : (arr.val.take n.val).Perm (arr0.val.take n.val)) :
    sort_extents_loop arr n by_lower_first i ⦃ r => (r.val.take n.val).Perm (arr0.val.take n.val) ⦄ := by
  unfold sort_extents_loop
  apply loop.spec_decr_nat (fun p : Array UidGidExtent 340#usize × U32 => n.val - p.2.val)
    (fun p : Array UidGidExtent 340#usize × U32 => (p.1.val.take n.val).Perm (arr0.val.take n.val))
    _ _ _ _ hperm
  rintro ⟨a, i1⟩ hperm1
  have hperm1' : (a.val.take n.val).Perm (arr0.val.take n.val) := hperm1
  dsimp only
  unfold sort_extents_loop.body
  split
  · rename_i hlt
    have hlt' : i1.val < n.val := by scalar_tac
    unfold sort_sink
    step with sort_sink_loop_fun arr0 a by_lower_first n.val hn i1 hlt' hperm1' as ⟨ arr1, harr1 ⟩
    step with @UScalar.add_spec .U32 i1 1#u32 (by scalar_tac) as ⟨ i2, hi2 ⟩
    exact ⟨harr1, by scalar_tac⟩
  · exact (spec_ok _).mpr hperm1'

theorem sort_extents_fun (arr : Array UidGidExtent 340#usize) (n : U32) (by_lower_first : Bool)
    (hn : n.val ≤ 340) :
    sort_extents arr n by_lower_first ⦃ r => (r.val.take n.val).Perm (arr.val.take n.val) ⦄ := by
  unfold sort_extents
  exact sort_extents_loop_fun arr arr n by_lower_first 1#u32 hn (List.Perm.refl _)

theorem sort_idmaps_loop_fun (a a1 : Array UidGidExtent 340#usize) (n i : U32)
    (hn : n.val ≤ 340) (hi : i.val ≤ n.val)
    (hpre : a1.val.take i.val = a.val.take i.val) :
    sort_idmaps_loop a a1 n i ⦃ r => r.val.take n.val = a.val.take n.val ⦄ := by
  unfold sort_idmaps_loop
  apply loop.spec_decr_nat (fun p : Array UidGidExtent 340#usize × U32 => n.val - p.2.val)
    (fun p : Array UidGidExtent 340#usize × U32 =>
      p.2.val ≤ n.val ∧ p.1.val.take p.2.val = a.val.take p.2.val)
    _ _ _ _ ⟨hi, hpre⟩
  rintro ⟨a2, i1⟩ ⟨hi1, hpre⟩
  have hi1' : i1.val ≤ n.val := hi1
  have hpre1 : a2.val.take i1.val = a.val.take i1.val := hpre
  dsimp only
  unfold sort_idmaps_loop.body
  split
  · rename_i hlt
    have hlt' : i1.val < n.val := by scalar_tac
    have hlena : a.val.length = 340 := by simp [Array.length_eq]
    have hlena2 : a2.val.length = 340 := by simp [Array.length_eq]
    simp only [lift, bind_tc_ok]
    have hk := cast_usize_val i1
    have hb1 : (UScalar.cast .Usize i1).val < a.length := by simp only [Array.length]; scalar_tac
    step with Array.index_usize_spec a (UScalar.cast .Usize i1) hb1 as ⟨ uge, huge ⟩
    have hb2 : (UScalar.cast .Usize i1).val < a2.length := by simp only [Array.length]; scalar_tac
    step with Array.update_spec a2 (UScalar.cast .Usize i1) uge hb2 as ⟨ a3, ha3 ⟩
    step with @UScalar.add_spec .U32 i1 1#u32 (by scalar_tac) as ⟨ i2, hi2 ⟩
    refine ⟨by scalar_tac, ?_, by scalar_tac⟩
    have hpre' : a2.val.take (UScalar.cast .Usize i1).val = a.val.take (UScalar.cast .Usize i1).val := by
      rw [hk]; exact hpre1
    have hi2' : i2.val = (UScalar.cast .Usize i1).val + 1 := by rw [hi2, hk]
    rw [hi2', ha3, Array.set_val_eq, take_set_succ _ _ _ (by omega), hpre', huge,
        ← take_add_one_of_getElem a.val (UScalar.cast .Usize i1).val (by omega)]
  · rename_i hge
    have : i1.val = n.val := by scalar_tac
    apply (spec_ok _).mpr
    rw [← this]; exact hpre1

theorem sort_idmaps_fun (m : UidGidMap) (hlen : m.nr_extents.val ≤ 340) :
    sort_idmaps m ⦃ r => r.1 = 0#i32 ∧ r.2.nr_extents = m.nr_extents ∧ r.2.extent = m.extent ∧
      (absFwd r.2).Perm (absFwd m) ∧
      (5 < m.nr_extents.val → r.2.reverse_live = true ∧ (absRev r.2).Perm (absFwd r.2)) ⦄ := by
  unfold sort_idmaps
  have h5 : (UScalar.cast .U32 UID_GID_MAP_MAX_BASE_EXTENTS).val = 5 := by
    simp [UID_GID_MAP_MAX_BASE_EXTENTS, UScalar.cast_val_eq]
  simp only [lift, bind_tc_ok]
  split
  · rename_i hle
    have hle' : m.nr_extents.val ≤ 5 := by scalar_tac
    apply (spec_ok _).mpr
    refine ⟨rfl, rfl, rfl, List.Perm.refl _, fun h => by omega⟩
  · rename_i hgt
    have hgt' : 5 < m.nr_extents.val := by scalar_tac
    step with sort_extents_fun m.forward m.nr_extents false hlen as ⟨ a, ha ⟩
    step with sort_idmaps_loop_fun a m.reverse m.nr_extents 0#u32 hlen (by simp) (by simp) as ⟨ a1, ha1 ⟩
    step with sort_extents_fun a1 m.nr_extents true hlen as ⟨ a2, ha2 ⟩
    refine ⟨?_, fun _ => ?_⟩
    · rw [absFwd_gt5 (by simp; exact hgt'), absFwd_gt5 hgt']
      exact ha
    · rw [absRev_gt5 (by simp; exact hgt'), absFwd_gt5 (by simp; exact hgt')]
      dsimp only
      rw [ha1] at ha2
      exact ha2

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

set_option maxHeartbeats 2000000 in
/-- **The line loop of `map_write_body`** (992–1049, `map_write_body_loop0`):
after `k` accepted lines the abstract map of `new_map` is exactly those lines,
is `PreRemap` and duplicate-free, and the exact 340 boundary of 1041 is
carried as `i1 < 340 ∨ i1 = len`. On exhaustion it hands off to
`remap_install_fun`; on any failed check it returns the negative code it was
given. Proved; inherits the `sorry` of `remap_install_fun` only. -/
theorem lines_loop_fun (parent : UidGidMap) (hpwf : WellFormed parent)
    (map : UidGidMap) (lines : Slice UidGidExtent) (permitted : Bool)
    (new_map : UidGidMap) (i1 : Usize) (ret ret1 ret2 : I32)
    (hret : ret < 0#i32) (hret1 : ret1 < 0#i32) (hret2 : ret2 < 0#i32)
    (hinv : absFwd new_map = lines.val.take i1.val ∧ PreRemap (absFwd new_map) ∧
      (absFwd new_map).Nodup ∧ new_map.nr_extents.val = i1.val ∧
      (i1.val < 340 ∨ i1.val = lines.val.length) ∧ i1.val ≤ lines.val.length) :
    map_write_body_loop0 ret ret1 map.extent map.forward map.reverse map.forward_live
      map.reverse_live map.nr_extents parent lines permitted new_map ret2 i1 ⦃ r =>
      r.1 < 0#i32 ∨ (r.1 = 0#i32 ∧ WellFormed (resMap r)) ⦄ := by
  unfold map_write_body_loop0
  apply loop.spec_decr_nat (fun p : UidGidMap × I32 × Usize => lines.val.length - p.2.2.val)
    (fun p : UidGidMap × I32 × Usize => p.2.1 < 0#i32 ∧ absFwd p.1 = lines.val.take p.2.2.val ∧
      PreRemap (absFwd p.1) ∧ (absFwd p.1).Nodup ∧ p.1.nr_extents.val = p.2.2.val ∧
      (p.2.2.val < 340 ∨ p.2.2.val = lines.val.length) ∧ p.2.2.val ≤ lines.val.length)
    _ _ _ _ (And.intro hret2 hinv)
  intro p hinv
  obtain ⟨nm, ret3, i2⟩ := p
  obtain ⟨hr3, habs, hpre, hnd, hnr, hbound, hle⟩ := hinv
  dsimp only at hr3 habs hpre hnd hnr hbound hle ⊢
  unfold map_write_body_loop0.body
  have hlenL : (absFwd nm).length = i2.val := by
    rw [habs, List.length_take]; omega
  by_cases hlt : i2 < Slice.len lines
  · rw [if_pos hlt]
    have hlt' : i2.val < lines.val.length := by simp [Slice.len] at hlt; scalar_tac
    have hb : i2.val < lines.length := by simp [Slice.length]; exact hlt'
    step with Slice.index_usize_spec lines i2 hb as ⟨ extent, hext ⟩
    step with @UScalar.add_spec .Usize i2 1#usize (by scalar_tac) as ⟨ i3, hi3 ⟩
    simp only [lift, bind_tc_ok]
    split
    · exact (spec_ok _).mpr (Or.inl hr3)
    split
    · exact (spec_ok _).mpr (Or.inl hr3)
    split
    · exact (spec_ok _).mpr (Or.inl hr3)
    rename_i hwu
    split
    · exact (spec_ok _).mpr (Or.inl hr3)
    rename_i hwl
    obtain ⟨hc, hnwu⟩ := (nowrap_check_iff extent.first extent.count).1 hwu
    obtain ⟨_, hnwl⟩ := (nowrap_check_iff extent.lower_first extent.count).1 hwl
    have hpwf' : ∀ p ∈ absFwd nm, 1 ≤ p.count.val ∧ p.first.val + p.count.val ≤ 2^32 - 1 ∧
        p.lower_first.val + p.count.val ≤ 2^32 - 1 :=
      fun p hp => ⟨hpre.count_pos p hp, hpre.nowrap_u p hp, hpre.nowrap_l p hp⟩
    have hnr340 : nm.nr_extents.val ≤ 340 := by omega
    step with mappings_overlap_fun nm extent hnr340 ⟨hc, hnwu, hnwl⟩ hpwf' as ⟨ b2, hb2 ⟩
    split
    · exact (spec_ok _).mpr (Or.inl hr3)
    rename_i hb2f
    have hdisj : ∀ p ∈ absFwd nm, ¬ overlaps p extent := hb2 (by simpa using hb2f)
    step with @UScalar.add_spec .U32 nm.nr_extents 1#u32 (by scalar_tac) as ⟨ i7, hi7 ⟩
    have h340 : (UScalar.cast .U32 UID_GID_MAP_MAX_EXTENTS).val = 340 := by
      simp [UID_GID_MAP_MAX_EXTENTS, UScalar.cast_val_eq]
    -- the invariant after a successful insert, shared by both insert branches
    have hstep : ∀ (nm' : UidGidMap), nm'.nr_extents.val = nm.nr_extents.val + 1 →
        absFwd nm' = absFwd nm ++ [extent] →
        (absFwd nm' = lines.val.take i3.val ∧ PreRemap (absFwd nm') ∧ (absFwd nm').Nodup ∧
          nm'.nr_extents.val = i3.val) := by
      intro nm' hn' habs'
      refine ⟨?_, ?_, ?_, by omega⟩
      · rw [habs', habs, hi3, hext, ← take_add_one_of_getElem lines.val i2.val hlt']
      · rw [habs']; exact preRemap_append _ _ hpre hc hnwu hnwl hdisj (by omega)
      · rw [habs']; exact nodup_append_of_disjoint _ _ hnd hc hdisj
    split
    · rename_i h339
      have h339' : nm.nr_extents.val = 339 := by scalar_tac
      split
      · exact (spec_ok _).mpr (Or.inl hr3)
      · rename_i hnonext
        step with insert_extent_fun nm extent (by omega) as ⟨ ie1, nm', hie1, hn', habs', hrev ⟩
        split
        · exfalso; rename_i hneg; scalar_tac
        · obtain ⟨h1, h2, h3, h4⟩ := hstep nm' hn' habs'
          apply (spec_ok _).mpr
          refine ⟨hret1, h1, h2, h3, h4, ?_, by scalar_tac, by scalar_tac⟩
          show i3.val < 340 ∨ i3.val = lines.val.length
          right; simp [Slice.len] at hnonext; scalar_tac
    · rename_i hne339
      have hlt340 : nm.nr_extents.val < 339 := by
        rcases hbound with hb | hb
        · have : nm.nr_extents.val ≠ 339 := by intro h; apply hne339; apply UScalar.eq_of_val_eq; scalar_tac
          omega
        · omega
      step with insert_extent_fun nm extent (by omega) as ⟨ ie1, nm', hie1, hn', habs', hrev ⟩
      split
      · exfalso; rename_i hneg; scalar_tac
      · obtain ⟨h1, h2, h3, h4⟩ := hstep nm' hn' habs'
        apply (spec_ok _).mpr
        refine ⟨hret1, h1, h2, h3, h4, ?_, by scalar_tac, by scalar_tac⟩
        show i3.val < 340 ∨ i3.val = lines.val.length
        left; scalar_tac
  · -- lines exhausted
    rw [if_neg hlt]
    split
    · exact (spec_ok _).mpr (Or.inl hr3)
    · rename_i hnz
      split
      · have hpos : 1 ≤ nm.nr_extents.val := by scalar_tac
        step with remap_install_fun parent hpwf map.extent map.forward map.reverse map.forward_live
          map.reverse_live map.nr_extents nm hpre hnd hpos ret as ⟨ q1, q2, q3, q4, q5, q6, q7, q8, hres ⟩
        apply (spec_ok _).mpr
        exact hres
      · exact (spec_ok _).mpr (Or.inl hret)

/-! ## 8. F5 — PRESERVE, assembled -/

set_option maxHeartbeats 2000000 in
/-- **F5.** A successful `map_write` installs a `WellFormed` map, given a
`WellFormed` parent (`A-PARENT-WF`). No hypothesis on `map` is needed: success
itself forces the write-once check (980) and the capability check (986) to
have passed. Proved from `lines_loop_fun`; inherits its `sorry`. -/
theorem write_preserves_wf (parent : UidGidMap) (hpwf : WellFormed parent)
    (map : UidGidMap) (lines : Slice UidGidExtent) (cap_ok permitted : Bool)
    (r : I32 × UidGidMap) (h : map_write map parent lines cap_ok permitted = ok r)
    (hok : r.1 = 0#i32) : WellFormed r.2 := by
  unfold map_write at h
  simp only [UidGidMap.zeroed, bind_tc_ok] at h
  unfold map_write_body at h
  simp only [EPERM, EINVAL] at h
  have hneg1 : (-. (1#i32)) = ok (-1)#i32 := by rfl
  have hneg2 : (-. (22#i32)) = ok (-22)#i32 := by rfl
  have hm1 : ((-1)#i32) < 0#i32 := by scalar_tac
  set z : UidGidExtent := { first := 0#u32, lower_first := 0#u32, count := 0#u32 } with hz
  set nm0 : UidGidMap := { extent := Array.repeat 5#usize z, forward := Array.repeat 340#usize z, reverse := Array.repeat 340#usize z, forward_live := false, reverse_live := false, nr_extents := 0#u32 } with hnm0
  rw [hneg1] at h
  simp only [bind_tc_ok] at h
  -- the tail of map_write applied to a concrete (ret, map1, new_map1) triple, spelled out
  have tail : ∀ (c : I32) (m1 nm1 : UidGidMap), c < 0#i32 →
      (if c < 0#i32 then (do
          let i ← lift (UScalar.cast .U32 UID_GID_MAP_MAX_BASE_EXTENTS)
          if nm1.nr_extents > i then ok (c, { m1 with forward_live := false, reverse_live := false, nr_extents := 0#u32 })
          else ok (c, m1))
        else ok (c, m1)) = ok r → r.1 = 0#i32 → False := by
    intro c m1 nm1 hc h hok
    rw [if_pos hc] at h
    simp only [lift, bind_tc_ok] at h
    split at h <;> simp only [ok.injEq] at h <;> subst h <;> dsimp only at hok <;> scalar_tac
  split at h
  · -- map already written: ret = -1
    simp only [bind_tc_ok] at h
    exact (tail ((-1)#i32) map nm0 hm1 h hok).elim
  · split at h
    · -- cap_ok: the real path
      rw [hneg2] at h
      simp only [bind_tc_ok] at h
      have habs0 : absFwd nm0 = [] := by simp [absFwd, hnm0]
      have hinv : absFwd nm0 = lines.val.take (0#usize).val ∧ PreRemap (absFwd nm0) ∧
          (absFwd nm0).Nodup ∧ nm0.nr_extents.val = (0#usize).val ∧
          ((0#usize).val < 340 ∨ (0#usize).val = lines.val.length) ∧ (0#usize).val ≤ lines.val.length := by
        refine ⟨by simp [habs0], ?_, by simp [habs0], by simp [hnm0], by simp, by simp⟩
        rw [habs0]; exact ⟨by simp, by simp, by simp, by simp, by simp, by simp⟩
      have HL := lines_loop_fun parent hpwf map lines permitted nm0 (0#usize) ((-1)#i32) ((-22)#i32) ((-22)#i32)
        (hret := by scalar_tac) (hret1 := by scalar_tac) (hret2 := by scalar_tac) (hinv := hinv)
      obtain ⟨v, hv, hpost⟩ := spec_imp_exists HL
      obtain ⟨i, a, a1, a2, b, b1, i1, nm⟩ := v
      simp only [resMap, mkMap] at hpost
      rw [hv] at h
      simp only [bind_tc_ok] at h
      rcases hpost with hneg | ⟨hzero, hwf⟩
      · exact (tail i (mkMap a a1 a2 b b1 i1) nm hneg h hok).elim
      · subst hzero
        have h' : (if (0#i32) < 0#i32 then (do
            let j ← lift (UScalar.cast .U32 UID_GID_MAP_MAX_BASE_EXTENTS)
            if nm.nr_extents > j then ok ((0#i32), { (mkMap a a1 a2 b b1 i1) with forward_live := false, reverse_live := false, nr_extents := 0#u32 })
            else ok ((0#i32), mkMap a a1 a2 b b1 i1))
          else ok ((0#i32), mkMap a a1 a2 b b1 i1)) = ok r := h
        have hnl : ¬ ((0#i32) < (0#i32)) := by scalar_tac
        rw [if_neg hnl] at h'
        simp only [ok.injEq] at h'
        subst h'
        exact hwf
    · -- !cap_ok: ret = -1
      simp only [bind_tc_ok] at h
      exact (tail ((-1)#i32) map nm0 hm1 h hok).elim

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

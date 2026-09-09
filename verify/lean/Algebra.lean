-- SPDX-License-Identifier: GPL-2.0
import Spec
import Safety
/-!
# Functional properties of the lookups: F1 (soundness), F2 `INJECTIVITY`,
F3 `ROUNDTRIP` (SPEC.md §4.2, §4.3)

Scope of this file: the single-id forms `map_id_down` / `map_id_up`
(`count = 1`), which are what `make_kuid` / `from_kuid` call and what
`INJECTIVITY` and `ROUNDTRIP` are about. General ranges are step 5.

Structure:
- `*_sound`: whatever a lookup returns, if it is not the sentinel, it came
  from an extent of the active arm that contains the input. Proved for BOTH
  paths — the binary search only ever returns an element for which
  `cmp_map_id` said `0`, and that needs no sortedness.
- `*_complete_le5`: below 6 extents, the linear scan finds a containing extent
  if one exists.
- `bsearch_complete`: the same for the binary search. **Stated with `sorry`**:
  it needs `SortedArms`, and it is the heart of F4 `AGREEMENT` (step 5).
- F2 needs soundness only and is `sorry`-free for both paths.
- F3 splits: `roundtrip_sound` ("never an unrelated id") is `sorry`-free for
  both paths; `roundtrip_complete` ("and it is found") is `sorry`-free below 6
  and rests on `bsearch_complete` above.
-/
open Aeneas Aeneas.Std Result ControlFlow WP
open uidmap UidmapSpec UidmapSafety

namespace UidmapAlgebra

instance : Inhabited UidGidExtent := ⟨{ first := 0#u32, lower_first := 0#u32, count := 0#u32 }⟩

/-! ## Scalar bridges -/

/-- `id + 1 - 1 = id` in `u32`, the `id2` of every single-id lookup. -/
theorem id2_one_val (id : U32) :
    (core.num.U32.wrapping_sub (core.num.U32.wrapping_add id 1#u32) 1#u32).val = id.val := by
  simp only [core.num.U32.wrapping_add, core.num.U32.wrapping_sub,
             UScalar.wrapping_add_val_eq, UScalar.wrapping_sub_val_eq, UScalar.size,
             UScalarTy.U32_numBits_eq, Nat.reducePow]
  have h1 : (1#u32).val = 1 := by simp
  rw [h1]
  scalar_tac

/-- The result arithmetic of `map_id_range_down` (:331), exact under
`inU` and `nowrap_l`. -/
theorem down_result_val (e : UidGidExtent) (id : U32) (hx : inU e id.val)
    (hnw : e.lower_first.val + e.count.val ≤ 2^32 - 1) :
    (core.num.U32.wrapping_add (core.num.U32.wrapping_sub id e.first) e.lower_first).val
      = apDown e id.val := by
  unfold inU apDown at *
  simp only [core.num.U32.wrapping_add, core.num.U32.wrapping_sub,
             UScalar.wrapping_add_val_eq, UScalar.wrapping_sub_val_eq, UScalar.size,
             UScalarTy.U32_numBits_eq, Nat.reducePow]
  scalar_tac

/-- The result arithmetic of `map_id_range_up` (:397). -/
theorem up_result_val (e : UidGidExtent) (id : U32) (hy : inL e id.val)
    (hnw : e.first.val + e.count.val ≤ 2^32 - 1) :
    (core.num.U32.wrapping_add (core.num.U32.wrapping_sub id e.lower_first) e.first).val
      = apUp e id.val := by
  unfold inL apUp at *
  simp only [core.num.U32.wrapping_add, core.num.U32.wrapping_sub,
             UScalar.wrapping_add_val_eq, UScalar.wrapping_sub_val_eq, UScalar.size,
             UScalarTy.U32_numBits_eq, Nat.reducePow]
  scalar_tac

theorem sentinel_val : ID_SENTINEL.val = 2^32 - 1 := by simp [ID_SENTINEL]

/-! ## List helpers on `take` -/

theorem mem_take_of_getElem {α} (l : List α) (n k : Nat) (hk : k < n) (hkl : k < l.length) :
    l[k] ∈ l.take n := by
  rw [List.mem_iff_getElem]
  refine ⟨k, ?_, ?_⟩
  · simp; omega
  · simp [List.getElem_take]

theorem forall_take_succ {α} (l : List α) (k : Nat) (hk : k < l.length) (P : α → Prop)
    (hprev : ∀ e ∈ l.take k, P e) (hcur : P l[k]) : ∀ e ∈ l.take (k + 1), P e := by
  intro e he
  rw [List.take_add_one] at he
  simp only [List.mem_append, List.getElem?_eq_getElem hk, Option.toList_some,
             List.mem_singleton] at he
  rcases he with h | h
  · exact hprev e h
  · subst h; exact hcur

/-! ## `cmp_map_id`, functionally -/

/-- If `cmp_map_id` says `0` in the downward polarity, both ends of the key's
range lie in `[first, last]`, with `last` and `id2` the C's wrapping values. -/
theorem cmp_map_id_zero_down (key : IdmapKey) (el : UidGidExtent) (hup : key.map_up = false)
    (h : cmp_map_id key el = ok 0#i32) :
    key.id ≥ el.first ∧
    key.id ≤ core.num.U32.wrapping_sub (core.num.U32.wrapping_add el.first el.count) 1#u32 ∧
    core.num.U32.wrapping_sub (core.num.U32.wrapping_add key.id key.count) 1#u32 ≥ el.first ∧
    core.num.U32.wrapping_sub (core.num.U32.wrapping_add key.id key.count) 1#u32 ≤
      core.num.U32.wrapping_sub (core.num.U32.wrapping_add el.first el.count) 1#u32 := by
  unfold cmp_map_id at h
  simp only [lift, bind_tc_ok, hup, Bool.false_eq_true, if_false] at h
  split_ifs at h with h1 h2 h3 h4 <;> simp only [ok.injEq] at h
  · exact ⟨h1, h2, h3, h4⟩
  all_goals (exfalso; scalar_tac)

/-- The same in the upward polarity: the interval is `[lower_first, last]`. -/
theorem cmp_map_id_zero_up (key : IdmapKey) (el : UidGidExtent) (hup : key.map_up = true)
    (h : cmp_map_id key el = ok 0#i32) :
    key.id ≥ el.lower_first ∧
    key.id ≤ core.num.U32.wrapping_sub (core.num.U32.wrapping_add el.lower_first el.count) 1#u32 ∧
    core.num.U32.wrapping_sub (core.num.U32.wrapping_add key.id key.count) 1#u32 ≥ el.lower_first ∧
    core.num.U32.wrapping_sub (core.num.U32.wrapping_add key.id key.count) 1#u32 ≤
      core.num.U32.wrapping_sub (core.num.U32.wrapping_add el.lower_first el.count) 1#u32 := by
  unfold cmp_map_id at h
  simp only [lift, bind_tc_ok, hup, if_true] at h
  split_ifs at h with h1 h2 h3 h4 <;> simp only [ok.injEq] at h
  · exact ⟨h1, h2, h3, h4⟩
  all_goals (exfalso; scalar_tac)

/-! ## The `≤ 5` linear scans, functionally -/

/-- The downward base scan on a single id: whatever it returns is right, and
`none` means nothing contains the id. Precondition on the array prefix only:
each extent has `count ≥ 1` and `first + count ≤ W - 1`, so `last` is exact. -/
theorem base_loop_down_fun (extents : U32) (m : UidGidMap) (id id2 idx : U32)
    (hext : extents.val ≤ 5) (hidx : idx.val ≤ extents.val)
    (hwf : ∀ e ∈ m.extent.val.take extents.val, 1 ≤ e.count.val ∧ e.first.val + e.count.val ≤ 2^32 - 1)
    (hpre : ∀ e ∈ m.extent.val.take idx.val, ¬ (inU e id.val ∧ inU e id2.val)) :
    map_id_range_down_base_loop extents m id idx id2 ⦃ r =>
      match r with
      | some e => e ∈ m.extent.val.take extents.val ∧ inU e id.val ∧ inU e id2.val
      | none => ∀ e ∈ m.extent.val.take extents.val, ¬ (inU e id.val ∧ inU e id2.val) ⦄ := by
  unfold map_id_range_down_base_loop
  apply loop.spec_decr_nat (fun idx : U32 => extents.val - idx.val)
    (fun idx : U32 => idx.val ≤ extents.val ∧ ∀ e ∈ m.extent.val.take idx.val, ¬ (inU e id.val ∧ inU e id2.val))
    _ _ _ _ (And.intro hidx hpre)
  intro idx hinv
  obtain ⟨hidx, hpre⟩ := hinv
  unfold map_id_range_down_base_loop.body
  split
  · rename_i hlt
    have hlt' : idx.val < extents.val := by scalar_tac
    have hc : idx.val ≤ UScalar.max .Usize := by scalar_tac
    step with UScalar.cast_inBounds_spec .Usize idx hc as ⟨ i, hi ⟩
    have hlen5 : m.extent.val.length = 5 := by simp [Array.length_eq]
    have hbound : i.val < m.extent.length := by simp [Array.length]; scalar_tac
    step with Array.index_usize_spec m.extent i hbound as ⟨ e, he ⟩
    have hmem : e ∈ m.extent.val.take extents.val := by
      rw [he]; exact mem_take_of_getElem _ _ _ (by omega) (by omega)
    obtain ⟨hcnt, hnw⟩ := hwf e hmem
    have hlast := last_val e.first e.count hcnt (by simp [U32.max_eq]; omega)
    simp only [lift, bind_tc_ok]
    have hnext : ∀ (hnot : ¬ (inU e id.val ∧ inU e id2.val)),
        (∀ e' ∈ m.extent.val.take (idx.val + 1), ¬ (inU e' id.val ∧ inU e' id2.val)) := by
      intro hnot
      have hpre_i : ∀ e' ∈ m.extent.val.take i.val, ¬ (inU e' id.val ∧ inU e' id2.val) := by
        rw [hi]; exact hpre
      have := forall_take_succ m.extent.val i.val (by omega)
        (fun e' => ¬ (inU e' id.val ∧ inU e' id2.val)) hpre_i (by rw [← he]; exact hnot)
      rw [hi] at this; exact this
    split_ifs with h1 h2 h3 h4
    · -- all four comparisons hold: e contains id
      simp only [spec_ok]
      refine ⟨hmem, ?_, ?_⟩ <;> unfold inU <;> scalar_tac
    all_goals
      have hnot : ¬ (inU e id.val ∧ inU e id2.val) := by unfold inU; scalar_tac
      step with @UScalar.add_spec .U32 idx 1#u32 (by scalar_tac) as ⟨ idx1, hidx1 ⟩
      all_goals (try simp only [spec_ok, and_assoc])
      refine ⟨by scalar_tac, ?_, by scalar_tac⟩
      rw [hidx1]; exact hnext hnot
  · simp only [spec_ok]
    rename_i hge
    have : extents.val ≤ idx.val := by scalar_tac
    have heq : idx.val = extents.val := by omega
    rw [heq] at hpre; exact hpre

theorem base_loop_up_fun (extents : U32) (m : UidGidMap) (id id2 idx : U32)
    (hext : extents.val ≤ 5) (hidx : idx.val ≤ extents.val)
    (hwf : ∀ e ∈ m.extent.val.take extents.val, 1 ≤ e.count.val ∧ e.lower_first.val + e.count.val ≤ 2^32 - 1)
    (hpre : ∀ e ∈ m.extent.val.take idx.val, ¬ (inL e id.val ∧ inL e id2.val)) :
    map_id_range_up_base_loop extents m id idx id2 ⦃ r =>
      match r with
      | some e => e ∈ m.extent.val.take extents.val ∧ inL e id.val ∧ inL e id2.val
      | none => ∀ e ∈ m.extent.val.take extents.val, ¬ (inL e id.val ∧ inL e id2.val) ⦄ := by
  unfold map_id_range_up_base_loop
  apply loop.spec_decr_nat (fun idx : U32 => extents.val - idx.val)
    (fun idx : U32 => idx.val ≤ extents.val ∧ ∀ e ∈ m.extent.val.take idx.val, ¬ (inL e id.val ∧ inL e id2.val))
    _ _ _ _ (And.intro hidx hpre)
  intro idx hinv
  obtain ⟨hidx, hpre⟩ := hinv
  unfold map_id_range_up_base_loop.body
  split
  · rename_i hlt
    have hlt' : idx.val < extents.val := by scalar_tac
    have hc : idx.val ≤ UScalar.max .Usize := by scalar_tac
    step with UScalar.cast_inBounds_spec .Usize idx hc as ⟨ i, hi ⟩
    have hlen5 : m.extent.val.length = 5 := by simp [Array.length_eq]
    have hbound : i.val < m.extent.length := by simp [Array.length]; scalar_tac
    step with Array.index_usize_spec m.extent i hbound as ⟨ e, he ⟩
    have hmem : e ∈ m.extent.val.take extents.val := by
      rw [he]; exact mem_take_of_getElem _ _ _ (by omega) (by omega)
    obtain ⟨hcnt, hnw⟩ := hwf e hmem
    have hlast := last_val e.lower_first e.count hcnt (by simp [U32.max_eq]; omega)
    simp only [lift, bind_tc_ok]
    have hnext : ∀ (hnot : ¬ (inL e id.val ∧ inL e id2.val)),
        (∀ e' ∈ m.extent.val.take (idx.val + 1), ¬ (inL e' id.val ∧ inL e' id2.val)) := by
      intro hnot
      have hpre_i : ∀ e' ∈ m.extent.val.take i.val, ¬ (inL e' id.val ∧ inL e' id2.val) := by
        rw [hi]; exact hpre
      have := forall_take_succ m.extent.val i.val (by omega)
        (fun e' => ¬ (inL e' id.val ∧ inL e' id2.val)) hpre_i (by rw [← he]; exact hnot)
      rw [hi] at this; exact this
    split_ifs with h1 h2 h3 h4
    · simp only [spec_ok]
      refine ⟨hmem, ?_, ?_⟩ <;> unfold inL <;> scalar_tac
    all_goals
      have hnot : ¬ (inL e id.val ∧ inL e id2.val) := by unfold inL; scalar_tac
      step with @UScalar.add_spec .U32 idx 1#u32 (by scalar_tac) as ⟨ idx1, hidx1 ⟩
      all_goals (try simp only [spec_ok, and_assoc])
      refine ⟨by scalar_tac, ?_, by scalar_tac⟩
      rw [hidx1]; exact hnext hnot
  · simp only [spec_ok]
    rename_i hge
    have : extents.val ≤ idx.val := by scalar_tac
    have heq : idx.val = extents.val := by omega
    rw [heq] at hpre; exact hpre

/-! ## The `> 5` binary search: soundness needs no sortedness -/

theorem bsearch_loop_sound (key : IdmapKey) (arr : Array UidGidExtent 340#usize) (lo num : Usize)
    (n : Nat) (hn : n ≤ 340) (hwin : lo.val + num.val ≤ n) :
    bsearch_extent_loop key arr lo num ⦃ r =>
      ∀ e, r = some e → e ∈ arr.val.take n ∧ cmp_map_id key e = ok 0#i32 ⦄ := by
  unfold bsearch_extent_loop
  apply loop.spec_decr_nat (fun p : Usize × Usize => p.2.val)
    (fun p : Usize × Usize => p.1.val + p.2.val ≤ n) _ _ _ _ hwin
  rintro ⟨ lo, num ⟩ hinv
  simp only at hinv
  dsimp only
  unfold bsearch_extent_loop.body
  split
  · rename_i hpos
    have hpos' : 0 < num.val := by scalar_tac
    step with UScalar.ShiftRight_IScalar_spec num 1#i32 (by simp) (by simp; cases System.Platform.numBits_eq <;> simp [*]) as ⟨ half, hhalf, _ ⟩
    have hhalf' : half.val = num.val / 2 := by rw [hhalf]; simp [Nat.shiftRight_eq_div_pow]
    have hpivot_ok : lo.val + half.val ≤ UScalar.max .Usize := by scalar_tac
    step with @UScalar.add_spec .Usize lo half hpivot_ok as ⟨ pivot, hpivot ⟩
    have hlen : arr.val.length = 340 := by simp [Array.length_eq]
    have hbound : pivot.val < arr.length := by simp [Array.length]; scalar_tac
    step with Array.index_usize_spec arr pivot hbound as ⟨ uge, huge ⟩
    -- keep the value of cmp_map_id
    obtain ⟨result, hres⟩ := spec_imp_exists (cmp_map_id_spec key uge)
    rw [hres.1]
    simp only [bind_tc_ok]
    split
    · rename_i hzero
      simp only [spec_ok]
      intro e he
      injection he with he
      subst he
      refine ⟨?_, ?_⟩
      · rw [huge]; exact mem_take_of_getElem _ _ _ (by omega) (by omega)
      · rw [hres.1, hzero]
    · split
      · step with @UScalar.add_spec .Usize pivot 1#usize (by scalar_tac) as ⟨ lo2, hlo2 ⟩
        step with @UScalar.sub_spec .Usize num 1#usize (by scalar_tac) as ⟨ num2, hnum2, _ ⟩
        step with UScalar.ShiftRight_IScalar_spec num2 1#i32 (by simp) (by simp; cases System.Platform.numBits_eq <;> simp [*]) as ⟨ num3, hnum3, _ ⟩
        have hnum3' : num3.val = num2.val / 2 := by rw [hnum3]; simp [Nat.shiftRight_eq_div_pow]
        all_goals (try constructor)
        all_goals scalar_tac
      · step with UScalar.ShiftRight_IScalar_spec num 1#i32 (by simp) (by simp; cases System.Platform.numBits_eq <;> simp [*]) as ⟨ num3, hnum3, _ ⟩
        have hnum3' : num3.val = num.val / 2 := by rw [hnum3]; simp [Nat.shiftRight_eq_div_pow]
        all_goals (try constructor)
        all_goals scalar_tac
  · simp [spec_ok]

/-- **Named gap (step 5).** Completeness of the binary search: if some extent
of the sorted prefix contains the single id, the search finds one. This is the
core of F4 `AGREEMENT` and needs `SortedArms` plus disjointness (so that
`cmp_map_id` is monotone along the array — SPEC §4.4 obligation 1). -/
theorem bsearch_complete (key : IdmapKey) (arr : Array UidGidExtent 340#usize) (n : Nat)
    (hn : n ≤ 340)
    (hsorted : (arr.val.take n).Pairwise (fun a b =>
      (if key.map_up then a.lower_first.val else a.first.val) <
      (if key.map_up then b.lower_first.val else b.first.val)))
    (hwf : ∀ e ∈ arr.val.take n, 1 ≤ e.count.val ∧
      (if key.map_up then e.lower_first.val else e.first.val) + e.count.val ≤ 2^32 - 1)
    (hcount1 : key.count.val = 1)
    (hhit : ∃ e ∈ arr.val.take n, if key.map_up then inL e key.id.val else inU e key.id.val) :
    bsearch_extent key arr (Usize.ofNat n (by scalar_tac)) ⦃ r => r ≠ none ⦄ := by
  sorry

/-! ## Soundness of the single-id lookups, both paths -/

theorem cmp_zero_inU {key : IdmapKey} {e : UidGidExtent}
    (hup : key.map_up = false) (hcnt1 : key.count.val = 1)
    (hecnt : 1 ≤ e.count.val) (hnw : e.first.val + e.count.val ≤ 2^32 - 1)
    (h : cmp_map_id key e = ok 0#i32) : inU e key.id.val := by
  have hz := cmp_map_id_zero_down key e hup h
  have hlast := last_val e.first e.count hecnt (by simp [U32.max_eq]; omega)
  have hid2 : (core.num.U32.wrapping_sub (core.num.U32.wrapping_add key.id key.count) 1#u32).val
      = key.id.val := by
    have h1 : key.count = 1#u32 := by
      apply UScalar.eq_of_val_eq; simp [hcnt1]
    rw [h1]; exact id2_one_val key.id
  unfold inU; scalar_tac

theorem cmp_zero_inL {key : IdmapKey} {e : UidGidExtent}
    (hup : key.map_up = true) (hcnt1 : key.count.val = 1)
    (hecnt : 1 ≤ e.count.val) (hnw : e.lower_first.val + e.count.val ≤ 2^32 - 1)
    (h : cmp_map_id key e = ok 0#i32) : inL e key.id.val := by
  have hz := cmp_map_id_zero_up key e hup h
  have hlast := last_val e.lower_first e.count hecnt (by simp [U32.max_eq]; omega)
  have hid2 : (core.num.U32.wrapping_sub (core.num.U32.wrapping_add key.id key.count) 1#u32).val
      = key.id.val := by
    have h1 : key.count = 1#u32 := by
      apply UScalar.eq_of_val_eq; simp [hcnt1]
    rw [h1]; exact id2_one_val key.id
  unfold inL; scalar_tac

/-- F1, downward, single id: the result is the sentinel or comes from a
containing extent of the active arm. -/
theorem down_sound (m : UidGidMap) (hwf : WellFormed m) (x : U32) :
    map_id_down m x ⦃ v => v = ID_SENTINEL ∨ ∃ e ∈ absFwd m, inU e x.val ∧ v.val = apDown e x.val ⦄ := by
  unfold map_id_down map_id_range_down
  have h5 : (UScalar.cast .U32 UID_GID_MAP_MAX_BASE_EXTENTS).val = 5 := by
    simp [UID_GID_MAP_MAX_BASE_EXTENTS, UScalar.cast_val_eq]
  have hid2 := id2_one_val x
  simp only [lift, bind_tc_ok]
  split
  · rename_i hle
    have hle' : m.nr_extents.val ≤ 5 := by scalar_tac
    have habs := absFwd_le5 hle'
    unfold map_id_range_down_base
    simp only [lift, bind_tc_ok]
    have hwf' : ∀ e ∈ m.extent.val.take m.nr_extents.val,
        1 ≤ e.count.val ∧ e.first.val + e.count.val ≤ 2^32 - 1 := by
      intro e he; rw [← habs] at he; exact ⟨hwf.count_pos e he, hwf.nowrap_u e he⟩
    step with base_loop_down_fun m.nr_extents m x _ 0#u32 hle' (by simp) hwf' (by simp) as ⟨ ext, hext ⟩
    rcases ext with _ | e
    · simp [spec_ok]
    · simp only [spec_ok]
      right
      obtain ⟨hmem, hin, _⟩ := hext
      rw [← habs] at hmem
      exact ⟨e, hmem, hin, down_result_val e x hin (hwf.nowrap_l e hmem)⟩
  · rename_i hgt
    have hgt' : 5 < m.nr_extents.val := by scalar_tac
    have habs := absFwd_gt5 hgt'
    unfold map_id_range_down_max
    have hc : m.nr_extents.val ≤ UScalar.max .Usize := by scalar_tac
    step with UScalar.cast_inBounds_spec .Usize m.nr_extents hc as ⟨ n, hn ⟩
    unfold bsearch_extent
    step with bsearch_loop_sound { map_up := false, id := x, count := 1#u32 } m.forward 0#usize n
      m.nr_extents.val hwf.len_le (by simp; omega) as ⟨ ext, hext ⟩
    rcases ext with _ | e
    · simp [spec_ok]
    · simp only [spec_ok]
      right
      obtain ⟨hmem, hzero⟩ := hext e rfl
      rw [← habs] at hmem
      have hin : inU e x.val :=
        cmp_zero_inU rfl (by simp) (hwf.count_pos e hmem) (hwf.nowrap_u e hmem) hzero
      exact ⟨e, hmem, hin, down_result_val e x hin (hwf.nowrap_l e hmem)⟩

/-- F1, upward, single id. -/
theorem up_sound (m : UidGidMap) (hwf : WellFormed m) (y : U32) :
    map_id_up m y ⦃ v => v = ID_SENTINEL ∨ ∃ e ∈ absRev m, inL e y.val ∧ v.val = apUp e y.val ⦄ := by
  unfold map_id_up map_id_range_up
  have h5 : (UScalar.cast .U32 UID_GID_MAP_MAX_BASE_EXTENTS).val = 5 := by
    simp [UID_GID_MAP_MAX_BASE_EXTENTS, UScalar.cast_val_eq]
  have hid2 := id2_one_val y
  simp only [lift, bind_tc_ok]
  split
  · rename_i hle
    have hle' : m.nr_extents.val ≤ 5 := by scalar_tac
    have habs := absRev_le5 hle'
    have habsF := absFwd_le5 hle'
    unfold map_id_range_up_base
    simp only [lift, bind_tc_ok]
    have hwf' : ∀ e ∈ m.extent.val.take m.nr_extents.val,
        1 ≤ e.count.val ∧ e.lower_first.val + e.count.val ≤ 2^32 - 1 := by
      intro e he; rw [← habsF] at he; exact ⟨hwf.count_pos e he, hwf.nowrap_l e he⟩
    step with base_loop_up_fun m.nr_extents m y _ 0#u32 hle' (by simp) hwf' (by simp) as ⟨ ext, hext ⟩
    rcases ext with _ | e
    · simp [spec_ok]
    · simp only [spec_ok]
      right
      obtain ⟨hmem, hin, _⟩ := hext
      have hmemF : e ∈ absFwd m := by rw [habsF]; exact hmem
      rw [← habs] at hmem
      exact ⟨e, hmem, hin, up_result_val e y hin (hwf.nowrap_u e hmemF)⟩
  · rename_i hgt
    have hgt' : 5 < m.nr_extents.val := by scalar_tac
    have habs := absRev_gt5 hgt'
    unfold map_id_range_up_max
    have hc : m.nr_extents.val ≤ UScalar.max .Usize := by scalar_tac
    step with UScalar.cast_inBounds_spec .Usize m.nr_extents hc as ⟨ n, hn ⟩
    unfold bsearch_extent
    step with bsearch_loop_sound { map_up := true, id := y, count := 1#u32 } m.reverse 0#usize n
      m.nr_extents.val hwf.len_le (by simp; omega) as ⟨ ext, hext ⟩
    rcases ext with _ | e
    · simp [spec_ok]
    · simp only [spec_ok]
      right
      obtain ⟨hmem, hzero⟩ := hext e rfl
      rw [← habs] at hmem
      have hmemF : e ∈ absFwd m := (hwf.mem_absRev_iff e).1 hmem
      have hin : inL e y.val :=
        cmp_zero_inL rfl (by simp) (hwf.count_pos e hmemF) (hwf.nowrap_l e hmemF) hzero
      exact ⟨e, hmem, hin, up_result_val e y hin (hwf.nowrap_u e hmemF)⟩

/-! ## F2 — INJECTIVITY (SPEC §4.2) -/

/-- Two distinct namespace ids never map to the same kernel id. `sorry`-free
for both lookup paths: it needs soundness only. -/
theorem down_injective (m : UidGidMap) (hwf : WellFormed m) (x y v : U32)
    (hx : map_id_down m x = ok v) (hy : map_id_down m y = ok v) (hv : v ≠ ID_SENTINEL) :
    x = y := by
  have hsx := down_sound m hwf x; rw [hx, spec_ok] at hsx
  have hsy := down_sound m hwf y; rw [hy, spec_ok] at hsy
  rcases hsx with h | ⟨e, he, hxe, hve⟩
  · exact absurd h hv
  rcases hsy with h | ⟨e', he', hye, hve'⟩
  · exact absurd h hv
  have : x.val = y.val := hwf.abs_injective he he' hxe hye (by rw [← hve, ← hve'])
  exact UScalar.eq_of_val_eq this

/-! ## F3 — ROUNDTRIP (SPEC §4.3) -/

/-- Never an unrelated id: `up (down x)` is `x` or the sentinel. `sorry`-free
for both paths. -/
theorem roundtrip_sound (m : UidGidMap) (hwf : WellFormed m) (x k r : U32)
    (hd : map_id_down m x = ok k) (hu : map_id_up m k = ok r) :
    r = ID_SENTINEL ∨ r = x := by
  have hsd := down_sound m hwf x; rw [hd, spec_ok] at hsd
  have hsu := up_sound m hwf k; rw [hu, spec_ok] at hsu
  rcases hsu with h | ⟨e', he', hke', hre'⟩
  · exact Or.inl h
  right
  -- k lies in L(e'); so k is not the sentinel
  have he'F : e' ∈ absFwd m := (hwf.mem_absRev_iff e').1 he'
  have hk_ne : k.val ≠ 2^32 - 1 := inL_ne_sentinel (hwf.nowrap_l e' he'F) hke'
  rcases hsd with h | ⟨e, he, hxe, hke⟩
  · exact absurd (by rw [h, sentinel_val]) hk_ne
  -- k = apDown e x, and e' contains it, so e' = e and apUp e' k = x
  have : apUp e' (apDown e x.val) = x.val := hwf.abs_roundtrip he he'F hxe (hke ▸ hke')
  apply UScalar.eq_of_val_eq
  rw [hre', hke]; exact this

/-- And it is found, below 6 extents: `up` never returns the sentinel on the
image of a successful `down`. -/
theorem roundtrip_complete_le5 (m : UidGidMap) (hwf : WellFormed m) (h5 : m.nr_extents.val ≤ 5)
    (x k : U32) (hd : map_id_down m x = ok k) (hk : k ≠ ID_SENTINEL) :
    map_id_up m k ⦃ r => r ≠ ID_SENTINEL ⦄ := by
  have hsd := down_sound m hwf x; rw [hd, spec_ok] at hsd
  rcases hsd with h | ⟨e, he, hxe, hke⟩
  · exact absurd h hk
  have hkL : inL e k.val := by rw [hke]; exact apDown_inL hxe
  unfold map_id_up map_id_range_up
  have h5' : (UScalar.cast .U32 UID_GID_MAP_MAX_BASE_EXTENTS).val = 5 := by
    simp [UID_GID_MAP_MAX_BASE_EXTENTS, UScalar.cast_val_eq]
  have hid2 := id2_one_val k
  have hle : m.nr_extents ≤ UScalar.cast .U32 UID_GID_MAP_MAX_BASE_EXTENTS := by scalar_tac
  simp only [lift, bind_tc_ok, hle, if_true]
  have habsF := absFwd_le5 h5
  unfold map_id_range_up_base
  simp only [lift, bind_tc_ok]
  have hwf' : ∀ e ∈ m.extent.val.take m.nr_extents.val,
      1 ≤ e.count.val ∧ e.lower_first.val + e.count.val ≤ 2^32 - 1 := by
    intro e he; rw [← habsF] at he; exact ⟨hwf.count_pos e he, hwf.nowrap_l e he⟩
  step with base_loop_up_fun m.nr_extents m k _ 0#u32 h5 (by simp) hwf' (by simp) as ⟨ ext, hext ⟩
  rcases ext with _ | e'
  · -- none: contradiction, e contains k
    exfalso
    have he' : e ∈ m.extent.val.take m.nr_extents.val := by rw [← habsF]; exact he
    have hkL2 : inL e (core.num.U32.wrapping_sub (core.num.U32.wrapping_add k 1#u32) 1#u32).val := by
      rw [hid2]; exact hkL
    exact hext e he' ⟨hkL, hkL2⟩
  · simp only [spec_ok]
    obtain ⟨hmem, hin, _⟩ := hext
    have hmemF : e' ∈ absFwd m := by rw [habsF]; exact hmem
    intro hcontra
    have hv := up_result_val e' k hin (hwf.nowrap_u e' hmemF)
    have : (core.num.U32.wrapping_add (core.num.U32.wrapping_sub k e'.lower_first) e'.first).val
        = 2^32 - 1 := by rw [hcontra, sentinel_val]
    rw [hv] at this
    exact inU_ne_sentinel (hwf.nowrap_u e' hmemF) (apUp_inU hin) this

/-- Completeness for every map, resting on `bsearch_complete` above 5. -/
theorem roundtrip_complete (m : UidGidMap) (hwf : WellFormed m) (hsorted : SortedArms m)
    (x k : U32) (hd : map_id_down m x = ok k) (hk : k ≠ ID_SENTINEL) :
    map_id_up m k ⦃ r => r ≠ ID_SENTINEL ⦄ := by
  by_cases h5 : m.nr_extents.val ≤ 5
  · exact roundtrip_complete_le5 m hwf h5 x k hd hk
  · sorry

end UidmapAlgebra

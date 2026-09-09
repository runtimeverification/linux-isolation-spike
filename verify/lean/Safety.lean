-- SPDX-License-Identifier: GPL-2.0
import Uidmap
/-!
# Safety properties S1–S5 (SPEC.md §2, §4.1, §4.7, §1.3)

Against the Aeneas-extracted model in `Uidmap.lean` (Model T).

Aeneas puts every function in `Result α = ok α | fail Error | div`. A Rust
panic (index out of bounds, checked-arithmetic overflow) is `fail`; a
non-terminating loop is `div`. The Hoare-triple notation `x ⦃ p ⦄` is
`WP.spec x p`, which is FALSE at `fail` and at `div` (`WP.spec_fail`,
`WP.spec_div`). So `x ⦃ _ => True ⦄` says exactly: `x` returns `ok`. That is
S2 (no panic) and S3 (termination) in one statement; `spec_true_iff_ok` below
makes the reading explicit.

Naming: `<fn>_spec` is the total-correctness statement for `<fn>`; hypotheses
are the SPEC clause names where one applies.
-/
open Aeneas Aeneas.Std Result ControlFlow WP
open uidmap

namespace UidmapSafety

/-! ## Reading `⦃ _ => True ⦄` -/

theorem spec_true_iff_ok {α} (x : Result α) : (x ⦃ _ => True ⦄) ↔ ∃ v, x = ok v := by
  cases x <;> simp [spec_ok, spec_fail, spec_div]

/-! ## S1 — TOTAL-SAFETY

Every outcome is `ok` / `fail` / `div`; there is no fourth,
undefined-behaviour outcome. Content-free as a proof, and stated because the
*completeness* of the enumeration is the memory-safety guarantee the C lacks:
every array access in the model is a checked `index_usize` that returns `fail`
on a bad index, never a wild read. -/

theorem total_safety {α} (x : Result α) :
    (∃ v, x = ok v) ∨ (∃ e, x = fail e) ∨ x = div := by
  cases x <;> simp

theorem map_id_down_total_safety (m : UidGidMap) (id : U32) :
    (∃ v, map_id_down m id = ok v) ∨ (∃ e, map_id_down m id = fail e) ∨ map_id_down m id = div :=
  total_safety _
theorem map_id_up_total_safety (m : UidGidMap) (id : U32) :
    (∃ v, map_id_up m id = ok v) ∨ (∃ e, map_id_up m id = fail e) ∨ map_id_up m id = div :=
  total_safety _
theorem map_id_range_down_total_safety (m : UidGidMap) (id count : U32) :
    (∃ v, map_id_range_down m id count = ok v) ∨ (∃ e, map_id_range_down m id count = fail e)
      ∨ map_id_range_down m id count = div :=
  total_safety _
theorem map_id_range_up_total_safety (m : UidGidMap) (id count : U32) :
    (∃ v, map_id_range_up m id count = ok v) ∨ (∃ e, map_id_range_up m id count = fail e)
      ∨ map_id_range_up m id count = div :=
  total_safety _
theorem insert_extent_total_safety (m : UidGidMap) (e : UidGidExtent) :
    (∃ v, insert_extent m e = ok v) ∨ (∃ err, insert_extent m e = fail err) ∨ insert_extent m e = div :=
  total_safety _

/-! ## `cmp_map_id` is total

Only wrapping arithmetic and comparisons; every leaf is `ok`. This is the
comparison predicate the binary search steps through, and its totality is the
first thing `bsearch_extent_spec` needs. -/

theorem cmp_map_id_spec (key : IdmapKey) (el : UidGidExtent) :
    cmp_map_id key el ⦃ _ => True ⦄ := by
  unfold cmp_map_id
  simp only [lift, bind_tc_ok]
  split <;> simp only [bind_tc_ok] <;> split_ifs <;> simp [spec_ok]

/-! ## S4 — NO-OVERFLOW: the arithmetic bridge

The C computes `last = first + count - 1` in `u32`, which the model renders
as `wrapping_sub (wrapping_add first count) 1`. Under `WF-COUNT` (`count ≥ 1`)
and `WF-NOWRAP` (`first + count ≤ 2^32 - 1`, SPEC §1.2.1) the wrapping
computation equals the mathematical value. This is the lemma F1/F2 consume;
stated here because it is the *content* of S4 — the wrapping sites cannot
panic (they are total) but they compute the intended value only under these
two clauses. -/

theorem last_val (first count : U32)
    (hcount : 1 ≤ count.val) (hnowrap : first.val + count.val ≤ U32.max) :
    (core.num.U32.wrapping_sub (core.num.U32.wrapping_add first count) 1#u32).val
      = first.val + count.val - 1 := by
  simp only [core.num.U32.wrapping_add, core.num.U32.wrapping_sub,
             UScalar.wrapping_add_val_eq, UScalar.wrapping_sub_val_eq]
  have hmax := first.hmax
  have h2 : (1#u32).val = 1 := by simp
  simp only [h2, UScalar.size]
  scalar_tac

/-- The caller-supplied range `id + count - 1` (`cmp_map_id` :255, the base
scans :304/:353): same bridge, same hypotheses, on the key rather than the
extent. -/
theorem id2_val (id count : U32)
    (hcount : 1 ≤ count.val) (hnowrap : id.val + count.val ≤ U32.max) :
    (core.num.U32.wrapping_sub (core.num.U32.wrapping_add id count) 1#u32).val
      = id.val + count.val - 1 :=
  last_val id count hcount hnowrap

/-! ## S2 + S3 for the `≤ 5` linear scans

Precondition: `extents ≤ 5`. Nothing else — no well-formedness is needed for
the base scan to be safe, because every index is `idx < extents ≤ 5` and the
array has 5 slots. `map_id_range_down` supplies the precondition by
construction (it only takes this path when `nr_extents ≤ 5`). -/

theorem map_id_range_down_base_loop_spec
    (extents : U32) (m : UidGidMap) (id id2 idx : U32)
    (hext : extents.val ≤ 5) (hidx : idx.val ≤ extents.val) :
    map_id_range_down_base_loop extents m id idx id2 ⦃ _ => True ⦄ := by
  unfold map_id_range_down_base_loop
  apply loop.spec_decr_nat (fun idx : U32 => extents.val - idx.val)
    (fun idx : U32 => idx.val ≤ extents.val) (fun _ => True) _ _ _ hidx
  intro idx hinv
  unfold map_id_range_down_base_loop.body
  split
  · rename_i hlt
    have hlt' : idx.val < extents.val := by scalar_tac
    have hcast : idx.val ≤ UScalar.max .Usize := by scalar_tac
    step with UScalar.cast_inBounds_spec .Usize idx hcast as ⟨ i, hi ⟩
    have hbound : i.val < m.extent.length := by simp [Array.length]; scalar_tac
    step with Array.index_usize_spec m.extent i hbound as ⟨ e, he ⟩
    simp only [lift, bind_tc_ok]
    have hsucc : idx.val + 1 ≤ U32.max := by scalar_tac
    split_ifs
    all_goals first
      | (simp [spec_ok])
      | (step with @UScalar.add_spec .U32 idx 1#u32 (by scalar_tac) as ⟨ idx1, hidx1 ⟩
         all_goals (try constructor)
         all_goals scalar_tac)
  · simp [spec_ok]

theorem map_id_range_up_base_loop_spec
    (extents : U32) (m : UidGidMap) (id id2 idx : U32)
    (hext : extents.val ≤ 5) (hidx : idx.val ≤ extents.val) :
    map_id_range_up_base_loop extents m id idx id2 ⦃ _ => True ⦄ := by
  unfold map_id_range_up_base_loop
  apply loop.spec_decr_nat (fun idx : U32 => extents.val - idx.val)
    (fun idx : U32 => idx.val ≤ extents.val) (fun _ => True) _ _ _ hidx
  intro idx hinv
  unfold map_id_range_up_base_loop.body
  split
  · rename_i hlt
    have hlt' : idx.val < extents.val := by scalar_tac
    have hcast : idx.val ≤ UScalar.max .Usize := by scalar_tac
    step with UScalar.cast_inBounds_spec .Usize idx hcast as ⟨ i, hi ⟩
    have hbound : i.val < m.extent.length := by simp [Array.length]; scalar_tac
    step with Array.index_usize_spec m.extent i hbound as ⟨ e, he ⟩
    simp only [lift, bind_tc_ok]
    have hsucc : idx.val + 1 ≤ U32.max := by scalar_tac
    split_ifs
    all_goals first
      | (simp [spec_ok])
      | (step with @UScalar.add_spec .U32 idx 1#u32 (by scalar_tac) as ⟨ idx1, hidx1 ⟩
         all_goals (try constructor)
         all_goals scalar_tac)
  · simp [spec_ok]

theorem map_id_range_down_base_spec (extents : U32) (m : UidGidMap) (id count : U32)
    (hext : extents.val ≤ 5) :
    map_id_range_down_base extents m id count ⦃ _ => True ⦄ := by
  unfold map_id_range_down_base
  simp only [lift, bind_tc_ok]
  exact map_id_range_down_base_loop_spec extents m id _ 0#u32 hext (by simp)

theorem map_id_range_up_base_spec (extents : U32) (m : UidGidMap) (id count : U32)
    (hext : extents.val ≤ 5) :
    map_id_range_up_base extents m id count ⦃ _ => True ⦄ := by
  unfold map_id_range_up_base
  simp only [lift, bind_tc_ok]
  exact map_id_range_up_base_loop_spec extents m id _ 0#u32 hext (by simp)

/-! ## S2 + S3 for the `> 5` binary search

Precondition: `nmemb ≤ 340` — `WF-LEN`'s upper half. This is the one place
the lookup path's memory safety depends on a `WellFormed` clause: with
`nr_extents > 340` the C's `bsearch` reads past the 340-slot heap array, and
the model's `index_usize` returns `fail`. `map_write` 1041 is what establishes
the bound.

Invariant on the `(lo, num)` state: `lo + num ≤ 340`, i.e. the search window
stays inside the array. Measure: `num`, which strictly decreases because
`num >>= 1` on `num ≥ 1` decreases, and the `num--` branch decreases first
(SPEC §4.4 obligation 2 is exactly this invariant re-established across both
branches). -/

theorem bsearch_extent_loop_spec
    (key : IdmapKey) (arr : Array UidGidExtent 340#usize) (lo num : Usize)
    (hwin : lo.val + num.val ≤ 340) :
    bsearch_extent_loop key arr lo num ⦃ _ => True ⦄ := by
  unfold bsearch_extent_loop
  apply loop.spec_decr_nat (fun p : Usize × Usize => p.2.val)
    (fun p : Usize × Usize => p.1.val + p.2.val ≤ 340) (fun _ => True) _ _ _ hwin
  rintro ⟨ lo, num ⟩ hinv
  simp only at hinv
  dsimp only
  unfold bsearch_extent_loop.body
  split
  · rename_i hpos
    have hpos' : 0 < num.val := by scalar_tac
    step with UScalar.ShiftRight_IScalar_spec num 1#i32 (by simp) (by simp; cases System.Platform.numBits_eq <;> simp [*]) as ⟨ half, hhalf, _ ⟩
    have hhalf' : half.val = num.val / 2 := by
      rw [hhalf]; simp [Nat.shiftRight_eq_div_pow]
    have hpivot_ok : lo.val + half.val ≤ UScalar.max .Usize := by scalar_tac
    step with @UScalar.add_spec .Usize lo half hpivot_ok as ⟨ pivot, hpivot ⟩
    have hbound : pivot.val < arr.length := by simp [Array.length]; scalar_tac
    step with Array.index_usize_spec arr pivot hbound as ⟨ uge, huge ⟩
    step with cmp_map_id_spec key uge as ⟨ result ⟩
    split
    · simp [spec_ok]
    · -- the (lo1, num1) update, then num1 >>> 1
      split
      · -- result > 0: lo = pivot + 1, num = num - 1
        step with @UScalar.add_spec .Usize pivot 1#usize (by scalar_tac) as ⟨ lo2, hlo2 ⟩
        step with @UScalar.sub_spec .Usize num 1#usize (by scalar_tac) as ⟨ num2, hnum2, _ ⟩
        step with UScalar.ShiftRight_IScalar_spec num2 1#i32 (by simp) (by simp; cases System.Platform.numBits_eq <;> simp [*]) as ⟨ num3, hnum3, _ ⟩
        have hnum3' : num3.val = num2.val / 2 := by
          rw [hnum3]; simp [Nat.shiftRight_eq_div_pow]
        all_goals (try constructor)
        all_goals scalar_tac
      · step with UScalar.ShiftRight_IScalar_spec num 1#i32 (by simp) (by simp; cases System.Platform.numBits_eq <;> simp [*]) as ⟨ num3, hnum3, _ ⟩
        have hnum3' : num3.val = num.val / 2 := by
          rw [hnum3]; simp [Nat.shiftRight_eq_div_pow]
        all_goals (try constructor)
        all_goals scalar_tac
  · simp [spec_ok]

theorem bsearch_extent_spec
    (key : IdmapKey) (arr : Array UidGidExtent 340#usize) (nmemb : Usize)
    (hlen : nmemb.val ≤ 340) :
    bsearch_extent key arr nmemb ⦃ _ => True ⦄ := by
  unfold bsearch_extent
  exact bsearch_extent_loop_spec key arr 0#usize nmemb (by simp; exact hlen)

/-! ## S2 + S3 for the dispatching lookups

The single hypothesis is `WF-LEN`'s upper half, `nr_extents ≤ 340`. Below 5
the base path needs nothing; above 5 the binary search needs the bound. -/

theorem map_id_range_down_spec (m : UidGidMap) (id count : U32)
    (hlen : m.nr_extents.val ≤ 340) :
    map_id_range_down m id count ⦃ _ => True ⦄ := by
  unfold map_id_range_down
  have h5 : (UScalar.cast .U32 UID_GID_MAP_MAX_BASE_EXTENTS).val = 5 := by
    simp [UID_GID_MAP_MAX_BASE_EXTENTS, UScalar.cast_val_eq]
  simp only [lift, bind_tc_ok]
  split
  · rename_i hle
    have : m.nr_extents.val ≤ 5 := by scalar_tac
    step with map_id_range_down_base_spec m.nr_extents m id count this as ⟨ ext ⟩
    rcases ext with _ | e <;> simp [spec_ok]
  · unfold map_id_range_down_max
    have hc : m.nr_extents.val ≤ UScalar.max .Usize := by scalar_tac
    step with UScalar.cast_inBounds_spec .Usize m.nr_extents hc as ⟨ n, hn ⟩
    step with bsearch_extent_spec _ m.forward n (by scalar_tac) as ⟨ ext ⟩
    rcases ext with _ | e <;> simp [spec_ok]

theorem map_id_range_up_spec (m : UidGidMap) (id count : U32)
    (hlen : m.nr_extents.val ≤ 340) :
    map_id_range_up m id count ⦃ _ => True ⦄ := by
  unfold map_id_range_up
  have h5 : (UScalar.cast .U32 UID_GID_MAP_MAX_BASE_EXTENTS).val = 5 := by
    simp [UID_GID_MAP_MAX_BASE_EXTENTS, UScalar.cast_val_eq]
  simp only [lift, bind_tc_ok]
  split
  · rename_i hle
    have : m.nr_extents.val ≤ 5 := by scalar_tac
    step with map_id_range_up_base_spec m.nr_extents m id count this as ⟨ ext ⟩
    rcases ext with _ | e <;> simp [spec_ok]
  · unfold map_id_range_up_max
    have hc : m.nr_extents.val ≤ UScalar.max .Usize := by scalar_tac
    step with UScalar.cast_inBounds_spec .Usize m.nr_extents hc as ⟨ n, hn ⟩
    step with bsearch_extent_spec _ m.reverse n (by scalar_tac) as ⟨ ext ⟩
    rcases ext with _ | e <;> simp [spec_ok]

theorem map_id_down_spec (m : UidGidMap) (id : U32) (hlen : m.nr_extents.val ≤ 340) :
    map_id_down m id ⦃ _ => True ⦄ := by
  unfold map_id_down; exact map_id_range_down_spec m id 1#u32 hlen

theorem map_id_up_spec (m : UidGidMap) (id : U32) (hlen : m.nr_extents.val ≤ 340) :
    map_id_up m id ⦃ _ => True ⦄ := by
  unfold map_id_up; exact map_id_range_up_spec m id 1#u32 hlen

theorem make_kuid_spec (m : UidGidMap) (uid : U32) (hlen : m.nr_extents.val ≤ 340) :
    make_kuid m uid ⦃ _ => True ⦄ := by
  unfold make_kuid; exact map_id_down_spec m uid hlen

theorem from_kuid_spec (m : UidGidMap) (kuid : U32) (hlen : m.nr_extents.val ≤ 340) :
    from_kuid m kuid ⦃ _ => True ⦄ := by
  unfold from_kuid; exact map_id_up_spec m kuid hlen

/-! ## S2 + S3 for `insert_extent` — the write-path constructor

Precondition: `nr_extents < 340`, i.e. `nr_extents ≤ 339`. This is the exact
boundary `map_write` 1041 enforces (`nr_extents + 1 == 340 && next_line` ->
reject), and the one place a `+1` off-by-one would be an out-of-bounds write
into the 340-slot heap array. The migration branch (`nr_extents == 5`) copies
the base arm into the heap arm — the loop indexes `extent[i]` for `i < 5` and
writes `forward[i]` — then performs the two clobber writes and the insert at
`forward[5]`.

Postcondition: returns `0` (the C's success code; the `-ENOMEM` path is
unreachable in the model, SPEC §7 item 6) and increments `nr_extents` by
exactly one. -/

/-- `u32 as usize` never truncates: the pure form of `UScalar.cast_inBounds_spec`,
for sites where the `lift` has already been reduced away. -/
theorem cast_usize_val (x : U32) : (UScalar.cast .Usize x).val = x.val := by
  have hc : x.val ≤ UScalar.max .Usize := by scalar_tac
  have h := UScalar.cast_inBounds_spec .Usize x hc
  simpa [lift, spec_ok] using h

theorem insert_extent_loop_spec
    (a : Array UidGidExtent 5#usize) (a1 : Array UidGidExtent 340#usize) (i i1 : U32)
    (hi : i.val ≤ 5) (hi1 : i1.val ≤ i.val) :
    insert_extent_loop a a1 i i1 ⦃ _ => True ⦄ := by
  unfold insert_extent_loop
  apply loop.spec_decr_nat (fun p : Array UidGidExtent 340#usize × U32 => i.val - p.2.val)
    (fun p : Array UidGidExtent 340#usize × U32 => p.2.val ≤ i.val) (fun _ => True) _ _ _ hi1
  rintro ⟨ a2, i2 ⟩ hinv
  simp only at hinv
  dsimp only
  unfold insert_extent_loop.body
  split
  · rename_i hlt
    have hlt' : i2.val < i.val := by scalar_tac
    have hc : i2.val ≤ UScalar.max .Usize := by scalar_tac
    step with UScalar.cast_inBounds_spec .Usize i2 hc as ⟨ j, hj ⟩
    have hb1 : j.val < a.length := by simp [Array.length]; scalar_tac
    step with Array.index_usize_spec a j hb1 as ⟨ uge, huge ⟩
    step with UScalar.cast_inBounds_spec .Usize i2 hc as ⟨ j', hj' ⟩
    have hb2 : j'.val < a2.length := by simp [Array.length]; scalar_tac
    step with Array.update_spec a2 j' uge hb2 as ⟨ a3, ha3 ⟩
    step with @UScalar.add_spec .U32 i2 1#u32 (by scalar_tac) as ⟨ i3, hi3 ⟩
    all_goals (try constructor)
    all_goals scalar_tac
  · simp [spec_ok]

theorem insert_extent_spec (m : UidGidMap) (e : UidGidExtent)
    (hlen : m.nr_extents.val < 340) :
    insert_extent m e ⦃ r => r.1 = 0#i32 ∧ r.2.nr_extents.val = m.nr_extents.val + 1 ⦄ := by
  unfold insert_extent
  have h5 : (UScalar.cast .U32 UID_GID_MAP_MAX_BASE_EXTENTS).val = 5 := by
    simp [UID_GID_MAP_MAX_BASE_EXTENTS, UScalar.cast_val_eq]
  simp only [lift, bind_tc_ok]
  split
  · -- migration: nr_extents == 5
    rename_i heq
    have h5' : m.nr_extents.val = 5 := by rw [heq]; exact h5
    step with insert_extent_loop_spec m.extent m.forward m.nr_extents 0#u32 (by scalar_tac) (by simp)
      as ⟨ a ⟩
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
    all_goals (first | rfl | scalar_tac)
  · rename_i hne
    split
    · -- nr_extents < 5: insert into the base arm
      rename_i hlt
      have hk := cast_usize_val m.nr_extents
      have hbk : (UScalar.cast .Usize m.nr_extents).val < m.extent.length := by
        simp only [Array.length, Array.length_eq]; scalar_tac
      step with Array.update_spec m.extent (UScalar.cast .Usize m.nr_extents) e hbk as ⟨ a2, ha2 ⟩
      step with @UScalar.add_spec .U32 m.nr_extents 1#u32 (by scalar_tac) as ⟨ n1, hn1 ⟩
      all_goals (first | rfl | scalar_tac)
    · -- nr_extents > 5: insert into the heap arm at nr_extents < 340
      have hk := cast_usize_val m.nr_extents
      have hbk : (UScalar.cast .Usize m.nr_extents).val < m.forward.length := by
        simp only [Array.length, Array.length_eq]; scalar_tac
      step with Array.update_spec m.forward (UScalar.cast .Usize m.nr_extents) e hbk as ⟨ a2, ha2 ⟩
      step with @UScalar.add_spec .U32 m.nr_extents 1#u32 (by scalar_tac) as ⟨ n1, hn1 ⟩
      all_goals (first | rfl | scalar_tac)

/-! ## S5 — NO-STALE-READ (Model T)

Non-interference: for a map on the heap arm (`nr_extents > 5`), the lookups
depend only on the heap arrays and `nr_extents`. Perturbing the base arm
`extent[]` — which is exactly what `insert_extent`'s clobber does — changes
nothing. This is the theorem that replaces assumption `A-UNION`.

The proof is by unfolding: the dispatch takes the `else` branch in both maps,
and `map_id_range_down_max` / `_up_max` mention only `forward` / `reverse` and
`nr_extents`. -/

theorem no_stale_read_down (m m' : UidGidMap) (h5 : 5 < m.nr_extents.val)
    (hfw : m.forward = m'.forward) (hn : m.nr_extents = m'.nr_extents)
    (id count : U32) :
    map_id_range_down m id count = map_id_range_down m' id count := by
  have h5' : (UScalar.cast .U32 UID_GID_MAP_MAX_BASE_EXTENTS).val = 5 := by
    simp [UID_GID_MAP_MAX_BASE_EXTENTS, UScalar.cast_val_eq]
  have hno : ¬ (m.nr_extents ≤ UScalar.cast .U32 UID_GID_MAP_MAX_BASE_EXTENTS) := by scalar_tac
  have hno' : ¬ (m'.nr_extents ≤ UScalar.cast .U32 UID_GID_MAP_MAX_BASE_EXTENTS) := by
    rw [← hn]; exact hno
  unfold map_id_range_down
  simp only [lift, bind_tc_ok, hno, hno', if_false]
  unfold map_id_range_down_max
  rw [hn, hfw]

theorem no_stale_read_up (m m' : UidGidMap) (h5 : 5 < m.nr_extents.val)
    (hrv : m.reverse = m'.reverse) (hn : m.nr_extents = m'.nr_extents)
    (id count : U32) :
    map_id_range_up m id count = map_id_range_up m' id count := by
  have h5' : (UScalar.cast .U32 UID_GID_MAP_MAX_BASE_EXTENTS).val = 5 := by
    simp [UID_GID_MAP_MAX_BASE_EXTENTS, UScalar.cast_val_eq]
  have hno : ¬ (m.nr_extents ≤ UScalar.cast .U32 UID_GID_MAP_MAX_BASE_EXTENTS) := by scalar_tac
  have hno' : ¬ (m'.nr_extents ≤ UScalar.cast .U32 UID_GID_MAP_MAX_BASE_EXTENTS) := by
    rw [← hn]; exact hno
  unfold map_id_range_up
  simp only [lift, bind_tc_ok, hno, hno', if_false]
  unfold map_id_range_up_max
  rw [hn, hrv]

/-- The symmetric fact for the base arm: below 5 extents, the heap arrays are
never consulted. Together with `no_stale_read_*` this is the complete
statement that each lookup reads exactly one arm of the union. -/
theorem base_arm_only_down (m m' : UidGidMap) (h5 : m.nr_extents.val ≤ 5)
    (hex : m.extent = m'.extent) (hn : m.nr_extents = m'.nr_extents)
    (id count : U32) :
    map_id_range_down m id count = map_id_range_down m' id count := by
  have h5' : (UScalar.cast .U32 UID_GID_MAP_MAX_BASE_EXTENTS).val = 5 := by
    simp [UID_GID_MAP_MAX_BASE_EXTENTS, UScalar.cast_val_eq]
  have hyes : m.nr_extents ≤ UScalar.cast .U32 UID_GID_MAP_MAX_BASE_EXTENTS := by scalar_tac
  have hyes' : m'.nr_extents ≤ UScalar.cast .U32 UID_GID_MAP_MAX_BASE_EXTENTS := by
    rw [← hn]; exact hyes
  unfold map_id_range_down
  simp only [lift, bind_tc_ok, hyes, hyes', if_true]
  unfold map_id_range_down_base map_id_range_down_base_loop map_id_range_down_base_loop.body
  rw [hn, hex]

end UidmapSafety

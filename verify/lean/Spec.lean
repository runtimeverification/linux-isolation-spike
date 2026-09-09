-- SPDX-License-Identifier: GPL-2.0
import Uidmap
/-!
# The abstract map and `WellFormed` (SPEC.md §1)

Pure definitions over the Aeneas-extracted `UidGidMap`, plus the algebra
lemmas that F2 `INJECTIVITY` and F3 `ROUNDTRIP` reduce to. Nothing here
mentions a `Result`; this is the mathematical side.

Conventions: `W = 2^32`, and `⊥ = W - 1` is `ID_SENTINEL`. Intervals are over
`Nat`; `WellFormed.nowrap_*` is what makes that identification legitimate
(SPEC §1.2.1).
-/
open Aeneas Aeneas.Std Result WP
open uidmap

namespace UidmapSpec

/-! ## Extents as affine partial functions (SPEC §1.1) -/

/-- `x ∈ U(e) = [first, first + count)`. -/
def inU (e : UidGidExtent) (x : Nat) : Prop :=
  e.first.val ≤ x ∧ x < e.first.val + e.count.val

/-- `y ∈ L(e) = [lower_first, lower_first + count)`. -/
def inL (e : UidGidExtent) (y : Nat) : Prop :=
  e.lower_first.val ≤ y ∧ y < e.lower_first.val + e.count.val

/-- `⟦e⟧(x) = (x - first) + lower_first`, on `Nat`. -/
def apDown (e : UidGidExtent) (x : Nat) : Nat := x - e.first.val + e.lower_first.val

/-- `⟦e⟧⁻¹(y) = (y - lower_first) + first`, on `Nat`. -/
def apUp (e : UidGidExtent) (y : Nat) : Nat := y - e.lower_first.val + e.first.val

theorem apDown_inL {e : UidGidExtent} {x : Nat} (h : inU e x) : inL e (apDown e x) := by
  unfold inU inL apDown at *; omega

theorem apUp_inU {e : UidGidExtent} {y : Nat} (h : inL e y) : inU e (apUp e y) := by
  unfold inU inL apUp at *; omega

theorem apUp_apDown {e : UidGidExtent} {x : Nat} (h : inU e x) : apUp e (apDown e x) = x := by
  unfold inU apDown apUp at *; omega

theorem apDown_apUp {e : UidGidExtent} {y : Nat} (h : inL e y) : apDown e (apUp e y) = y := by
  unfold inL apDown apUp at *; omega

/-- `⟦e⟧` is injective on `U(e)`. -/
theorem apDown_injective {e : UidGidExtent} {x y : Nat} (hx : inU e x) (hy : inU e y)
    (h : apDown e x = apDown e y) : x = y := by
  unfold inU apDown at *; omega

/-- On a well-formed extent the image never reaches the sentinel
(`WF-NOSENT-IV`, SPEC §1.2.1): `lower_first + count ≤ W - 1` puts all of
`L(e)` strictly below `W - 1`. -/
theorem inL_ne_sentinel {e : UidGidExtent} {y : Nat}
    (hnw : e.lower_first.val + e.count.val ≤ 2^32 - 1) (h : inL e y) : y ≠ 2^32 - 1 := by
  unfold inL at h; omega

theorem inU_ne_sentinel {e : UidGidExtent} {x : Nat}
    (hnw : e.first.val + e.count.val ≤ 2^32 - 1) (h : inU e x) : x ≠ 2^32 - 1 := by
  unfold inU at h; omega

/-! ## The abstract map: the active arm as a list (SPEC §1.3) -/

/-- The extents the *downward* lookup consults: the base arm below 6 extents,
the `forward` heap arm above. -/
def absFwd (m : UidGidMap) : List UidGidExtent :=
  if m.nr_extents.val ≤ 5 then m.extent.val.take m.nr_extents.val
  else m.forward.val.take m.nr_extents.val

/-- The extents the *upward* lookup consults: the base arm below 6 extents,
the `reverse` heap arm above. -/
def absRev (m : UidGidMap) : List UidGidExtent :=
  if m.nr_extents.val ≤ 5 then m.extent.val.take m.nr_extents.val
  else m.reverse.val.take m.nr_extents.val

theorem absFwd_le5 {m : UidGidMap} (h : m.nr_extents.val ≤ 5) :
    absFwd m = m.extent.val.take m.nr_extents.val := by simp [absFwd, h]
theorem absFwd_gt5 {m : UidGidMap} (h : 5 < m.nr_extents.val) :
    absFwd m = m.forward.val.take m.nr_extents.val := by
  simp [absFwd, show ¬ m.nr_extents.val ≤ 5 by omega]
theorem absRev_le5 {m : UidGidMap} (h : m.nr_extents.val ≤ 5) :
    absRev m = m.extent.val.take m.nr_extents.val := by simp [absRev, h]
theorem absRev_gt5 {m : UidGidMap} (h : 5 < m.nr_extents.val) :
    absRev m = m.reverse.val.take m.nr_extents.val := by
  simp [absRev, show ¬ m.nr_extents.val ≤ 5 by omega]

/-! ## `WellFormed` (SPEC §1.2)

Each field is a clause of SPEC §1.2's table. Disjointness is stated as "two
extents sharing a point are the same extent", which is what injectivity
consumes; on a duplicate-free list it is equivalent to the index form.
`rev_perm` is `WF-REVERSE-LIVE` plus the content of `A-SORT`'s permutation
half: above 5, the `reverse` arm is populated and holds the same extents as
`forward`. Sortedness is NOT part of `WellFormed`; it is `SortedArms` below,
consumed only by F4 `AGREEMENT`. -/
structure WellFormed (m : UidGidMap) : Prop where
  /-- `WF-LEN`, lower half (`map_write` 1053) -/
  len_pos : 1 ≤ m.nr_extents.val
  /-- `WF-LEN`, upper half (`map_write` 1041, `insert_extent` 789) -/
  len_le : m.nr_extents.val ≤ 340
  /-- `WF-COUNT` (from 1031) -/
  count_pos : ∀ e ∈ absFwd m, 1 ≤ e.count.val
  /-- `WF-NOWRAP-U` (1031): `≤ W - 1`, one tighter than "no wrap", SPEC §1.2.1 -/
  nowrap_u : ∀ e ∈ absFwd m, e.first.val + e.count.val ≤ 2^32 - 1
  /-- `WF-NOWRAP-L` (1033, then preserved through the re-map at 1082) -/
  nowrap_l : ∀ e ∈ absFwd m, e.lower_first.val + e.count.val ≤ 2^32 - 1
  /-- `WF-DISJ-UPPER` (`mappings_overlap` 771–774 at 1038) -/
  disj_u : ∀ e ∈ absFwd m, ∀ e' ∈ absFwd m, ∀ x, inU e x → inU e' x → e = e'
  /-- `WF-DISJ-LOWER` on the **post-remap** ids — SPEC §1.5: a theorem of the
  write path (`PRESERVE-LOWER`), not a check -/
  disj_l : ∀ e ∈ absFwd m, ∀ e' ∈ absFwd m, ∀ y, inL e y → inL e' y → e = e'
  /-- `WF-REVERSE-LIVE` + the permutation half of `A-SORT` -/
  rev_perm : 5 < m.nr_extents.val → m.reverse_live = true ∧ (absRev m).Perm (absFwd m)

/-- What `sort_idmaps` (856) establishes above 5 extents and F4 `AGREEMENT`
consumes: `forward` sorted by `first`, `reverse` by `lower_first`. Strictly, in
each case, which follows from disjointness once the map is `WellFormed`. -/
structure SortedArms (m : UidGidMap) : Prop where
  fwd : 5 < m.nr_extents.val → (absFwd m).Pairwise (fun a b => a.first.val < b.first.val)
  rev : 5 < m.nr_extents.val → (absRev m).Pairwise (fun a b => a.lower_first.val < b.lower_first.val)

/-! ## Facts every well-formed map gives about its extents -/

theorem WellFormed.mem_absRev_iff {m : UidGidMap} (hwf : WellFormed m) (e : UidGidExtent) :
    e ∈ absRev m ↔ e ∈ absFwd m := by
  by_cases h5 : m.nr_extents.val ≤ 5
  · rw [absRev_le5 h5, absFwd_le5 h5]
  · have := (hwf.rev_perm (by omega)).2
    exact this.mem_iff

/-- The clause `WF-NOSENT-IV`, derived: no extent of a well-formed map maps
anything to the sentinel. This is what makes `⊥` an unambiguous failure code
(SPEC §4.3). -/
theorem WellFormed.apDown_ne_sentinel {m : UidGidMap} (hwf : WellFormed m)
    {e : UidGidExtent} (he : e ∈ absFwd m) {x : Nat} (hx : inU e x) :
    apDown e x ≠ 2^32 - 1 :=
  inL_ne_sentinel (hwf.nowrap_l e he) (apDown_inL hx)

/-- The abstract algebra behind F2: two extents of a well-formed map that
send `x` and `y` to the same image are the same extent, and then `x = y`. -/
theorem WellFormed.abs_injective {m : UidGidMap} (hwf : WellFormed m)
    {e e' : UidGidExtent} (he : e ∈ absFwd m) (he' : e' ∈ absFwd m)
    {x y : Nat} (hx : inU e x) (hy : inU e' y) (h : apDown e x = apDown e' y) : x = y := by
  have hee' : e = e' :=
    hwf.disj_l e he e' he' (apDown e x) (apDown_inL hx) (h ▸ apDown_inL hy)
  subst hee'
  exact apDown_injective hx hy h

/-- The abstract algebra behind F3: an extent `e'` that contains the image of
`x` under `e` is `e` itself, so applying it upward returns `x`. -/
theorem WellFormed.abs_roundtrip {m : UidGidMap} (hwf : WellFormed m)
    {e e' : UidGidExtent} (he : e ∈ absFwd m) (he' : e' ∈ absFwd m)
    {x : Nat} (hx : inU e x) (hk : inL e' (apDown e x)) : apUp e' (apDown e x) = x := by
  have hee' : e' = e := hwf.disj_l e' he' e he (apDown e x) hk (apDown_inL hx)
  subst hee'
  exact apUp_apDown hx

/-! ## The initial namespace (SPEC §1.2.2, §7.10) is well-formed

`init_user_ns.uid_map = { (0, 0, 4294967295) }`, `nr_extents = 1`. Note
`count = W - 1`, so `first + count = W - 1 ≤ W - 1` holds with nothing to
spare: this is the extent that shows the bound in `nowrap_u` is the right one.
Base case of `A-PARENT-WF`. -/
theorem init_user_ns_map_wf :
    ∀ m, UidGidMap.init_user_ns_map = ok m → WellFormed m := by
  intro m hm
  simp only [UidGidMap.init_user_ns_map, UidGidMap.zeroed, bind_tc_ok] at hm
  -- the single Array.update in the initializer is total (index 0 < 5)
  set z : UidGidExtent := { first := 0#u32, lower_first := 0#u32, count := 0#u32 } with hz
  set e0 : UidGidExtent := { first := 0#u32, lower_first := 0#u32, count := 4294967295#u32 } with he0
  have hb : (0#usize).val < (Array.repeat 5#usize z).length := by simp [Array.length]
  obtain ⟨a, ha, hset⟩ := spec_imp_exists (Array.update_spec (Array.repeat 5#usize z) 0#usize e0 hb)
  rw [ha] at hm
  simp only [bind_tc_ok, ok.injEq] at hm
  -- the active arm is exactly [e0]
  have habs : absFwd m = [e0] := by
    rw [← hm]
    simp only [absFwd]
    simp [hset, Array.set, Array.repeat, List.replicate, List.set, List.take]
  have hn : m.nr_extents.val = 1 := by rw [← hm]; simp
  have hrl : m.reverse_live = false := by rw [← hm]
  refine ⟨by omega, by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro e he; rw [habs] at he; simp at he; subst he; simp [he0]
  · intro e he; rw [habs] at he; simp at he; subst he; simp [he0]
  · intro e he; rw [habs] at he; simp at he; subst he; simp [he0]
  · intro e he e' he' x _ _; rw [habs] at he he'; simp at he he'; rw [he, he']
  · intro e he e' he' y _ _; rw [habs] at he he'; simp at he he'; rw [he, he']
  · intro h; omega

end UidmapSpec

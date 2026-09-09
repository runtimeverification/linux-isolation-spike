# VERIFY-REPORT — Phase 3

**Model:** the results below are in **Model T** (`SPEC.md` §1.3): `struct
uid_gid_map`'s union is two separate arms, and `insert_extent` reproduces the
clobber the two pointer stores inflict on `extent[0]` and `extent[1].first`.
The Model F fallback was **not** used. The one Aeneas blocker encountered
(B-1, `OPEN_CHALLENGES.md`) is unrelated to the union and was worked around by
a semantics-preserving by-value parameter in `cmp_map_id`.

**Toolchain:** Charon `909ff09` (LLBC v0.1.220, `--preset=aeneas`), Aeneas
`c2015b86` (`~/aeneas-project/aeneas/bin/aeneas`), Lean/mathlib `v4.31.0`,
rustc 1.94.0. Kernel reference `~/linux-full` at `v7.2-rc7-687-ge172eee25cfe`.

**Status by step (the brief's order):**

| Step | Content | State |
|---|---|---|
| 1 | crate skeleton and data model | done |
| 2 | `down`/`up`, both lookup paths, Charon→Aeneas→Lean round trip | done — 15 defs, 0 `sorry` in generated code |
| 3 | S1–S4 safety, plus S5 | **done — 28 theorems, 0 `sorry`, axiom-clean** |
| 4 | F2 `INJECTIVITY`, F3 `ROUNDTRIP`, F5 `PRESERVE` | **F2 proved; F3 soundness proved, completeness proved below 6 extents; F5 reduced to two named loop lemmas** — see §1b, §2 |
| 5 | F4 `AGREEMENT` | not started |
| 6 | F6 `ADMISSION` + 3 lemmas | not started |

Nothing in steps 5–6 is claimed. The words "proved" and "verified" below refer
only to theorems in `verify/lean/{Safety,Spec,Algebra,WritePath}.lean` that the
audit in §4 shows free of `sorryAx`.

---

## 1. What is proved (step 3) — `sorry`-free

All in `verify/lean/Safety.lean`, against the generated `verify/lean/Uidmap.lean`.
`x ⦃ _ => True ⦄` is `WP.spec x (fun _ => True)`, which is false at `fail` and
at `div`; so it states *no panic and termination* at once
(`spec_true_iff_ok` makes the reading explicit).

### S1 — TOTAL-SAFETY

| Theorem | Statement |
|---|---|
| `total_safety` | for every `Result`, `ok ∨ fail ∨ div` — the enumeration is complete |
| `map_id_down_total_safety`, `map_id_up_total_safety`, `map_id_range_down_total_safety`, `map_id_range_up_total_safety`, `insert_extent_total_safety` | instances for the public entry points |

Unconditional. Content-free as a proof; the content is that every array
access in the model is a checked `index_usize` returning `fail` on a bad index
— the memory-safety property the C lacks, stated.

### S2 + S3 — NO-PANIC and TERMINATION, lookups

| Theorem | Hypothesis | What it says |
|---|---|---|
| `cmp_map_id_spec` | none | the comparison predicate is total |
| `map_id_range_down_base_loop_spec`, `_up_base_loop_spec` | `extents ≤ 5`, `idx ≤ extents` | the linear scans terminate and never index out of `extent[5]`; measure `extents - idx` |
| `map_id_range_down_base_spec`, `_up_base_spec` | `extents ≤ 5` | wrappers |
| `bsearch_extent_loop_spec` | `lo + num ≤ 340` | the monomorphized `__inline_bsearch` terminates and never indexes out of the 340-slot array; measure `num`; the invariant is re-established across **both** branches, including the `num--; num >>= 1` one (SPEC §4.4 obligation 2) |
| `bsearch_extent_spec` | `nmemb ≤ 340` | wrapper |
| `map_id_range_down_spec`, `map_id_range_up_spec` | **`nr_extents ≤ 340`** | the dispatching lookups return `ok` |
| `map_id_down_spec`, `map_id_up_spec`, `make_kuid_spec`, `from_kuid_spec` | `nr_extents ≤ 340` | corollaries |

**Result worth stating:** the lookup path's memory safety needs *exactly one*
clause of `WellFormed` — the upper half of `WF-LEN`, established by
`map_write` 1041 — and no arithmetic clause. The `≤ 5` scan needs nothing;
the `> 5` binary search needs the array bound, because with `nr_extents > 340`
the C's `bsearch` reads past the heap array. SPEC §2 predicted "on a
`WellFormed` map"; the proof shows which part of it. Recorded in SPEC §9.4.

### S2 + S3 — NO-PANIC and TERMINATION, write-path constructor

| Theorem | Hypothesis | What it says |
|---|---|---|
| `cast_usize_val` | none | `u32 as usize` never truncates |
| `insert_extent_loop_spec` | `i ≤ 5`, `i1 ≤ i` | the migration memcpy loop terminates and stays inside `extent[5]` / `forward[340]` |
| `insert_extent_spec` | **`nr_extents < 340`** | returns `0` and `nr_extents + 1`; no out-of-bounds write in any of the three branches (base insert, migration + heap insert at index 5, heap insert at `nr_extents`) |

The hypothesis is the exact boundary `map_write` 1041 enforces (insert is only
reached with `nr_extents ≤ 339`), and the theorem is the statement that the
`+1` at `insert_extent` 819 is not an off-by-one write into `forward[340]`.

### S4 — NO-OVERFLOW, the arithmetic bridge

| Theorem | Hypotheses | What it says |
|---|---|---|
| `last_val` | `count ≥ 1` (`WF-COUNT`), `first + count ≤ U32.max` (`WF-NOWRAP`) | the `u32`-wrapping `first + count - 1` equals the mathematical value |
| `id2_val` | same, on the key | the caller-supplied `id + count - 1` likewise |

These are the *content* of S4. SPEC §4.1's `no_overflow_upper` as literally
stated is a projection of `WellFormed` and lands with that definition in step 4;
what the wrapping sites need is exactly these two lemmas, and they are what
F1/F2 will consume.

### S5 — NO-STALE-READ (Model T)

| Theorem | Hypotheses | What it says |
|---|---|---|
| `no_stale_read_down` | `5 < nr_extents`, equal `forward`, equal `nr_extents` | the downward lookup does not depend on the base arm |
| `no_stale_read_up` | `5 < nr_extents`, equal `reverse`, equal `nr_extents` | the upward lookup does not depend on the base arm |
| `base_arm_only_down` | `nr_extents ≤ 5`, equal `extent`, equal `nr_extents` | below 5, the heap arms are not consulted |

Non-interference: perturbing `extent[]` arbitrarily — which is what the clobber
does — changes no lookup on a heap-arm map. **What this does and does not
replace.** It proves the *model's* dispatch never reads the base arm above 5.
Whether the *C* never reads `extent[]` after migration remains a claim about
the C; what S5 does is shrink `A-UNION` from a semantic assumption ("no stale
read happens") to a structural-correspondence check ("the model's four
`nr_extents ≤ 5` dispatch sites mirror the C's at 324, 390, 761, 899") that is
verifiable by side-by-side reading and exercised by the Phase 4 harness. That
is a real reduction, not an elimination, and §3 records it as such.

## 2. What is NOT proved (step 3)

No theorem in `Safety.lean` carries `sorry`. The table of `sorry`-carrying
results is therefore **empty** for this step. Statements SPEC lists that are
not yet stated in Lean at all — F1–F6 — are simply not started; they are not
"in progress with gaps".

---

## 3. Theorem × assumption matrix — regenerated from the proofs

Columns are `SPEC.md` §3's named assumptions plus the concrete hypotheses the
theorems actually carry. ✔ = the theorem's *relevance to the C* rests on it;
**H** = it appears as an explicit hypothesis in the Lean statement; — = not
needed.

| Theorem group | `A-PUB` | `A-UNION` | `A-SORT` | `A-BSEARCH` | `A-CAPORACLE` | `A-PARENT-WF` | explicit Lean hypotheses |
|---|:--:|:--:|:--:|:--:|:--:|:--:|---|
| S1 `*_total_safety` | — | — | — | — | — | — | none |
| S3/S2 base scans | ✔ | ✔* | — | — | — | — | `extents ≤ 5` |
| S3/S2 `bsearch_extent*` | ✔ | ✔* | — | ✔ | — | — | `lo + num ≤ 340` / `nmemb ≤ 340` |
| S3/S2 `map_id_range_{down,up}_spec` + corollaries | ✔ | ✔* | — | ✔ | — | — | **`nr_extents ≤ 340`** |
| S3/S2 `insert_extent*_spec` | ✔ | ✔* | — | — | — | — | `nr_extents < 340`; loop: `i ≤ 5` |
| S4 `last_val`, `id2_val` | — | — | — | — | — | — | `count ≥ 1`, `first + count ≤ U32.max` |
| S5 `no_stale_read_*`, `base_arm_only_down` | ✔ | (is the replacement) | — | — | — | — | `5 < nr_extents` / `≤ 5`, arm equalities |

\* `A-UNION` in its **reduced** form: Model T's dispatch mirrors the C's four
`nr_extents ≤ 5` sites. S5 is what performs the reduction.

Reading the matrix against SPEC §5's prediction:

- **Less needed than predicted:** S2/S3 for lookups needs `WF-LEN`'s upper
  half only, not `WellFormed`. SPEC §5 had S2 conditional on `A-PUB` and
  `A-UNION`; that stands, in the sense that a *C reader* sees a consistent
  map only under `A-PUB`, but the Lean statements themselves carry only the
  array bound.
- **Nothing needed that was not predicted.** `insert_extent_spec`'s
  `nr_extents < 340` is the pre-install form of `WF-LEN`, implicit in SPEC §1.2
  ("upper: 1041 + `insert_extent` 789") and now explicit.
- **`A-PUB` is on every S2/S3/S5 row** and is not discharged. It cannot be,
  with this tool. See §5.

---

---

## 1b. What is proved (step 4) — `sorry`-free

Files: `verify/lean/Spec.lean` (the abstract map and `WellFormed`),
`verify/lean/Algebra.lean` (lookups, F2, F3), `verify/lean/WritePath.lean`
(F5). Everything in this section is free of `sorryAx` per §4.

### The abstract map and `WellFormed` (Spec.lean)

`absFwd m` / `absRev m` read the active union arm as a list — the base arm
below 6 extents, `forward` / `reverse` above. `WellFormed m` is SPEC §1.2's
table as a structure, every clause traced to the C line that establishes it
(`len_pos`, `len_le`, `count_pos`, `nowrap_u`, `nowrap_l`, `disj_u`, `disj_l`,
`rev_perm`). Sortedness is **not** in `WellFormed`; it is the separate
`SortedArms`, consumed only by F4.

| Theorem | Says |
|---|---|
| `apDown_inL`, `apUp_inU`, `apUp_apDown`, `apDown_apUp`, `apDown_injective` | an extent is a translation: bijective between `U(e)` and `L(e)` |
| `inL_ne_sentinel`, `inU_ne_sentinel` | `WF-NOSENT-IV`: under `nowrap`, no interval reaches `⊥` |
| `WellFormed.mem_absRev_iff` | above 5 the two arms hold the same extents (from `rev_perm`) |
| `WellFormed.abs_injective`, `WellFormed.abs_roundtrip` | the pure algebra F2 and F3 reduce to |
| **`init_user_ns_map_wf`** | the initial namespace's map, read off `kernel/user.c` 39–48, is `WellFormed` — **base case of `A-PARENT-WF`**; `count = 2^32 − 1` makes `nowrap_u` hold with nothing to spare |

### F1 — functional soundness of both lookup paths (Algebra.lean)

| Theorem | Hypotheses | Says |
|---|---|---|
| `id2_one_val`, `down_result_val`, `up_result_val` | `inU`/`inL`, `nowrap` | the `u32` result arithmetic at :331/:397 equals `apDown`/`apUp` |
| `cmp_map_id_zero_down`, `cmp_map_id_zero_up` | — | `cmp_map_id = 0` gives the four C comparisons |
| `base_loop_down_fun`, `base_loop_up_fun` | `extents ≤ 5`, prefix `count ≥ 1 ∧ nowrap` | the linear scans are **sound and complete**: `some e` is a containing extent of the prefix, `none` means none contains both ends |
| `bsearch_loop_sound` | `lo + num ≤ n ≤ 340` | the binary search is **sound with no sortedness**: it only ever returns an element `cmp_map_id` called `0` on |
| `cmp_zero_inU`, `cmp_zero_inL`, `cmp_zero_inU_range` | `count = 1` / general | containment from `cmp_map_id = 0` |
| **`down_sound`**, **`up_sound`** | `WellFormed` | single-id lookups: the result is `⊥` or the image of the input under a containing extent of the active arm — both paths |
| **`down_range_sound`** (WritePath.lean) | `WellFormed parent`, `count ≥ 1`, `id + count ≤ 2^32−1` | the range form used by the re-map at 1072: the result is `⊥` or the image under a parent extent containing the **whole** range |

### F2 — INJECTIVITY

```lean
theorem down_injective (m : UidGidMap) (hwf : WellFormed m) (x y v : U32)
    (hx : map_id_down m x = ok v) (hy : map_id_down m y = ok v) (hv : v ≠ ID_SENTINEL) : x = y
```
**Proved, `sorry`-free, for both lookup paths.** It needs soundness only —
whichever extent the binary search returned, disjointness of the lower
intervals pins it down. SPEC §4.2's operational reading stands: two distinct
container ids cannot resolve to one host id on a `WellFormed` map.

### F3 — ROUNDTRIP, split as SPEC §4.3 anticipated

| Theorem | Status | Says |
|---|---|---|
| **`roundtrip_sound`** | **proved, both paths** | `up (down x)` is `x` or `⊥`, **never an unrelated id** — the "containment" property of the brief |
| **`roundtrip_complete_le5`** | **proved** | below 6 extents, `up` on a successful `down` never returns `⊥` |
| `roundtrip_complete` | `sorry` above 5 (§2) | the same for every map; rests on `bsearch_complete` |

### F5 — PRESERVE (WritePath.lean): what is closed

| Theorem | Says |
|---|---|
| `remap_disjoint` | **PRESERVE-LOWER, the induction step, pure**: two lower-disjoint extents, each re-mapped through a parent extent containing its whole lower range, stay lower-disjoint — because the parent's lower intervals are disjoint and each parent extent is a translation |
| `preserve_lower_list` | the same on lists: a `PreRemap` list `Remapped` through a `WellFormed` parent has pairwise-disjoint lower intervals — the clause `mappings_overlap` could not check because it ran before the re-map (SPEC §1.5) |
| `insert_extent_loop_fun`, `insert_extent_fun` | `insert_extent` **appends** to the abstract map, through all three branches including the migration at `nr_extents == 5` |
| `overlapsU_iff`, `overlapsL_iff`, `dispatch_read`, `mappings_overlap_loop_fun`, `mappings_overlap_fun` | `mappings_overlap` says `false` only when the candidate is disjoint from every inserted extent in **both** coordinates |
| `nowrap_check_iff` | the C's `u32` test `(first + count) <= first` at 1031/1033 accepts exactly `count ≥ 1 ∧ first + count ≤ 2^32−1` — SPEC §1.2.1, now a theorem |
| `preRemap_append`, `nodup_append_of_disjoint`, `overlaps_self` | the accumulating invariant extends by an accepted extent |
| **`lines_loop_fun`** | the line loop of `map_write_body` (992–1049): after `k` accepted lines the abstract map is exactly those lines, `PreRemap`, duplicate-free; the exact **340 boundary of 1041** is carried as `i < 340 ∨ i = len`; on exhaustion it hands off to `remap_install_fun` — *inherits that lemma's `sorry`, contributes none of its own* |
| **`write_preserves_wf`** | F5 assembled: success forces the write-once (980) and capability (986) checks to have passed, so **no hypothesis on the target map is needed** — *inherits* |
| `Reachable`, **`reachable_wf`** | the induction on namespace depth: `init_user_ns_map_wf` is the base case, `write_preserves_wf` the step — *inherits* |

## 2. What is NOT proved (steps 4–5) — the `sorry` table

Seven declarations carry `sorryAx` (§4). Two are genuine step-5 gaps, two are
genuine F5 gaps, three inherit.

| Declaration | Kind | What is missing | Why it is a gap |
|---|---|---|---|
| `bsearch_complete` (Algebra) | step-5 gap | completeness of the monomorphized `__inline_bsearch`: if a sorted, disjoint prefix has an extent containing the id, the search finds one | needs `SortedArms` + disjointness to make `cmp_map_id` monotone along the array (SPEC §4.4 obligation 1) and the window invariant for the hit — this **is** the core of F4 `AGREEMENT` |
| `roundtrip_complete` (Algebra) | inherits | the `> 5` branch only | reduces to `bsearch_complete` on `reverse` |
| `sort_idmaps_fun` (WritePath) | F5 gap | `sort_idmaps` permutes `forward` in place, fills `reverse` with a permutation of it, sets `reverse_live`, leaves `nr_extents`/`extent` alone | a permutation proof for the insertion sort standing in for `lib/sort.c` under `A-SORT`; no kernel-specific content, two nested Aeneas loops |
| `remap_install_fun` (WritePath) | F5 gap | the re-map loop and tail of `map_write_body` (1063–1102): from a `PreRemap`, duplicate-free `new_map`, either fail negative or install a `WellFormed` map | the loop invariant "positions `< idx` re-mapped, positions `≥ idx` original" over the union-dispatched write-back at 1082, then `preserve_lower_list` + `down_range_sound` for `disj_l`, `sort_idmaps_fun` for `rev_perm`, and the install memcpy loop; the mathematics is done (`preserve_lower_list`), the loop plumbing is not |
| `lines_loop_fun` (WritePath) | inherits | — | own proof complete; calls `remap_install_fun` on exhaustion |
| `write_preserves_wf` (WritePath) | inherits | — | own proof complete; calls `lines_loop_fun` |
| `reachable_wf` (WritePath) | inherits | — | own proof complete; calls `write_preserves_wf` |

Nothing in this table is described as proved anywhere in this repository.

## 3b. Theorem × assumption matrix — step 4, regenerated from the proofs

| Theorem group | `A-PUB` | `A-UNION`* | `A-SORT` | `A-BSEARCH` | `A-CAPORACLE` | `A-PARENT-WF` | explicit Lean hypotheses |
|---|:--:|:--:|:--:|:--:|:--:|:--:|---|
| Spec algebra lemmas | — | — | — | — | — | — | `inU`/`inL`, `nowrap` |
| `init_user_ns_map_wf` | — | — | — | — | — | (is the base case) | none |
| F1 `down_sound`, `up_sound`, `down_range_sound` | ✔ | ✔* | ✔ (perm half, via `rev_perm`) | ✔ | — | — | `WellFormed m` |
| F2 `down_injective` | ✔ | ✔* | ✔ (perm half) | ✔ | — | — | `WellFormed m`, `v ≠ ⊥` |
| F3 `roundtrip_sound` | ✔ | ✔* | ✔ (perm half) | ✔ | — | — | `WellFormed m` |
| F3 `roundtrip_complete_le5` | ✔ | ✔* | — | — | — | — | `WellFormed m`, `nr_extents ≤ 5` |
| F3 `roundtrip_complete` (>5) | ✔ | ✔* | ✔ (both halves) | ✔ | — | — | + `SortedArms m` — **`sorry`** |
| F5 `remap_disjoint`, `preserve_lower_list` | — | — | — | — | — | ✔ | `WellFormed parent`, `PreRemap L`, `Remapped`, `Nodup` |
| F5 `insert_extent_fun`, `mappings_overlap_fun`, `lines_loop_fun` | ✔ | ✔* | — | — | ✔ (`permitted`, `cap_ok` are inputs) | ✔ | `nr_extents < 340` / invariant |
| F5 `write_preserves_wf`, `reachable_wf` | ✔ | ✔* | ✔ (via `sort_idmaps_fun`) | ✔ | ✔ | ✔ | none on the target map — **inherit `sorry`** |

\* reduced form (§1 S5).

Read against SPEC §5: `A-SORT` now appears in F1–F3 through `WellFormed.rev_perm`
— the permutation half of the sort contract was folded into `WellFormed`
because F1 needs the `reverse` arm to hold the same extents as `forward`; SPEC
had it only under F4. That is a result: the *soundness* of the upward lookup
above 5 extents depends on `reverse` being a permutation of `forward`, not
merely on its being sorted. Nothing else needed an assumption SPEC did not
predict. `write_preserves_wf` needed **fewer** hypotheses than SPEC §4.5
stated (none on the target map).

---

## 4. Axiom audit (`verify/lean/axioms.sh` → `verify/lean/axioms-step4.txt`)

Expected on every line: `[propext, Classical.choice, Quot.sound]`. Any fourth
axiom, in particular `sorryAx`, is a stop-and-report. Result: **93 declarations audited. 86 are on the standard three axioms or a
strict subset of them. Exactly 7 carry `sorryAx`, and they are exactly the
rows of §2.** No other axiom appears anywhere.

Note on the trusted base: `lake build` reports `declaration uses 'sorry'` at
`Aeneas/Std/Slice.lean:363`, `Slice.lean:586`, `StringIter.lean:13` — in the
Aeneas standard library's `get_unchecked` specs. The audit below is the
empirical statement that nothing in this project reaches them; the model uses
`Array _ 5#usize` / `Array _ 340#usize` with checked indexing and no `Slice`.
This is re-run after every change, never assumed.

### 4.1 The generated model (`Uidmap.lean`)

| Declaration | Axioms |
|---|---|
| `uidmap.cmp_map_id` | `[propext, Classical.choice, Quot.sound]` |
| `uidmap.bsearch_extent` | `[propext, Classical.choice, Quot.sound]` |
| `uidmap.map_id_range_down_base` | `[propext, Classical.choice, Quot.sound]` |
| `uidmap.map_id_range_down_max` | `[propext, Classical.choice, Quot.sound]` |
| `uidmap.map_id_range_down` | `[propext, Classical.choice, Quot.sound]` |
| `uidmap.map_id_down` | `[propext, Classical.choice, Quot.sound]` |
| `uidmap.map_id_range_up_base` | `[propext, Classical.choice, Quot.sound]` |
| `uidmap.map_id_range_up_max` | `[propext, Classical.choice, Quot.sound]` |
| `uidmap.map_id_range_up` | `[propext, Classical.choice, Quot.sound]` |
| `uidmap.map_id_up` | `[propext, Classical.choice, Quot.sound]` |
| `uidmap.make_kuid` | `[propext, Classical.choice, Quot.sound]` |
| `uidmap.from_kuid` | `[propext, Classical.choice, Quot.sound]` |
| `uidmap.insert_extent` | `[propext, Classical.choice, Quot.sound]` |
| `uidmap.UidGidMap.zeroed` | `[propext, Classical.choice, Quot.sound]` |
| `uidmap.UidGidMap.init_user_ns_map` | `[propext, Classical.choice, Quot.sound]` |

### 4.2 Safety (`Safety.lean`)

| Declaration | Axioms |
|---|---|
| `UidmapSafety.total_safety` | `[propext, Quot.sound]` |
| `UidmapSafety.map_id_down_total_safety` | `[propext, Classical.choice, Quot.sound]` |
| `UidmapSafety.map_id_up_total_safety` | `[propext, Classical.choice, Quot.sound]` |
| `UidmapSafety.map_id_range_down_total_safety` | `[propext, Classical.choice, Quot.sound]` |
| `UidmapSafety.map_id_range_up_total_safety` | `[propext, Classical.choice, Quot.sound]` |
| `UidmapSafety.insert_extent_total_safety` | `[propext, Classical.choice, Quot.sound]` |
| `UidmapSafety.spec_true_iff_ok` | `[propext, Quot.sound]` |
| `UidmapSafety.cmp_map_id_spec` | `[propext, Classical.choice, Quot.sound]` |
| `UidmapSafety.last_val` | `[propext, Classical.choice, Quot.sound]` |
| `UidmapSafety.id2_val` | `[propext, Classical.choice, Quot.sound]` |
| `UidmapSafety.map_id_range_down_base_loop_spec` | `[propext, Classical.choice, Quot.sound]` |
| `UidmapSafety.map_id_range_up_base_loop_spec` | `[propext, Classical.choice, Quot.sound]` |
| `UidmapSafety.map_id_range_down_base_spec` | `[propext, Classical.choice, Quot.sound]` |
| `UidmapSafety.map_id_range_up_base_spec` | `[propext, Classical.choice, Quot.sound]` |
| `UidmapSafety.bsearch_extent_loop_spec` | `[propext, Classical.choice, Quot.sound]` |
| `UidmapSafety.bsearch_extent_spec` | `[propext, Classical.choice, Quot.sound]` |
| `UidmapSafety.map_id_range_down_spec` | `[propext, Classical.choice, Quot.sound]` |
| `UidmapSafety.map_id_range_up_spec` | `[propext, Classical.choice, Quot.sound]` |
| `UidmapSafety.map_id_down_spec` | `[propext, Classical.choice, Quot.sound]` |
| `UidmapSafety.map_id_up_spec` | `[propext, Classical.choice, Quot.sound]` |
| `UidmapSafety.make_kuid_spec` | `[propext, Classical.choice, Quot.sound]` |
| `UidmapSafety.from_kuid_spec` | `[propext, Classical.choice, Quot.sound]` |
| `UidmapSafety.insert_extent_loop_spec` | `[propext, Classical.choice, Quot.sound]` |
| `UidmapSafety.insert_extent_spec` | `[propext, Classical.choice, Quot.sound]` |
| `UidmapSafety.no_stale_read_down` | `[propext, Classical.choice, Quot.sound]` |
| `UidmapSafety.no_stale_read_up` | `[propext, Classical.choice, Quot.sound]` |
| `UidmapSafety.base_arm_only_down` | `[propext, Classical.choice, Quot.sound]` |

### 4.3 Spec (`Spec.lean`)

| Declaration | Axioms |
|---|---|
| `UidmapSpec.apDown_inL` | `[propext, Classical.choice, Quot.sound]` |
| `UidmapSpec.apUp_apDown` | `[propext, Quot.sound]` |
| `UidmapSpec.apDown_injective` | `[propext, Quot.sound]` |
| `UidmapSpec.inL_ne_sentinel` | `[propext, Quot.sound]` |
| `UidmapSpec.WellFormed.mem_absRev_iff` | `[propext, Classical.choice, Quot.sound]` |
| `UidmapSpec.WellFormed.apDown_ne_sentinel` | `[propext, Classical.choice, Quot.sound]` |
| `UidmapSpec.WellFormed.abs_injective` | `[propext, Classical.choice, Quot.sound]` |
| `UidmapSpec.WellFormed.abs_roundtrip` | `[propext, Classical.choice, Quot.sound]` |
| `UidmapSpec.init_user_ns_map_wf` | `[propext, Classical.choice, Quot.sound]` |

### 4.4 Algebra (`Algebra.lean`) — `sorryAx` on `bsearch_complete`, `roundtrip_complete` only

| Declaration | Axioms |
|---|---|
| `UidmapAlgebra.id2_one_val` | `[propext, Classical.choice, Quot.sound]` |
| `UidmapAlgebra.down_result_val` | `[propext, Classical.choice, Quot.sound]` |
| `UidmapAlgebra.up_result_val` | `[propext, Classical.choice, Quot.sound]` |
| `UidmapAlgebra.cmp_map_id_zero_down` | `[propext, Classical.choice, Quot.sound]` |
| `UidmapAlgebra.cmp_map_id_zero_up` | `[propext, Classical.choice, Quot.sound]` |
| `UidmapAlgebra.base_loop_down_fun` | `[propext, Classical.choice, Quot.sound]` |
| `UidmapAlgebra.base_loop_up_fun` | `[propext, Classical.choice, Quot.sound]` |
| `UidmapAlgebra.bsearch_loop_sound` | `[propext, Classical.choice, Quot.sound]` |
| `UidmapAlgebra.cmp_zero_inU` | `[propext, Classical.choice, Quot.sound]` |
| `UidmapAlgebra.cmp_zero_inL` | `[propext, Classical.choice, Quot.sound]` |
| `UidmapAlgebra.down_sound` | `[propext, Classical.choice, Quot.sound]` |
| `UidmapAlgebra.up_sound` | `[propext, Classical.choice, Quot.sound]` |
| `UidmapAlgebra.down_injective` | `[propext, Classical.choice, Quot.sound]` |
| `UidmapAlgebra.roundtrip_sound` | `[propext, Classical.choice, Quot.sound]` |
| `UidmapAlgebra.roundtrip_complete_le5` | `[propext, Classical.choice, Quot.sound]` |
| `UidmapAlgebra.bsearch_complete` | `[propext, sorryAx, Classical.choice, Quot.sound]` |
| `UidmapAlgebra.roundtrip_complete` | `[propext, sorryAx, Classical.choice, Quot.sound]` |

### 4.5 WritePath (`WritePath.lean`) — `sorryAx` on `sort_idmaps_fun`, `remap_install_fun` and the three that inherit

| Declaration | Axioms |
|---|---|
| `UidmapWritePath.inL_remap` | `[propext, Classical.choice, Quot.sound]` |
| `UidmapWritePath.remap_disjoint` | `[propext, Classical.choice, Quot.sound]` |
| `UidmapWritePath.take_set_of_le` | `[propext, Quot.sound]` |
| `UidmapWritePath.take_add_one_of_getElem` | `[propext]` |
| `UidmapWritePath.take_set_succ` | `[propext, Quot.sound]` |
| `UidmapWritePath.insert_extent_loop_fun` | `[propext, Classical.choice, Quot.sound]` |
| `UidmapWritePath.insert_extent_fun` | `[propext, Classical.choice, Quot.sound]` |
| `UidmapWritePath.overlapsU_iff` | `[propext, Classical.choice, Quot.sound]` |
| `UidmapWritePath.overlapsL_iff` | `[propext, Classical.choice, Quot.sound]` |
| `UidmapWritePath.dispatch_read` | `[propext, Classical.choice, Quot.sound]` |
| `UidmapWritePath.mappings_overlap_loop_fun` | `[propext, Classical.choice, Quot.sound]` |
| `UidmapWritePath.mappings_overlap_fun` | `[propext, Classical.choice, Quot.sound]` |
| `UidmapWritePath.preserve_lower_list` | `[propext, Classical.choice, Quot.sound]` |
| `UidmapWritePath.cmp_zero_inU_range` | `[propext, Classical.choice, Quot.sound]` |
| `UidmapWritePath.down_range_sound` | `[propext, Classical.choice, Quot.sound]` |
| `UidmapWritePath.nowrap_check_iff` | `[propext, Classical.choice, Quot.sound]` |
| `UidmapWritePath.overlaps_self` | `[propext, Classical.choice, Quot.sound]` |
| `UidmapWritePath.preRemap_append` | `[propext, Classical.choice, Quot.sound]` |
| `UidmapWritePath.nodup_append_of_disjoint` | `[propext, Classical.choice, Quot.sound]` |
| `UidmapWritePath.sort_idmaps_fun` | `[propext, sorryAx, Classical.choice, Quot.sound]` |
| `UidmapWritePath.remap_install_fun` | `[propext, sorryAx, Classical.choice, Quot.sound]` |
| `UidmapWritePath.lines_loop_fun` | `[propext, sorryAx, Classical.choice, Quot.sound]` |
| `UidmapWritePath.write_preserves_wf` | `[propext, sorryAx, Classical.choice, Quot.sound]` |
| `UidmapWritePath.reachable_wf` | `[propext, sorryAx, Classical.choice, Quot.sound]` |

---

## 5. What these results do NOT cover

First on the list, as required.

1. **Barrier discipline and concurrency — `A-PUB`.** Every S2/S3/S5 theorem is
   about a map *value*. The C's lock-free reader (`nr_extents`, `smp_rmb()` at
   322/388, extents) paired with the writer (extents, `smp_wmb()` at 1101,
   `nr_extents` at 1102, write-once at 980) is what makes that value
   well-defined for a concurrent reader, and **a sequential Aeneas model cannot
   express it**. Nobody reading this report should conclude the publication
   protocol was checked. It was not; it needs a memory-model tool.
2. **The C's NULL-`reverse` hazard is invisible to Model T** (SPEC §9.4). The
   model's `reverse` array always exists, so `map_id_range_up_spec` needed no
   `reverse_live` hypothesis — not because the hazard is harmless but because
   the model cannot exhibit it. `WF-REVERSE-LIVE` is a C-level clause,
   discharged sequentially by writer enumeration (`OPEN_CHALLENGES.md` S-5),
   and observable only in the Phase 4 harness under ASan.
   **[NEEDS EMPIRICAL CHECK]** carried there.
3. **Model T's faithfulness to the union** is now a structural claim (§1, S5),
   not a proved one.
4. **`lib/sort.c`, `bsearch`'s indirect call, the capability oracle, allocation
   failure, the `__user` boundary, the parser's functional correctness,
   `gid_map`/`projid_map` admission** — unchanged from SPEC §7 items 3–9; none
   is touched by step 3.
5. **The functional gaps of §2.** F4 `AGREEMENT` (step 5) is not started; its
   core, `bsearch_complete`, is what F3's completeness above 5 extents and any
   statement that the two lookup paths agree wait on. F5 is proved down to two
   named loop lemmas; until `remap_install_fun` and `sort_idmaps_fun` are
   closed, "the write path preserves well-formedness" is **not** a result of
   this repository — `write_preserves_wf` exists as a checked *reduction*, not
   as a theorem free of `sorry`. F6 (step 6) is not started.
6. **Nodup.** F5's invariant carries `(absFwd m).Nodup`, which the C never
   states; it follows from upper-disjointness (`nodup_append_of_disjoint`) and
   is needed by `preserve_lower_list` to tell two positions apart. It is a
   proof artefact, recorded here so nobody mistakes it for a kernel invariant.

## 6. Reproduce

```sh
cd rust && cargo test --release                       # 6 sanity tests
cd rust && PATH=$HOME/charon/bin:$PATH charon cargo --preset=aeneas
~/aeneas-project/aeneas/bin/aeneas -backend lean \
    verify/llbc/uidmap-charon-909ff09a-v0.1.220.llbc -dest verify/lean/
cd verify/lean && ./setup-local.sh && lake build       # Uidmap Safety Spec Algebra WritePath
cd verify/lean && ./axioms.sh                          # 93 lines; sorryAx on exactly 7 (§2)
```

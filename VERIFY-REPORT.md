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
| 4 | F2 `INJECTIVITY`, F3 `ROUNDTRIP`, F5 `PRESERVE` | not started |
| 5 | F4 `AGREEMENT` | not started |
| 6 | F6 `ADMISSION` + 3 lemmas | not started |

Nothing in steps 4–6 is claimed. The words "proved" and "verified" below refer
only to theorems in `verify/lean/Safety.lean` that the audit in §4 covers.

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

## 4. Axiom audit (`verify/lean/axioms.sh` → `verify/lean/axioms-step3.txt`)

Expected on every line: `[propext, Classical.choice, Quot.sound]`. Any fourth
axiom, in particular `sorryAx`, is a stop-and-report. Result: **42 declarations
audited, none outside the standard three; two use the strict subset
`[propext, Quot.sound]`; `sorryAx` appears nowhere.**

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

### 4.2 The safety theorems (`Safety.lean`)

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
5. **Everything functional.** F1–F6 are not started. In particular nothing here
   says the lookups return the *right* id — only that they return one, without
   panicking, on any map with `nr_extents ≤ 340`.

## 6. Reproduce

```sh
cd rust && cargo test --release                       # 6 sanity tests
cd rust && PATH=$HOME/charon/bin:$PATH charon cargo --preset=aeneas
~/aeneas-project/aeneas/bin/aeneas -backend lean \
    verify/llbc/uidmap-charon-909ff09a-v0.1.220.llbc -dest verify/lean/
cd verify/lean && ./setup-local.sh && lake build       # Uidmap + Safety
cd verify/lean && ./axioms.sh                          # 42 lines, standard axioms
```

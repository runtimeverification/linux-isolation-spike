# Open Challenges

Every gap, blocker and unproved obligation in this spike, with enough detail to
be picked up by someone else or filed upstream. Nothing here is presented as
solved. Sections:

- **B-*** toolchain blockers, with reproducers.
- **A-*** assumptions the theorems rest on that this approach cannot discharge.
- **L-*** named lemmas that are stated but carry `sorry`.
- **S-*** scope gaps: parts of the C the model does not cover.

Toolchain for all of the below: Charon `909ff09` (LLBC v0.1.220,
`--preset=aeneas`), Aeneas `c2015b86` (`~/aeneas-project/aeneas/bin/aeneas` —
**not** `~/aeneas`, see `ROADMAP.md` §6), Lean/mathlib `v4.31.0`, rustc stable
1.94.0. Kernel reference `~/linux-full` at `v7.2-rc7-687-ge172eee25cfe`.

---

## B-1 — Aeneas: internal `Unreachable` when a bool read through a reference guards a join whose value feeds a later condition

**Status: worked around, not fixed. Worth an upstream issue.**

### What breaks

Branching on a `bool` field read *through a reference*, where the branch
produces a joined value that is then used in a subsequent branch condition,
crashes Aeneas' abstraction merging.

### Reproducer (five lines, `repro/B-1-bool-deref-join.rs`)

```rust
#![no_std]
pub struct K { pub up: bool }

pub fn repro(k: &K, x: u32, y: u32) -> u32 {
    let f: u32 = if k.up { x } else { y };
    if x >= f { 1 } else { 0 }
}
```

### Exact error

Charon succeeds (exit 0). Aeneas:

```
[Error] Unreachable
Source: 'src/lib.rs', lines 5:17-5:41
Compiler source: interp/InterpAbs.ml, line 1688

Uncaught exception:
  (Failure "Unreachable\nSource: 'src/lib.rs', lines 5:17-5:41\n
            Compiler source: interp/InterpAbs.ml, line 1688")
Raised at Aeneas__Errors.craise_opt_span in file "Errors.ml", line 120
Called from Aeneas__InterpAbs.merge_abs_conts_aux        InterpAbs.ml:1934
Called from Aeneas__InterpAbs.merge_abs_conts            InterpAbs.ml:2009
Called from Aeneas__InterpAbs.merge_abstractions         InterpAbs.ml:2114
Called from Aeneas__InterpAbs.merge_into_first_abstraction
                                                         InterpAbs.ml:2192-2193
Called from Aeneas__InterpReduceCollapse.ctx_with_info_merge_into_first_abs
                                              InterpReduceCollapse.ml:289-290
Called from Aeneas__InterpReduceCollapse.repeat_iter_borrows_merge.explore_merge
                                              InterpReduceCollapse.ml:509-510
```

The span `5:17-5:41` is `if k.up { x } else { y }`. It is a crash in
abstraction merging at a context join, not a diagnosed unsupported construct.

### Bisection — what is and is not required

Established by 30 variants (the series is preserved in this repo's history);
each row is a single-variable change from the failing case.

| Variant | Result |
|---|---|
| `bool` field read through a reference as the branch condition, joined value feeds a later condition | **fails** |
| ... with the bool first copied to a local (`let u = k.up; if u {..}`) | **fails** — copying out does not help |
| ... with the struct passed **by value** (`k: K`) | passes |
| ... with the bool passed as a **parameter** (`u: bool`) | passes |
| ... with no later use of the joined value (join is the return value) | passes |
| ... with the joined value used in *arithmetic* instead of a condition | passes |
| ... with a `u32` comparison as the branch condition instead of the bool | passes |
| ... with the bool read but the join guarded by a parameter | passes |
| two sequential `if`s with early returns, no joined value | passes |
| everything by value, no references anywhere | passes |

So all three of these are necessary: **(i)** the guard is a `bool` reached
through a reference, **(ii)** the branch joins into a value, **(iii)** that
value is later used in a condition.

### Where it bit this spike

`cmp_map_id` (`kernel/user_namespace.c` 251–275) is exactly this shape. The C
is `if (key->map_up) first = el->lower_first; else first = el->first;`
followed by `if (key->id >= first && ...)` — a bool through a pointer guarding
a join that feeds a comparison.

### Workaround applied

`IdmapKey` is `Copy` and passed to `cmp_map_id` **by value** instead of behind
a reference. Semantics-preserving: `cmp_map_id` only reads the key, and the C's
key is a stack local at both call sites (`map_id_range_down_max` 286–288,
`map_id_range_up_max` 375–377), so no aliasing or mutation is observable. It is
tagged `DEVIATION` at the definition in `rust/src/lib.rs`.

### Phase 4 consequence: two assumptions meet at one function

The by-value `IdmapKey` deviation lives in `cmp_map_id`, which is also the
function `A-BSEARCH` (the monomorphized callback) routes to the differential
harness. Two argued-not-proved seams now sit in the same 25 lines and in the
one code path — the `> 5` binary search — that small hand-written container
configs never exercise. The general fuzzing run will under-sample it: with
uniformly random maps most inputs stay on the `≤ 5` linear scan.

**Phase 4 must therefore build a dedicated corpus** for `cmp_map_id` and the
`> 5` lookup path, not rely on the general run: seed maps with 6, 7, 339 and
340 extents; keys that land exactly on `first`, on `first + count - 1`, one
past each, and on the `id + count - 1` wrap boundary; `map_up` in both
polarities; and ranges (`count > 1`) that straddle two adjacent extents. The
harness should report coverage of `bsearch`'s three branches separately, and
a divergence there is to be treated as a defect in the *model*, not the C,
until shown otherwise.

### What this is *not*

It is **not** the union blocker
([AeneasVerif/aeneas#1199](https://github.com/AeneasVerif/aeneas/issues/1199))
and **not** a Model-T-specific problem. `struct uid_gid_map`'s Model T
representation translated without complaint. B-1 would have hit Model F
identically, so it is not a reason to fall back. Recorded because a workaround
in the subject of a theorem deserves to be visible, and because the reproducer
is small enough to be useful upstream.

---

## Assumptions the theorems rest on

Restated from `SPEC.md` §3 with their disposition as of this phase. The
authoritative per-theorem breakdown is `VERIFY-REPORT.md`'s regenerated matrix.

### A-PUB — barrier discipline and concurrency. **Not discharged. Tool gap.**

`map_id_range_down`/`_up` read `nr_extents`, then `smp_rmb()`
(`kernel/user_namespace.c` 322, 388), then the extents; `map_write` writes
extents, then `smp_wmb()` (1101), then `nr_extents` (1102); write-once is
enforced at 980; `copy_mnt_idmap` (`fs/mnt_idmapping.c` 219) repeats the
pattern with `READ_ONCE` (222) and refuses `nr_extents == 0` (235). The
invariant — *non-zero `nr_extents` implies fully-initialized extent storage* —
is what makes lock-free reads sound.

A sequential Aeneas model cannot express it. This is **first on the exclusion
list** and it is a *tool* gap, not an effort gap: closing it needs a memory-model
tool (a `herd`/litmus check of the four-access pattern, or CBMC with a weak
memory model), not more Lean. Every functional theorem in this spike is about
an already-published, quiescent map. **Nobody reading our output should
conclude the publication protocol was checked.**

### A-SORT — `lib/sort.c`'s heapsort is a contract, not a model.

357 LOC of heapsort with a comparison callback and size-dispatched byte swaps;
not faithfully translatable. Abstracted to "returns a permutation of the input,
sorted by the key". Non-weakening *given* the uniqueness lemmas
(`SORT-UNIQUE-FWD` free from `WF-DISJ-UPPER`; `SORT-UNIQUE-REV` a corollary of
`PRESERVE-LOWER`). The contract itself is tested by the Phase 4 differential
harness against the real `lib/sort.c`, not proved.

### A-BSEARCH — the monomorphized binary search.

`bsearch` (`lib/bsearch.c` 31 → `include/linux/bsearch.h` 9–28) is an indirect
call through `cmp_func_t`. Monomorphized in the model; justified because the
callback target is statically unique at both call sites, and tested by the
harness, which links the real `lib/bsearch.c` with the real indirect call.
Argued and tested, **not proved**.

### A-CAPORACLE — the capability layer.

`ns_capable`, `file_ns_capable` and the `cred`/`ns` fields they read are
parameters of the model. F6 says what the admission policy computes *given* the
oracle's answers; it says nothing about whether `ns_capable` answers correctly.
That is `cap_capable_helper` (`security/commoncap.c` 68), candidate E in
`ROADMAP.md` §3 — a separate target.

### A-PARENT-WF — induction on namespace depth.

Base case is `init_user_ns`'s map, read off the initializer
(`kernel/user.c` 39–48): `(first=0, lower_first=0, count=4294967295)`,
`nr_extents=1`. Discharged for the base case; the inductive step is
`PRESERVE-LOWER` (step 4).

### A-UNION — **reduced by S5, not eliminated.**

Under Model T the two union arms are separate fields and `insert_extent`
reproduces the clobber, so "no read observes a clobbered slot" could be
stated about the model. Step 3 proved it as **S5 `NO-STALE-READ`**
(`no_stale_read_down`, `no_stale_read_up`, `base_arm_only_down` in
`verify/lean/Safety.lean`): for `nr_extents > 5` the lookups depend only on the
heap arm and `nr_extents`; for `nr_extents ≤ 5` only on the base arm.

What that does and does not buy, exactly as `VERIFY-REPORT.md` §1 S5 states
it: S5 proves the *model's* dispatch never touches the base arm above 5.
Whether the *C* never reads `extent[]` after migration is still a claim about
the C. S5 shrinks that claim from a semantic one ("no stale read happens") to a
**structural-correspondence check**: the model's four `nr_extents ≤ 5` dispatch
sites must mirror the C's at `kernel/user_namespace.c` 324 (`map_id_range_down`),
390 (`map_id_range_up`), 761 (`mappings_overlap`) and 899 (`verify_root_map`).
That check is done by side-by-side reading and is exercised by the Phase 4
differential harness. It is a real reduction — a four-line syntactic
correspondence instead of a memory-model argument — but it is a residual
assumption and the matrix marks it `✔*`.

---

## Scope gaps

### S-1 — allocation failure paths.

`insert_extent` 796–799 and `sort_idmaps` 866–869 can return `-ENOMEM`, and
`map_write`'s `out:` path (1108–1115) frees both arrays and resets
`map->nr_extents = 0`. The fixed-array model has no allocation, so these paths
do not exist in it. This is a real gap: the `out:` cleanup after a partial
write is exactly the shape where a use-after-free would live, and nothing here
covers it.

### S-2 — the `__user` boundary.

`memdup_user_nul` (952) and the `*ppos` handling (947) are not modelled.

### S-3 — the line parser's functional correctness.

Extracted and fuzzed in Phase 4, but only total-safety is proved, not
correctness. Its measured behaviour is `SPEC.md` §6; note that behaviour
**differs between the host 6.8 kernel and the v7.2 target tree** (commit
`6e30111dbb40`), which is why the harness must compile the target tree's
`lib/kstrtox.c`.

### S-4 — `gid_map` and `projid_map` admission.

The algebra is shared, the admission policy is not. `SPEC.md` §4.6 states the
uid path (`cap_setid == CAP_SETUID`) in full;
`ADMIT-SETGROUPS-COUPLING` names the gid difference but the projid path
(`proc_projid_map_write` 1154, where `cap_valid(cap_setid)` is false and the
map is admitted unconditionally at 1200) is not covered.

### S-5 — `WF-REVERSE-LIVE`: the `[NEEDS EMPIRICAL CHECK]` is discharged for the sequential claim

`map_id_range_up_max` (372) binary-searches `map->reverse`. The clause says: a
published map with `nr_extents > 5` has `reverse != NULL`. When first written
this was a three-function reading and carried the mark. It has since been
checked the mechanical way — by enumerating **every** writer of `->reverse` in
the tree (`grep` over `kernel/ fs/ include/`, `*.c *.h`), then reading each
site in isolation:

| Writer | What it does | Publishes a `>5` map with `reverse == NULL`? |
|---|---|---|
| `kernel/user_namespace.c` 809, `insert_extent` | `map->reverse = NULL` at migration | **No** — writes the local `new_map`, which `map_write` never publishes before 1089/1098 |
| `kernel/user_namespace.c` 866, `sort_idmaps` | `map->reverse = kmemdup_array(...)`; `-ENOMEM` at 868–869 if it fails | No — on failure `map_write` goes to `out:` |
| `kernel/user_namespace.c` 1098–1099, `map_write` install | `map->forward = ..., map->reverse = ...` | **No** — reached only after `sort_idmaps` returned 0 at 1089–1091 |
| `kernel/user_namespace.c` 1110–1112, `map_write` `out:` | `forward = NULL; reverse = NULL; nr_extents = 0` | No — `nr_extents` is reset to 0 in the same block |
| `fs/mnt_idmapping.c` 268–270, `copy_mnt_idmap` | see below | **No** |

`copy_mnt_idmap` (219–272) deserves the detail, since it is the second producer
of `>5` maps (via `alloc_mnt_idmap` 287, at 298–300, for idmapped mounts). For
`nr_extents > 5` (the `≤ 5` case is a whole-struct copy at 244–247) it
`kmemdup_array`s **both** arrays — `forward` at 249–251, `reverse` at 255–257
— fails with `-ENOMEM` if either allocation fails (252–253; 258–261, freeing
`forward`), and only then stores `forward` (268), `reverse` (269) and
`nr_extents` (270), in that order. So a copied map with `nr_extents > 5`
always has `reverse` populated. Two caveats, stated rather than glossed:

- it **preserves** the clause from its source rather than establishing it:
  `kmemdup_array(map_from->reverse, ...)` at 255 would dereference NULL if the
  *source* had `reverse == NULL`, so it relies on the source (a published
  userns map) already satisfying `WF-REVERSE-LIVE`;
- the ordering at 268–270 is a sequential fact; whether a *concurrent* reader
  can observe `nr_extents` before `reverse` is `A-PUB` — and the comment at
  263–267 argues the map is not yet exposed, which is again a claim this model
  cannot check.

**Disposition.** The sequential claim — no writer publishes a `>5` map with
`reverse == NULL` — is established by exhaustive enumeration and the mark is
dropped for it. The concurrent-visibility residue folds into `A-PUB`. Model T
carries `reverse_live`; F5 `PRESERVE` (step 4) is where `nr_extents > 5 ->
reverse_live` is proved for `map_write`'s output. **Not a finding candidate;
step 3 proceeds.**

---

## Named lemmas with `sorry`

Authoritative list: the seven declarations `verify/lean/axioms-step4.txt` shows
with `sorryAx`. Two are step-5 gaps, two are F5 gaps, three inherit. Nothing on
this list is called proved anywhere in the repository.

### L-1 — `bsearch_complete` (Algebra.lean). **Step-5 gap; the core of F4.**

Statement: for a prefix of the 340-slot array that is sorted by the key
(`first` downward, `lower_first` upward), pairwise `count ≥ 1 ∧ nowrap`, and
contains an extent covering the single id, the monomorphized
`__inline_bsearch` returns `some _`.

Missing: the monotonicity of `cmp_map_id` along a sorted, disjoint array
(SPEC §4.4 obligation 1) and the search-window invariant "if a hit exists it
lies in `[lo, lo+num)`", re-established across both branches including the
`num--; num >>= 1` one (obligation 2). Soundness of the same loop is proved
(`bsearch_loop_sound`); completeness is exactly what sortedness buys, and it is
where a real defect would live. It is the first thing step 5 proves.

### L-2 — `roundtrip_complete` (Algebra.lean). **Inherits L-1.**

Only the `> 5` branch is open; below 6 extents it is proved
(`roundtrip_complete_le5`). It reduces to L-1 on the `reverse` arm.

### L-3 — `sort_idmaps_fun` (WritePath.lean). **F5 gap; no kernel content.**

Statement: `sort_idmaps` returns `0`, leaves `nr_extents` and `extent` alone,
permutes the heap arm's abstract list in place, and above 5 extents sets
`reverse_live` and fills `reverse` with a permutation of `forward`.

Missing: a permutation proof for the insertion sort that stands in for
`lib/sort.c` under `A-SORT`. Two nested Aeneas loops (`sort_sink_loop`,
`sort_extents_loop`) plus the copy loop. The statement deliberately asks for
**permutation only**; sortedness (`SortedArms`) is a separate obligation for
step 5, consumed by L-1.

### L-4 — `remap_install_fun` (WritePath.lean). **F5 gap; the loop-level PRESERVE-LOWER.**

Statement: from an accumulated `new_map` whose abstract list is `PreRemap` and
duplicate-free, `map_write_body_loop0_loop0` (the re-map loop at 1063–1083
plus `sort_idmaps` and the install at 1089–1102) either returns a negative code
or installs a `WellFormed` map.

Missing: the loop invariant over the union-dispatched write-back at 1082 —
"positions `< idx` carry the re-mapped `lower_first`, positions `≥ idx` the
original" — expressed through `Remapped`; then, at exhaustion, `disj_l` from
`preserve_lower_list` + `down_range_sound` (both **proved**), `rev_perm` from
L-3, `nowrap_l` for the re-mapped values from the parent's `nowrap_l`, and the
install memcpy loop (`map_write_body_loop0_loop0_loop0`, the same shape as
`insert_extent_loop_fun`). The mathematics of PRESERVE-LOWER is closed; this is
plumbing, but it is the plumbing that turns the mathematics into a statement
about the C's loop.

### Inheriting: `lines_loop_fun`, `write_preserves_wf`, `reachable_wf`

Each has a complete proof of its own and carries `sorryAx` only through L-4
(and L-3 via L-4). When L-3 and L-4 close, F5 closes with no further work.

### What was closed in step 4 that had been listed

`down_range_sound` (range soundness, both paths) — proved and moved out of this
list. `insert_extent_fun`, `mappings_overlap_fun`, `preserve_lower_list`,
`lines_loop_fun`'s own proof — never listed, proved directly.

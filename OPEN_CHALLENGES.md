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

### A-UNION — **eliminated, pending step 3.**

Under Model T this is theorem S5 `NO-STALE-READ` rather than an assumption.
Model T translated cleanly (`UidGidMap` with both arms plus the clobber write
in `insert_extent`), so the fallback to Model F was not needed. S5 is not yet
proved; until it is, this line is a promise, not a result.

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

### S-5 — `WF-REVERSE-LIVE`, a clause writing the model surfaced.

`map_id_range_up_max` (372) binary-searches `map->reverse`, which
`insert_extent` sets to `NULL` at migration (807) and only `sort_idmaps`
populates (866). So an upward lookup on a map with `nr_extents > 5` and
`reverse == NULL` would dereference NULL in the C. It is unreachable because
`map_write` installs at 1098–1099 only after `sort_idmaps` succeeded at 1089,
and the error path at 1108–1112 resets `nr_extents` to 0 — but that is a
three-function argument about the C's reachable states, so per the calibration
rule it is **[NEEDS EMPIRICAL CHECK]** and it is added to `SPEC.md`'s
`WellFormed` as `WF-REVERSE-LIVE` rather than assumed. Model T represents it as
the `reverse_live` flag; nothing yet proves the flag is true whenever
`nr_extents > 5`.

---

## Named lemmas with `sorry`

None yet — step 2 (extraction round trip) is where this phase currently stands
and no Lean proofs have been attempted. This section is populated from step 3
onward, one row per `sorry`, with what is missing and why.

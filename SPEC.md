# Phase 2 — Specification: user-namespace ID mapping

**Target:** the ID-mapping algebra and admission policy of
`kernel/user_namespace.c`, plus the shared `struct uid_gid_map` machinery it
exposes to `fs/mnt_idmapping.c`.
**Reference tree:** `~/linux-full` at `v7.2-rc7-687-ge172eee25cfe`. Every line
citation is against that commit.
**Status:** specification only. No Rust written, no proof attempted, no theorem
proved. Statements below are *goals*, and are marked with the assumptions they
will rest on.

Notation: `2^32` is written `W`. `u32` arithmetic is mod `W` unless stated.
`⊥` denotes the failure sentinel `(u32)-1 = W - 1`.

---

## 1. Data model

### 1.1 The abstract map

An **extent** is a triple over `u32`:

```
Extent := { first : u32, lower_first : u32, count : u32 }
```

An extent denotes the affine partial function on `u32`

```
⟦e⟧ : u32 ⇀ u32
⟦e⟧(x) = (x - e.first) + e.lower_first   if e.first ≤ x < e.first + e.count
         undefined                       otherwise
```

with the *upper interval* `U(e) = [e.first, e.first + e.count)` as its domain
and the *lower interval* `L(e) = [e.lower_first, e.lower_first + e.count)` as
its image. Both are intervals over the integers, **not** over `u32` — §1.3
(NOWRAP) is what makes that identification legitimate.

An **abstract map** is a finite sequence of extents:

```
Map := List Extent          -- order matters: it is the C array order
```

The two directions the kernel computes:

```
down⟦m⟧(x) = ⟦e⟧(x)    for the unique e ∈ m with x ∈ U(e);  ⊥ if none
up⟦m⟧(y)   = ⟦e⟧⁻¹(y)  for the unique e ∈ m with y ∈ L(e);  ⊥ if none
```

"the unique" is a claim, discharged by `WF-DISJ-UPPER` / `WF-DISJ-LOWER` below.
Range forms take a count and require the *whole* range to land in one extent —
this is `cmp_map_id`'s `id2 = key->id + key->count - 1` (255) plus the
four-way containment test at 267–268:

```
downR⟦m⟧(x, n) = ⟦e⟧(x)  for the unique e with [x, x+n) ⊆ U(e);  ⊥ if none
upR⟦m⟧(y, n)   = ⟦e⟧⁻¹(y) for the unique e with [y, y+n) ⊆ L(e); ⊥ if none
```

`map_id_down` (338) is `downR(·, 1)`; `map_id_up` (404) is `upR(·, 1)`.

### 1.2 Well-formedness

`WellFormed : Map → Prop` is the conjunction of the following. Each clause is
tagged with the C line that establishes it, so the predicate is auditable
against the write path rather than invented.

| Tag | Statement | Established at |
|---|---|---|
| `WF-LEN` | `1 ≤ |m| ≤ 340` | lower: `map_write` 1053 (`nr_extents == 0` -> reject); upper: 1041 + `insert_extent` 789 |
| `WF-COUNT` | `∀ e ∈ m. e.count ≥ 1` | implied by `WF-NOWRAP` |
| `WF-NOWRAP-U` | `∀ e ∈ m. e.first + e.count ≤ W - 1` | `map_write` 1031 — see §1.2.1 for why the bound is `W-1`, not `W` |
| `WF-NOWRAP-L` | `∀ e ∈ m. e.lower_first + e.count ≤ W - 1` | `map_write` 1033 |
| `WF-NOSENT` | `∀ e ∈ m. e.first ≠ ⊥ ∧ e.lower_first ≠ ⊥` | `map_write` 1024 (redundant given `WF-NOWRAP`; see §1.2.1) |
| `WF-NOSENT-IV` | `∀ e ∈ m. ⊥ ∉ U(e) ∧ ⊥ ∉ L(e)` | **corollary** of `WF-NOWRAP-U/L`, not a separate check |
| `WF-DISJ-UPPER` | `∀ i ≠ j. U(mᵢ) ∩ U(mⱼ) = ∅` | `mappings_overlap` 771–774, called at 1038 |
| `WF-DISJ-LOWER` | `∀ i ≠ j. L(mᵢ) ∩ L(mⱼ) = ∅` | `mappings_overlap` 776–779 at 1038 — **but see §1.5: only for pre-remapping values** |

### 1.2.1 The no-wrap check is one bit stronger than it looks, and that settles the sentinel

`map_write` 1031 reads, in `u32` arithmetic:

```c
if ((extent.first + extent.count) <= extent.first)
        goto out;
```

Working out what this accepts, rather than assuming it means "no wrap":

- `first + count < W` (no wrap): the sum exceeds `first` iff `count ≥ 1`.
- `first + count = W`: the sum is `0`, and `0 ≤ first` — rejected. (`first = 0`
  cannot reach this case, since `count ≤ W-1`.)
- `first + count > W`: the sum is `first + count - W ≤ first` — rejected.

So the check accepts **exactly** `count ≥ 1 ∧ first + count ≤ W - 1`.
Brute-forced over the boundary values plus 200 000 random `(first, count)`
pairs: the characterisation holds with no exceptions. Three consequences:

1. **`WF-NOWRAP` is `≤ W - 1`, not `≤ W`.** I had it as `≤ W`, which is the
   weaker "no wrap" reading. The real bound is one tighter.
2. **`⊥` is structurally excluded from every interval** (`WF-NOSENT-IV`).
   Since `U(e) = [first, first+count)` and `first + count ≤ W - 1 = ⊥`, the
   sentinel is never *in* `U(e)`; the same for `L(e)` via 1033. Verified by
   brute force over 200 000 accepted extents. **This eliminates the sentinel
   ambiguity entirely for any map installed through `map_write`** — see §4.3,
   where it was previously flagged as an open question.
3. **1024 is redundant given 1031** for `first`: `first = ⊥` with `count ≥ 1`
   forces `first + count ≥ W`, which 1031 rejects. Same for `lower_first` via
   1033. 1024 runs first and is defense-in-depth, not the load-bearing check.
   Worth stating because a reader (or a future patch) might otherwise take 1024
   to be what excludes the sentinel; it is not.

`WF-COUNT` also comes out of this same comparison rather than a separate check:
`count = 0` makes the sum equal `first`, so the `<=` fires. The kernel's comment
at 1028–1030 claims both facts for the one comparison, and it is right.

### 1.2.2 The four sources of a `uid_gid_map`, and which the spec covers

`WellFormed` is established by `map_write`, but that is not the only way a
`uid_gid_map` comes to exist. Enumerated, because a property proved about
`map_write`'s output covers a map only if `map_write` produced it:

| Source | Map value | Covered? |
|---|---|---|
| `map_write` (980–1102), via `proc_{uid,gid,projid}_map_write` 1120/1137/1154 | validated, `WellFormed` | **yes** — this is the spec's subject |
| `init_user_ns` (`kernel/user.c` 37–68) | static `(first=0, lower_first=0, count=4294967295)`, `nr_extents=1` | **yes**, and it satisfies `WellFormed`: `0 + (W-1) = W-1 ≤ W-1`. Note `count` is `W-1`, **not** `W`, so the identity map deliberately does not map `⊥`. |
| `copy_mnt_idmap` (219), via `alloc_mnt_idmap` (287, 298–300) | a copy of a `map_write`-installed userns map | **yes**, inherited — `alloc_mnt_idmap` copies `mnt_userns->{uid,gid}_map`, which came from `map_write` |
| `nop_mnt_idmap` / `invalid_mnt_idmap` (`fs/mnt_idmapping.c` 31, 40) | `nr_extents = 0`; both are `kzalloc`-shaped statics with only `.count` set | **no, and they never reach the algebra**: `make_vfsuid` short-circuits on pointer identity at 86–89 before touching `uid_map`, returning the kuid unchanged or `INVALID_VFSUID`. The `initial_idmapping(fs_userns)` test at 90 likewise bypasses `from_kuid`. |

The last row matters for the model's entry conditions: the algebra is only ever
called on a map with `nr_extents ≥ 1`, because the two `nr_extents = 0` statics
are filtered by pointer comparison upstream. That is an entry-condition
*hypothesis* of F1, not something the algebra itself enforces —
`map_id_range_down` on an empty map would simply return `⊥`, which is safe but
would be the wrong answer for `nop_mnt_idmap` (identity), and the reason it is
never asked.

### 1.3 The concrete representation

The C is a union (`include/linux/user_namespace.h` 25–35): the first 16 bytes
of `extent[5]` alias `forward`/`reverse`, while `nr_extents` sits at offset 60,
outside the aliased region. Two candidate Rust models:

**Model F (flat).** `{ extents: [Extent; 340], nr_extents: u32 }`. The abstract
map is `extents[0 .. nr_extents]`. Simple, certainly translatable, and
*conditionally* faithful — the condition being `A-UNION` (§3).

**Model T (two-armed).** Mirror the union:
`{ base: [Extent; 5], heap: [Extent; 340], reverse: Option<[Extent; 340]>, nr_extents: u32 }`,
with `insert_extent`'s migration modelled including the clobber of `base[0]`
and `base[1].first`, and every read dispatching on `nr_extents <= 5` exactly as
the four C readers do (`map_id_range_down_base` 300, `map_id_range_up_base`
349, `mappings_overlap` 761–764, `verify_root_map` 899–902).

**Recommendation: Model T, falling back to Model F.** Under Model T the union
side condition stops being an assumption and becomes a *theorem*
(`NO-STALE-READ`, §4.6): no read ever observes a clobbered slot. That converts
the single largest faithfulness risk in the target into a proof obligation,
which is the whole point of the exercise. The cost is more Rust and a real
chance Aeneas rejects it — `insert_extent`'s migration is a memcpy-then-alias
pattern, and the clobber is the construct that #1199 is about. Phase 3 attempts
Model T **first**, as a bounded experiment, and falls back to Model F with
`A-UNION` as an explicit hypothesis if Aeneas refuses. Which way it went will
be reported in `VERIFY-REPORT.md`; the fallback is not silent.

### 1.4 Two lookup paths

The abstract `down`/`up` are implemented twice:

- `|m| ≤ 5`: linear scan over unsorted extents — `map_id_range_down_base`
  (300), `map_id_range_up_base` (349).
- `|m| > 5`: binary search over `forward` (sorted by `first`) and `reverse`
  (sorted by `lower_first`) — `map_id_range_down_max` (282),
  `map_id_range_up_max` (372), through `bsearch` with `cmp_map_id` (251).

Their agreement is §4.4, the theorem where a real defect would live.

### 1.5 Sortedness, and the one place the model must be careful

`sort_idmaps` (856) runs at `map_write` **1089**, *after* the re-mapping loop
(1063–1083) has overwritten every `lower_first` at **1082** with a
kernel-global id from `map_id_range_down(parent_map, ...)` (1072).
`mappings_overlap` ran at **1038**, before that. Therefore:

- `cmp_extents_forward` (823) sorts by `first`, which is never rewritten.
  Distinctness of `first` follows directly from `WF-DISJ-UPPER`. **Premise.**
- `cmp_extents_reverse` (838) sorts by the post-remapping `lower_first`.
  `WF-DISJ-LOWER` as established at 1038 is about the *pre*-remapping values
  and says nothing about these. Distinctness here is exactly
  `PRESERVE-LOWER` (§4.5), which needs the parent map's injectivity.
  **Theorem, not premise.**

So the sort contract is stated as: the result is a permutation of the input,
sorted by the key. Uniqueness of that result — needed for "any correct sort
agrees with `lib/sort.c`'s heapsort" — is `SORT-UNIQUE-FWD` (free) and
`SORT-UNIQUE-REV` (a corollary of `PRESERVE-LOWER`).

---

## 2. Safety properties vs functional correctness

Labelled separately, as requested. **Safety** = the reimplementation cannot
misbehave regardless of input (no panic, no UB, no nontermination, no
out-of-bounds). **Functional correctness** = the reimplementation computes what
the C computes, and the C computes what the isolation model requires.

| # | Property | Class |
|---|---|---|
| S1 | `TOTAL-SAFETY` — every entry point is `ok` / controlled `fail` / `div`, never a fourth outcome | safety |
| S2 | `NO-PANIC` — on a `WellFormed` map, every lookup returns `ok`; no index or arithmetic panic | safety |
| S3 | `TERMINATION` — the linear scan, the binary search, the overlap loop and the sort all terminate | safety |
| S4 | `NO-OVERFLOW` — no `u32` operation in `first + count` or `id + count` overflows on a `WellFormed` map | safety |
| S5 | `NO-STALE-READ` — (Model T only) no read observes a slot clobbered by `insert_extent`'s migration | safety |
| F1 | `DOWN-FUNCTIONAL` / `UP-FUNCTIONAL` — the C's lookups implement `down`/`up` | functional |
| F2 | `INJECTIVITY` — `down` is injective on a `WellFormed` map | functional |
| F3 | `ROUNDTRIP` — `up ∘ down` is the identity or `⊥`, never an unrelated id | functional |
| F4 | `AGREEMENT` — the `≤5` scan and the `>5` binary search compute the same function | functional |
| F5 | `PRESERVE` — the validated write path takes a `WellFormed` parent to a `WellFormed` child | functional |
| F6 | `ADMISSION` — the admission policy admits exactly the maps it is documented to admit | functional |

S4 is listed as safety because in the Rust reimplementation an overflow *is* a
panic; the same statement about the C is functional correctness, since the C
wraps silently. The two are proved once and read twice.

---

## 3. Named assumptions

These appear **as explicit hypotheses in the theorem statements**, not only
here and not only in `OPEN_CHALLENGES.md`. §5 maps every property to the
assumptions it consumes.

| Tag | Statement | Discharged how |
|---|---|---|
| `A-PUB` | The map under consideration is one that some completed `map_write` installed, and is not concurrently mutated. | **Not discharged.** Requires a memory model; see §7. Consumed by every property. |
| `A-UNION` | (Model F only) No read observes `extent[]` after `forward` is set. | By inspection of the four readers. Under Model T this becomes theorem S5 instead. |
| `A-SORT` | `sort_idmaps`' sort returns a permutation of its input, sorted by the comparison key. | Contract of `lib/sort.c`; tested by the differential harness, not proved. |
| `A-BSEARCH` | The monomorphized binary search is semantics-equivalent to `bsearch` + the indirect `cmp_map_id` call. | Argued (unique static callback target) + tested by the harness. |
| `A-CAPORACLE` | `ns_capable`, `file_ns_capable`, `cap_raised` and the `cred`/`ns` fields they read behave as an opaque oracle whose answers are inputs. | By construction: they are parameters of the model. Only F6 consumes it. |
| `A-PARENT-WF` | The parent namespace's map is already `WellFormed` when the child's is written. | Induction on namespace depth; base case `init_user_ns`, whose map is the near-identity extent `(0, 0, W-1)` (§1.2.2, §7.10) — `W-1`, not `W`. |

A note on how `A-PUB` and `A-UNION` will appear in Lean, because "state it as a
hypothesis" has a limit worth being honest about. `A-PARENT-WF` and `A-SORT`
are *usable* hypotheses — the proofs consume them. `A-PUB` and `A-UNION` are
claims about the C, and Lean has no C to quantify over; carrying them as
`opaque` propositional arguments makes them visible in every theorem statement
(which is the requirement) but they will be **unused** in the proof terms, and
an unused hypothesis is a documentation device, not a logical one. Two
consequences I will not paper over: such a hypothesis does **not** show up in
`#print axioms`, so the axiom audit cannot be the place a reader discovers it;
and `A-UNION` disappears entirely if Model T succeeds. `VERIFY-REPORT.md` will
carry a table of theorem × assumption alongside the axiom audit, because the
axiom audit alone would understate what the theorems rest on.

---

## 4. The properties

### 4.1 `NO-OVERFLOW` (S4) — arithmetic

```lean
theorem no_overflow_upper (m : Map) (hpub : A_PUB m) (hwf : WellFormed m)
    (e : Extent) (he : e ∈ m) :
    (e.first.toNat + e.count.toNat) ≤ 2^32 - 1
```
and the same for `lower_first`. Plus, for the range forms, the fact
`cmp_map_id` depends on at 255:

```lean
theorem no_overflow_range (m : Map) (x n : U32)
    (hwf : WellFormed m) (hhit : ∃ e ∈ m, [x, x+n) ⊆ U(e)) :
    x.toNat + n.toNat ≤ 2^32 - 1
```

*Rests on:* `A-PUB`, `WF-NOWRAP-U/L`.

*Counterexample means:* `first + count` wrapping makes `U(e)` an interval that
"wraps past zero", so the containment test `id >= first && id <= last` with
`last < first` is false for every id — the extent silently maps nothing — or,
worse, for `cmp_map_id`'s `id2 = id + count - 1` computed on a caller-supplied
range, a wrapped `id2` makes the three-way comparison non-monotone and the
binary search unsound. **Operationally for a sandbox:** a mount idmap installed
via `mount_setattr` whose extent covers the top of the id space could look
empty (files appear unowned, `chown` fails oddly) or, through the range form,
resolve to an extent that does not contain the range — a file appearing to
belong to the wrong host uid. Note the *caller-supplied* range in
`fs/mnt_idmapping.c` 373 (`statmount_mnt_idmap`) comes from an extent that was
itself validated, so the reachable exposure is narrower than the function
signature suggests; that narrowing is part of what F1 must show.

### 4.2 `INJECTIVITY` (F2)

```lean
theorem down_injective (m : Map) (hpub : A_PUB m) (hwf : WellFormed m)
    (x y : U32) (hx : down m x ≠ sentinel) (hxy : down m x = down m y) :
    x = y
```

*Rests on:* `A-PUB`, `WF-DISJ-LOWER`, `WF-NOWRAP-L`, and — because
`WF-DISJ-LOWER` for an *installed* map is itself the conclusion of `PRESERVE`
(§4.5) — `A-PARENT-WF`. This is the induction whose necessity §1.5 established:
injectivity of the child's map is proved from injectivity of the parent's, with
`init_user_ns` as the base case.

*Why disjointness of the lower intervals and not just distinctness of
`lower_first`:* two extents `(0, 100, 10)` and `(50, 105, 10)` have distinct
`lower_first` but overlapping images, so namespace ids 5 and 50 both map to
global 105. `WF-DISJ-LOWER` is the right strength.

*Counterexample means:* two distinct in-container uids resolve to one host uid.
**Operationally:** the container's uid 1000 and uid 2000 are the same host
principal. Files written by one are owned by the other; `setuid` between them
inside the container is a no-op on the host side, so a privilege boundary the
workload's own design relies on (say, a supervisor uid and an untrusted worker
uid inside the sandbox) silently does not exist. This is the single most
consequential property in the target and the one a reviewer should test hardest.

### 4.3 `ROUNDTRIP` (F3)

The property you asked for, stated in the form the code actually supports:

```lean
theorem roundtrip (targ : Map) (hpub : A_PUB targ) (hwf : WellFormed targ)
    (x : U32) :
    let k := down targ x
    k = sentinel ∨ up targ k = x
```

i.e. `up (down x)` is either `x` or the lookup failed; it is **never a third,
unrelated id**. The stronger-looking `from_kuid (make_kuid ns u) = u ∨ = ⊥`
does not hold as stated across *different* namespaces — `make_kuid` uses
`ns->uid_map` (425) and `from_kuid` uses `targ->uid_map` (444), and for
`ns ≠ targ` there is no round-trip to speak of. The theorem is about one map.

**`SENTINEL-COLLISION` — raised, then resolved, and the resolution simplifies
the theorem.** The concern was: if `⊥ ∈ L(e)` for some extent, then
`down x = ⊥` is ambiguous between "lookup failed" and "succeeded, mapping to
`W-1`", and the disjunction in `ROUNDTRIP` would be hiding a real defect rather
than describing normal behaviour.

It cannot happen. §1.2.1 shows the no-wrap check at 1031/1033 accepts only
`first + count ≤ W - 1`, so `⊥ = W - 1` lies strictly above every accepted
interval — `WF-NOSENT-IV`. And `init_user_ns` (`kernel/user.c` 41–46) uses
`count = 4294967295 = W - 1`, not `W`, so the identity map deliberately stops
one short of the sentinel too. Across all four map sources in §1.2.2, no
reachable map has `⊥` in any `U(e)` or `L(e)`.

So `down x = ⊥` unambiguously means "no mapping", and the disjunction in
`ROUNDTRIP` is exactly the two cases it appears to be. `WF-NOSENT-IV` becomes a
lemma that the `ROUNDTRIP` proof discharges from `WF-NOWRAP` rather than an
open question.

**This item was marked [NEEDS EMPIRICAL CHECK] when first written, and the mark
earned its keep immediately.** Checking it turned up two things reading had
missed: that the no-wrap bound is `W-1` rather than `W`, and that
`init_user_ns.uid_map.extent[0].count` is `4294967295` rather than `2^32` — I
had written the initial map as `(0, 0, W)` in a first draft of §7, which is
wrong and would have made the initial namespace the one place the ambiguity was
unavoidable. The opposite is true: it is excluded everywhere, including there.

### 4.4 `AGREEMENT` (F4) — the theorem where a defect would live

```lean
theorem scan_bsearch_agree (m : Map) (hpub : A_PUB m) (hwf : WellFormed m)
    (hsort : A_SORT) (hbs : A_BSEARCH) (x n : U32) :
    down_base m x n = down_max (sortForward m) x n
  ∧ up_base   m x n = up_max   (sortReverse m) x n
```

Read carefully, this is three obligations:

1. **`cmp_map_id` is a valid search predicate.** For a fixed key `(x, n)`, the
   function `e ↦ cmp_map_id(key, e)` must be *monotone* along the sorted order:
   `-1` for extents above the key, `0` for the hit, `+1` for extents below.
   Inspecting 262–274: `first = el->first` for the down direction (265),
   `last = first + el->count - 1` (269), returns `0` iff both `id` and `id2`
   lie in `[first, last]` (271–272), `-1` if `id < first || id2 < first` (274),
   else `+1`. Monotonicity of this along `first`-sorted order needs
   `WF-DISJ-UPPER` and `WF-NOWRAP-U`; without disjointness the `0` region need
   not be contiguous and `bsearch` may miss a hit that a linear scan finds.
2. **`bsearch`'s loop is correct.** `__inline_bsearch`
   (`include/linux/bsearch.h` 9–28) is not textbook: on `result > 0` it does
   `base = pivot + size; num--;` and then `num >>= 1` unconditionally. The
   invariant "if a hit exists it lies in `[base, base+num)`" must be
   re-established across both branches; the `num--` before the shift is where
   an off-by-one would live.
3. **The reverse direction uses a different key field.** `cmp_map_id` selects
   `el->lower_first` when `key->map_up` is true (263–266) and `reverse` is
   sorted by `lower_first`, so the same monotonicity argument must be redone
   against `WF-DISJ-LOWER` — which, per §1.5, is the *post-remapping* property
   and therefore depends on `PRESERVE-LOWER`.

*Counterexample means:* a map with 6 or more extents resolves ids differently
from a map with 5. **Operationally:** this is the sharpest of all the
properties, because the two paths are exercised by *different deployments*.
Almost every hand-written container config uses one to three extents and stays
on the linear scan forever; large multi-tenant id allocations and
`/etc/subuid`-driven runtimes cross into the binary search. A defect here is
invisible in testing at small scale and appears only at the scale where a host
runs many tenants — the worst possible failure profile. If one theorem in this
spike is worth the effort, it is this one.

### 4.5 `PRESERVE` (F5) — the write path

```lean
theorem write_preserves_wf
    (parent : Map) (hppub : A_PUB parent) (hpwf : A_PARENT_WF parent)
    (lines : List (U32 × U32 × U32)) (oracle : CapOracle)
    (m : Map) (hok : map_write parent lines oracle = ok m) :
    WellFormed m
```

Decomposed by clause. `PRESERVE-UPPER` (`WF-DISJ-UPPER`, `WF-NOWRAP-U`,
`WF-NOSENT`, `WF-LEN`) is local: those fields are never rewritten, so the
checks at 1024/1031/1038/1041 establish them directly and `insert_extent` (789)
preserves them.

**`PRESERVE-LOWER` is the hard one, and it is the obligation §1.5 uncovered.**
After the loop at 1063–1083 replaces each `lower_first` with
`downR⟦parent⟧(lower_first, count)` (1072), we must show

```
∀ i ≠ j.  L(m'ᵢ) ∩ L(m'ⱼ) = ∅
```

given only that the *pre*-remapping lower intervals were disjoint. The argument:
`downR⟦parent⟧(y, n) ≠ ⊥` means `[y, y+n)` lies wholly inside a single parent
extent `p` (the four-way test at 267–268), on which `⟦p⟧` is a translation and
hence injective; distinct pre-images that shared a parent extent stay disjoint
by translation, and pre-images in *different* parent extents stay disjoint by
`parent`'s own `WF-DISJ-LOWER`. So `PRESERVE-LOWER` reduces to the parent's
disjointness — `A-PARENT-WF` — and the induction of §4.2 closes.

Corollaries: `SORT-UNIQUE-REV` (distinct post-remapping `lower_first`, hence a
unique reverse sort order, hence `A-SORT`'s abstraction is a non-weakening) and
the `WF-DISJ-LOWER` conjunct that `INJECTIVITY` and the reverse half of
`AGREEMENT` consume.

*Counterexample means:* a child map that passed every check in `map_write` is
nonetheless non-injective, because two of its extents were re-mapped into
overlapping global ranges. **Operationally:** the same collapse as §4.2, but
reached through a map the kernel explicitly accepted — so no amount of
userspace-side validation by the container runtime would catch it.

### 4.6 The admission policy (F6) — `new_idmap_permitted` and `verify_root_map`

Added per ROADMAP Amendment 3. Parameterized over `A-CAPORACLE`; the theorem
says what the policy *is*, which is the reviewable content.

```lean
theorem admission_characterisation
    (ns parent : Map) (o : CapOracle) (capSetid : CapId) (m : Map) :
    new_idmap_permitted o capSetid ns m = true ↔ Admissible o capSetid ns m
```

where `Admissible` is the disjunction the code implements, read off 1178–1211:

- **(root guard, 1178)** if `capSetid = CAP_SETUID` then `verify_root_map` must
  hold. `verify_root_map` (890) scans for an extent with `lower_first = 0`
  (898–907); if there is none it permits (909–910); otherwise it requires
  `file_ns->parent_could_setfcap` when `map_ns = file_ns` (918), else
  `file_ns_capable(file, map_ns->parent, CAP_SETFCAP)` (925).
- **(unprivileged self-map, 1184–1197)** `|m| = 1 ∧ m₀.count = 1 ∧
  ns.owner = cred.euid`, and then for `CAP_SETUID`,
  `make_kuid(parent, m₀.lower_first) = cred.euid` (1188–1189); for
  `CAP_SETGID`, `make_kgid(parent, m₀.lower_first) = cred.egid` **and**
  `¬(ns.flags & USERNS_SETGROUPS_ALLOWED)` (1193–1194).
- **(projid, 1200)** `¬cap_valid(capSetid)` — unconditionally permitted.
- **(privileged, 1207–1208)** `ns_capable(parent, capSetid) ∧
  file_ns_capable(file, parent, capSetid)` — **both**, the caller and the
  opener of the map file.
- otherwise denied (1211).

Three statements worth having as separate named lemmas, because each is a
property a sandbox author reasons about:

| Lemma | Statement |
|---|---|
| `ADMIT-UNPRIV-SINGLETON` | Without any capability in the parent, the *only* admissible uid map is a single extent of count 1 whose parent id maps to the caller's own euid. (From 1184–1190 being the sole path that returns `true` when 1200 and 1207 both fail.) |
| `ADMIT-SETGROUPS-COUPLING` | The unprivileged *gid* path additionally requires `setgroups` to be already disabled in `ns` (1193). So the pair (`gid_map` written unprivileged, `setgroups` enabled) is unreachable — the invariant that stops a task from dropping a supplementary group to gain access under a negative-permission ACL. Cross-check against `userns_may_setgroups` (1292) and `proc_setgroups_write` (1225). |
| `ADMIT-ROOT-NEEDS-SETFCAP` | An admissible uid map containing an extent with `lower_first = 0` implies the writer held `CAP_SETFCAP` in the relevant namespace. This is the link to `INVENTORY.md` §2c: it is what stops a sandboxed process from planting an fscap whose rootid maps to host uid 0. |

**In-bounds side condition.** 1184–1186 index `new_map->extent[0]` with no
`nr_extents <= 5` dispatch. Under Model F this is in-bounds because
`nr_extents == 1` guards it; under Model T it is a read of `base[0]`, in-bounds
for the same reason. Either way it is an explicit hypothesis of the lemma, not
an incidental fact — precisely the sort of guarded raw index that a
representation change can silently invalidate.

*Counterexample means:* the kernel installs a map it should have refused.
**Operationally:** `ADMIT-UNPRIV-SINGLETON` failing is the classic
unprivileged-userns escalation — a task with no privilege maps a parent id it
does not own and acquires that host identity. `ADMIT-ROOT-NEEDS-SETFCAP`
failing is fscap forging. These are the two consequences that motivate a
sandbox's `sysctl kernel.unprivileged_userns_clone=0` posture; the theorems say
what is lost by relaxing it.

### 4.7 Safety properties S1–S3, S5

`TOTAL-SAFETY` (S1) and `NO-PANIC` (S2) follow the pattern established in
`~/kernel-c-to-rust-spike/verify/`: S1 by exhaustive case split on the Aeneas
`Result`, S2 from `WellFormed` plus S4. `TERMINATION` (S3) has four obligations
— the two `for (idx = 0; idx < extents; idx++)` scans and the overlap loop are
structural; `__inline_bsearch`'s `while (num > 0)` needs the measure `num`,
strictly decreasing because `num >>= 1` on `num ≥ 1` decreases and the
`num--` branch decreases first. `NO-STALE-READ` (S5) exists only under Model T
and is stated in §1.3.

---

## 5. Theorem × assumption matrix

Which theorems are conditional on which assumption, per item 3 of the brief.
This table, not the axiom audit, is the honest summary of what the results rest
on.

| Property | `A-PUB` | `A-UNION` (Model F only) | `A-SORT` | `A-BSEARCH` | `A-CAPORACLE` | `A-PARENT-WF` |
|---|:--:|:--:|:--:|:--:|:--:|:--:|
| S1 `TOTAL-SAFETY` | — | — | — | — | — | — |
| S2 `NO-PANIC` | ✔ | ✔ | — | — | — | — |
| S3 `TERMINATION` | — | — | — | — | — | — |
| S4 `NO-OVERFLOW` | ✔ | ✔ | — | — | — | — |
| S5 `NO-STALE-READ` | — | n/a (Model T) | — | — | — | — |
| F1 `DOWN/UP-FUNCTIONAL` | ✔ | ✔ | — | ✔ | — | — |
| F2 `INJECTIVITY` | ✔ | ✔ | — | — | — | ✔ |
| F3 `ROUNDTRIP` | ✔ | ✔ | — | — | — | ✔ |
| F4 `AGREEMENT` | ✔ | ✔ | ✔ | ✔ | — | ✔ |
| F5 `PRESERVE-UPPER` | ✔ | ✔ | — | — | — | — |
| F5 `PRESERVE-LOWER` | ✔ | ✔ | — | — | — | ✔ |
| F6 `ADMISSION` + 3 lemmas | ✔ | ✔ | — | — | ✔ | — |

S1 and S3 are unconditional: they are properties of the extracted Rust, true
whether or not the Rust faithfully models the C. Everything else is conditional,
and `A-PUB` is on all of it.

---

## 6. Measured parser behaviour (not a property, and not a finding)

Recorded here because `ROADMAP.md` Amendment 2 promised it, and because it is
the one behaviour in the target established by measurement rather than reading.

The five data points, from `uidmap-probe.sh` / `uidmap-probe.txt`, written to
`/proc/PID/uid_map` in a fresh unprivileged user namespace, host uid 1000:

| Input line | Installed | Host kernel measured on |
|---|---|---|
| `0 1000 1` | `0 1000 1` | 6.8.0-138-generic |
| `4294967296 1000 1` | `0 1000 1` | 6.8.0-138-generic |
| `4294967297 1000 1` | `1 1000 1` | 6.8.0-138-generic |
| `4294967301 1000 1` | `5 1000 1` | 6.8.0-138-generic |
| `99999999999999999999999 1000 1` | `4135583743 1000 1` | 6.8.0-138-generic |

`4135583743 = (10^23 - 1) mod 2^32`, exactly — a mod-`2^64` wrap signature.

**Two statements, labelled by kernel, because they differ:**

- **On 6.8.0-138-generic (measured).** The parser reduces every decimal literal
  mod `2^32`. The only rejected input is one landing exactly on `(u32)-1` after
  truncation.
- **On `~/linux-full` v7.2-rc7+687 (derived, not measured).** The parser is
  exact below `2^64` and saturates to `ULLONG_MAX` at or above it; the
  saturated value truncates to exactly `(u32)-1` and is rejected at 1024. So
  the fifth row would read **rejected**, not `4135583743`.

The difference is commit `6e30111dbb40` "lib: fix `_parse_integer_limit()` to
handle overflow" (Dmitry Antipov, 2026-05-19, `git describe --contains` ->
`v7.2-rc1~77^2~64`), which introduced the `2^60` guard at `lib/kstrtox.c` 83
and the saturation at 84–88. 6.8 predates it; the target tree contains it.

**Not a vulnerability, on either kernel.** The truncated values (0, 1, 5) are
legal ids and every downstream check — sentinel, no-wrap, overlap, parent
mappability, admission — still applies. What it is: a documented-nowhere
acceptance of malformed input, and a place where the same test suite gives
different answers on 6.8 and 7.2. It belongs in the differential harness's
corpus for that reason.

**Load-bearing consequence for Phase 4.** The differential harness must compile
the C against the *target tree's* `lib/kstrtox.c`, not the host's libc or a
hand-written `simple_strtoul`. A harness that got this wrong would "confirm"
the 6.8 behaviour and silently disagree with the tree the theorems are about —
the same class of mistake as the `-fno-strict-overflow` issue documented in
`~/kernel-c-to-rust-spike/fuzz/build.rs`.

---

## 7. What these theorems do NOT cover

First on the list, as instructed.

1. **Barrier discipline and concurrency — `A-PUB`.** The lock-free read
   protocol is `map_id_range_down`/`_up` reading `nr_extents`, then `smp_rmb()`
   (322, 388), then the extents; `map_write` writing extents, then `smp_wmb()`
   (1101), then `nr_extents` (1102); write-once enforced at 980;
   `copy_mnt_idmap` (219) repeating the pattern with `READ_ONCE` (222) and
   refusing `nr_extents == 0` (235). The invariant — *non-zero `nr_extents`
   implies fully-initialized extent storage* — is what makes the whole scheme
   safe, and **a sequential Aeneas model cannot express it.** Every functional
   property above is stated about an already-published, quiescent map. Anyone
   reading "user-namespace ID mapping verified" must not conclude the barrier
   discipline was checked. It was not, and this toolchain cannot check it; it
   needs a memory-model tool (a litmus/`herd`-style check of the four-access
   pattern, or a CBMC-with-weak-memory harness). `OPEN_CHALLENGES.md` will name
   it as a tool gap, not an effort gap.
2. **The union, if Model T fails.** Under Model F, `A-UNION` is discharged by
   inspection. Under Model T it is theorem S5. Which one shipped will be stated
   in `VERIFY-REPORT.md`.
3. **`lib/sort.c`'s heapsort.** Abstracted to `A-SORT`. The uniqueness lemmas
   make the abstraction non-weakening *given* the contract, but the contract
   itself is tested (differential harness) rather than proved.
4. **`bsearch`'s indirect call.** `A-BSEARCH`. The monomorphization is argued
   and tested, not proved.
5. **The capability oracle.** `A-CAPORACLE`. F6 says what the policy computes
   *given* the oracle's answers. It says nothing about whether `ns_capable`
   answers correctly — that is `cap_capable_helper`, candidate E, a separate
   target. So `ADMIT-UNPRIV-SINGLETON` is conditional on the capability layer
   being right.
6. **Allocation failure.** `insert_extent` 796 and `sort_idmaps` 866 can return
   `-ENOMEM`, and `map_write`'s `out:` path (1108–1115) frees and resets. The
   fixed-array model has no allocation and therefore no ENOMEM path; the error
   paths of the C are out of scope. This is a real gap — the `out:` cleanup
   resetting `map->nr_extents = 0` after a partial write is exactly the kind of
   code where a use-after-free would live.
7. **The `__user` boundary.** `memdup_user_nul` (952) and the `*ppos` handling
   (947) are not modelled.
8. **Everything above the map.** `make_kuid`'s callers, `capable_wrt_inode_uidgid`,
   the fscap composition in `security/commoncap.c` — all consume these results
   and none is verified here.
9. **The other two maps' policy differences.** The spec covers `uid_map` with
   `cap_setid = CAP_SETUID`. `gid_map` (`proc_gid_map_write` 1137) and
   `projid_map` (1154) share the algebra but differ in admission (§4.6); only
   the uid path's lemmas are stated in full.
10. **`init_user_ns`'s identity map — checked, and it is not what I assumed.**
    The base case of `A-PARENT-WF` is the initial namespace's map. I had
    written it as the identity extent `(0, 0, W)`. It is actually
    `(first=0, lower_first=0, count=4294967295)` with `nr_extents = 1`
    (`kernel/user.c` 41–46, and identically for `gid_map` 51–56 and
    `projid_map` 61–66) — `count = W - 1`, one short of the full range. So the
    initial namespace does **not** map `⊥`, which is what makes
    `WF-NOSENT-IV` hold there too (§4.3). This is no longer an assumption; it
    is read off the initializer. What remains out of scope is only that the
    initializer is the *sole* writer of `init_user_ns`'s maps — `map_write` 980
    rejects a second write, but that argument is about the running kernel, not
    about the model.

## 8. Calibration rule adopted for this spike

Amendment 2 of `ROADMAP.md` records a three-file chain of source reasoning that
read as convincing and was wrong about the tree it claimed to describe. The
rule adopted, and applied above:

> A property derived by reading across files, with neither a machine-checked
> proof nor a measurement, is marked **[NEEDS EMPIRICAL CHECK]** and is not
> presented as settled. A measurement is recorded with the kernel version it
> was taken on, always — the version label is what turns a contradiction into
> a resolved discrepancy.

Both items that carried that mark when this document was drafted have since
been settled, and settling them changed the specification:

| Item | Outcome |
|---|---|
| §4.3 — is `⊥ ∈ L(e)` reachable? | **No.** Brute-forcing the `u32` comparison at 1031 showed it accepts only `first + count ≤ W - 1`, one bit stronger than the "no wrap" reading. `WF-NOWRAP` was corrected from `≤ W` to `≤ W - 1`, `WF-NOSENT-IV` was added as a corollary, `SENTINEL-COLLISION` was closed, and the redundancy of the check at 1024 was noted. |
| §7 item 10 — `init_user_ns`'s initializer | **Not as assumed.** `count = 4294967295 = W - 1`, not `2^32`. My draft had the initial map as `(0, 0, W)`, which would have put `⊥` inside its interval and made the initial namespace the one unavoidable instance of the ambiguity. The opposite holds. |

Two out of two marked items were wrong on the reading and right to check. That
is a poor hit rate for source reasoning and a good one for the rule, and it is
the reason §1.2.2 (enumerating the four ways a `uid_gid_map` comes into
existence) exists at all — it was written after the `init_user_ns` correction
made it obvious that "the map the spec is about" needed pinning down.

No items currently carry the mark. Any new one added during Phase 3 goes in
`OPEN_CHALLENGES.md` as well as here.

Applying the rule honestly to the rest of this document: §1.5's re-derivation
of the `map_write` step ordering, §4.4's monotonicity analysis of `cmp_map_id`,
and §4.5's `PRESERVE-LOWER` argument are all multi-step source reasoning. They
are *not* marked, because each is a claim about control flow and arithmetic
within a single function that the Lean proof will have to discharge anyway — if
they are wrong, the proof fails, which is the check. The marked items are the
ones where a wrong reading would be silently absorbed into an assumption
instead.

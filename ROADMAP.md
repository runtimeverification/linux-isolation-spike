# Phase 1 — target selection for the verification spike

Scope of this document: score candidate targets, pick one, and say plainly what
the pick can and cannot deliver. Nothing here is a claim about verified code —
no Rust has been written yet. `INVENTORY.md` is the input; `SPEC.md` is the
next artifact.

## 1. Method

The five dimensions requested, scored 1–5 (5 = best for a spike), plus one I
added and justify below.

| Dim | Meaning | Weight |
|---|---|---|
| **Size** | LOC of C that must enter the verified leaf. Smaller is better. | 0.10 |
| **Purity** | Absence of locking, allocation, callbacks, `__user` access, atomics. | 0.15 |
| **Arithmetic** | Density of arithmetic and boundary conditions — i.e. how much a proof actually buys over code review. | 0.15 |
| **Consequence** | Damage if the code is wrong, *for a sandboxed-AI-agent threat model specifically*. | 0.25 |
| **Translatability** | Does it get through Charon 909ff09a → Aeneas c2015b86 today, without an unfaithful model? | 0.20 |
| **Marginal assurance** | Is this already machine-verified elsewhere? 5 = no prior formal work, 1 = solved. | 0.15 |

**Why the sixth dimension.** The five requested dimensions measure
*tractability* and *stakes*. They do not measure whether the resulting proof
adds anything the world does not already have. Without that column my own
rubric ranks a target that has published machine-checked results above one
that has none (see §3, candidate D), which would be the wrong call for a
team deciding where to spend verification effort. The column is weighted
below Consequence and Translatability deliberately: re-verifying something in
a new toolchain has real value, just less.

Consequence is scored against the stated threat model — *a sandbox confining
an AI agent* — not against "kernel bugs in general". That changes the ranking:
it raises anything on the identity/permission path that is active in every
sandbox, and lowers anything reachable only through a facility a competent
sandbox already removes.

## 2. Candidates and measurements

LOC figures are `grep`-measured spans in `~/linux-full` at
`v7.2-rc7-687-ge172eee25cfe`, function definition line to closing brace.

| Id | Candidate | Constituent functions (file:span, lines) |
|---|---|---|
| **A** | user-namespace ID-mapping algebra | `kernel/user_namespace.c`: `cmp_map_id` 251–275 (25), `map_id_range_down_max` 282–292 (11), `_down_base` 300–316 (17), `map_id_range_down` 318–336 (19), `map_id_range_up_base` 349–365 (17), `_up_max` 372–382 (11), `map_id_range_up` 384–402 (19), `mappings_overlap` 745–782 (38), `insert_extent` 789–820 (32), `sort_idmaps` 856–876 (21); `verify_root_map` 890–930 (41), `new_idmap_permitted` 1172–1212 (41); `include/linux/bsearch.h` `__inline_bsearch` 9–28 (20); the extent parse/validate loop inside `map_write` 992–1049 (58). **Verified core ≈ 312 LOC (incl. Amendment 3); extracted leaf ≈ 372 LOC.** |
| **B** | `seccomp_is_const_allow` + reference cBPF semantics | `kernel/seccomp.c` 770–845 (76) **plus** what the property needs: `bpf_convert_filter` `net/core/filter.c` 580–922 (343) and `___bpf_prog_run` `kernel/bpf/core.c` 1852–2397 (546). **≈ 965 LOC.** |
| **C** | the cBPF validator family | `kernel/seccomp.c` `seccomp_check_filter` 278–346 (69); `net/core/filter.c` `bpf_check_classic` 1075–1151 (77), `check_load_and_stores` 931–982 (52); `io_uring/bpf_filter.c` `io_uring_check_cbpf_filter` 174–244 (71). **≈ 269 LOC.** |
| **D** | eBPF tristate-number abstract domain | `kernel/bpf/tnum.c` 17–217, the operators through `tnum_in` (**201 LOC**). |
| **E** | namespace capability walk | `security/commoncap.c` `cap_capable_helper` 68–106 (**39 LOC**). |
| **F** | hierarchical pids charge | `kernel/cgroup/pids.c` `pids_try_charge` 166–198 (33), `pids_can_fork` 273– (**~60 LOC**). |
| **G** | mount-propagation umount | `fs/pnode.c` `gather_candidates`/`trim_ancestors`/`handle_locked`/`propagate_umount` 500–687 (**~188 LOC**). |

## 3. Scoring table

| Id | Candidate | Size | Purity | Arith | Conseq | Transl | Marginal | **Total** |
|---|---|:--:|:--:|:--:|:--:|:--:|:--:|:--:|
| **A** | **userns ID-mapping algebra + admission policy** | 4 | 4 | 5 | 5 | 4 | 5 | **4.55** |
| D | eBPF tnum abstract domain | 4 | 5 | 5 | 4 | 5 | 2 | 4.20 |
| C | cBPF validator family | 4 | 5 | 3 | 4 | 5 | 4 | 4.20 |
| B | `seccomp_is_const_allow` + cBPF semantics | 2 | 4 | 4 | 5 | 3 | 5 | 4.00 |
| E | `cap_capable_helper` | 5 | 3 | 2 | 5 | 2 | 5 | 3.65 |
| F | hierarchical pids charge | 5 | 1 | 3 | 3 | 1 | 5 | 2.80 |
| G | mount-propagation umount | 2 | 1 | 2 | 4 | 1 | 5 | 2.60 |

### Score justifications, per candidate

**A — userns ID-mapping algebra. Total 4.55.**
*Size 4*: 230 LOC in the verified core; small, not trivially small.
*Purity 4*: the read path takes no locks (`smp_rmb` is a barrier, not a lock);
allocation exists (`insert_extent` 789, `sort_idmaps` 856) but the code itself
caps the array at `UID_GID_MAP_MAX_EXTENTS` = 340
(`include/linux/user_namespace.h` 17), so a fixed-capacity array is a faithful
model and no allocator is needed. One point deducted for the `bsearch`
callback and the `struct uid_gid_map` union (both addressed in §5).
*Arithmetic 5*: `first + count - 1` and `id + count - 1` throughout, wrap
guards at `map_write` 1031/1033, the sentinel `(u32)-1` colliding with a
syntactically legal ID, the 5-vs-340 storage boundary, an exact-fit off-by-one
at the 340 cap (`map_write` 1041), and `__inline_bsearch`'s unusual
`num--; num >>= 1` narrowing. This is a target where a proof says something a
careful reviewer plausibly misses.
*Consequence 5*: `INVENTORY.md` §9 makes it the deepest node in the
dependency graph. It resolves task identity (`make_kuid`/`from_kuid`), it is
the engine of idmapped mounts (`fs/mnt_idmapping.c` 96/159), and it feeds the
file-capability rootid translation (`security/commoncap.c` 460–467, 594–602,
708–735). A wrong result is a sandboxed process holding a host identity it
was never granted.
*Translatability 4*: no raw pointers, no `dyn`, no inline asm, no function
pointers *after* the monomorphization in §5.1, no union in the Rust model.
One point deducted because two of the enabling steps (§5.1, §5.2) are
modelling decisions, not free wins.
*Marginal 5*: I found no published formal verification of this code. The two
adjacent spikes in this environment (`~/kernel-c-to-rust-spike`,
`~/c2lean`) do not touch it.

**D — eBPF tnum. Total 4.20. This is the candidate that nearly won.**
It scores *better* than A on the three mechanical dimensions: 201 lines of
pure `u64` bit arithmetic, one loop in the whole file (`tnum_mul` 137), no
allocation, no locking, no callbacks, no pointers — as close to a
Charon-friendly target as the kernel contains. Its property, soundness of the
abstract domain (`x ∈ a ∧ y ∈ b → x op y ∈ tnum_op(a,b)`), is self-contained:
the concrete semantics is just machine arithmetic, so unlike B it needs no
interpreter. It loses on two counts. *Consequence 4, not 5*: unsound tnums
give a kernel R/W primitive, but only to a task that can load a BPF program —
and a sandbox that lets a confined agent call `bpf(2)` has a much larger
problem than tnum precision. For this threat model the verifier is a surface
to remove, not a primitive to depend on. *Marginal 2*: there is a published
line of machine-checked work on exactly these operators (the tristate-number
verification work of Vishwanathan et al., CGO 2022, and the range-analysis
verification that followed, CAV 2023). I have not re-verified those results
from this environment and do not vouch for their exact coverage — but their
existence means a spike here re-derives a known result in a new toolchain
rather than producing assurance nobody has. That is a fine second project and
a poor first one.

**C — cBPF validator family. Total 4.20.** Best translatability of any
candidate: three near-identical `for`-loops over an instruction array with
in-place mutation, no allocation, no callbacks (`seccomp_check_filter` *is* the
callback that `bpf_prog_create_from_user` invokes). *Arith 3* and
*Conseq 4* because the property provable **in isolation** is weak — "accepts
exactly this opcode set, terminates, never panics" — and the property that
matters ("an accepted program cannot make the interpreter read out of bounds
or loop forever") requires the interpreter, which is candidate B's problem.
There is, however, one strong theorem here that needs no interpreter, and it
is new: `seccomp_check_filter` (`kernel/seccomp.c` 278) and
`io_uring_check_cbpf_filter` (`io_uring/bpf_filter.c` 174) are structural
clones that differ only in the context-struct bound at lines 290 and 188.
Proving *equivalence modulo that constant* tells a sandbox author that
io_uring's new filter layer inherits seccomp's long-audited allowlist rather
than a freshly written one — which is exactly the question someone deciding
whether to permit io_uring in a sandbox has to answer. I recommend this as the
**second** target (§7).

**B — `seccomp_is_const_allow` + cBPF semantics. Total 4.00.** The single
highest-value *property* in the list: `seccomp_is_const_allow` decides which
syscalls go into the allow-bitmap that causes `seccomp_run_filters` to skip
filter evaluation entirely (`kernel/seccomp.c` 417), so a false positive is a
permanent, silent seccomp bypass. The theorem is a simulation: whenever it
returns true, the real filter returns `SECCOMP_RET_ALLOW` for every
`seccomp_data` agreeing on `nr` and `arch`. It fails on cost and mechanics.
Stating "the real filter" requires the actual execution path — `sock_filter`
→ `bpf_convert_filter` (343 LOC, two-pass with pointer arithmetic into a
growing instruction buffer) → `___bpf_prog_run` (546 LOC, a computed-goto
dispatch table). Neither is plausibly faithful through Charon today, and
substituting a hand-written "reference cBPF interpreter" would be precisely
the unfaithful model the honesty constraints forbid, because the whole content
of the theorem is agreement with the *real* semantics. Revisit when B's
reference chain is tractable or when a separately-justified cBPF semantics
exists.

**E — `cap_capable_helper`. Total 3.65.** 39 lines, and the property is
lovely: authority flows only downward through the namespace tree, with
termination resting on the `ns->level` invariant rather than a syntactic
bound. But the data structure is a heap-allocated parent-linked tree traversed
by pointer (`security/commoncap.c` 102). Modelling it for Charon means an
arena/index representation, which is a representation change to the *subject
of the theorem*, not to its environment — it strains "keep the C control flow
recognizable" harder than the amendments A needs. Good third target, ideally
after A establishes how to talk about namespace trees.

**F — hierarchical pids charge. Total 2.80.** Ruled out on purity and
translatability: `pids_try_charge` (166) is `atomic64_add_return` in a loop up
the ancestor chain with rollback, and its interesting property *is* the
concurrent one. A sequential model would verify the uninteresting half.

**G — mount-propagation umount. Total 2.60.** `propagate_umount` (658) and its
helpers are intrusive-list surgery over a mount graph under
`mount_lock`/`namespace_sem`. High consequence, near-zero translatability.
This is a model-checking or separation-logic target, not a Charon/Aeneas one.

## 4. Verdict: agree with the stated prior, with two scope amendments

**I agree that user-namespace ID mapping is the strongest first target**, and
I did not reach that by accepting the prior. My own weighting initially put
`tnum.c` (D) ahead of it on the five requested dimensions, and it took an
explicitly-declared sixth dimension to overturn that — see §3, candidate D.
The deciding arguments are (i) it is the deepest node in the isolation
dependency graph, with two independent consumers, so a theorem about it is a
theorem about idmapped mounts and file capabilities too; (ii) the arithmetic
is dense enough that a proof beats review; (iii) nothing here appears to be
verified already; and (iv) with the two amendments below it goes through the
pipeline without an unfaithful model.

The named function list in the prior was:
`map_id_range_down`, `map_id_up`, `make_kuid`, `from_kuid`,
`insert_extent`/`sort_idmaps`, and the `uid_map` write path in `map_write`.
Two amendments.

### Amendment 1 — `sort_idmaps` enters as a *contract*; only the forward half of the uniqueness argument is a premise

`sort_idmaps` (856) calls `lib/sort.c`'s heapsort (357 LOC) with a comparison
callback and generic byte-wise swaps selected by element size and alignment.
That is not faithfully translatable and I am not going to pretend otherwise.
The Rust/Lean side gets a simple in-place sort whose *contract* is stated: the
result is a permutation of the input, sorted by the key — exactly what
`lib/sort.c` provides. The **C side of the differential harness links the real
`lib/sort.c`**, so the abstraction is tested, not merely argued.

For the abstraction to be a non-weakening, the sorted order must be *unique*,
which needs distinct keys. I previously asserted this for both comparison
functions. **Only the forward half survives; the reverse half is a theorem, and
for a reason I had not noticed.**

**Forward — a premise, and cheap.** `cmp_extents_forward` (823) compares only
`first`. `mappings_overlap` checks the upper ranges at **771–774**
(`prev_upper_first <= upper_last && prev_upper_last >= upper_first`) and is
called from `map_write` **1038** before each insert. Two extents sharing
`first` have intersecting upper ranges whenever both counts are `>= 1` — which
the no-wrap check at 1031 guarantees — so 1038 rejects them. Distinct `first`
follows directly from a check on the value being sorted. Premise.

**Reverse — a theorem, because the sort key is rewritten after the check.**
`mappings_overlap` *does* check the lower ranges too, at **776–779**
(`prev_lower_first <= lower_last && prev_lower_last >= lower_first`) — so my
claim that non-overlap is enforced in both coordinates was right. But it is
enforced on the **wrong values**. The ordering in `map_write` is:

| Line | Step | State of `lower_first` |
|---|---|---|
| 1038 | `mappings_overlap` — establishes lower-range non-overlap | **parent-namespace** ids, as written by userspace |
| 1056 | `new_idmap_permitted` | parent-namespace ids |
| 1063–1083 | re-mapping loop; **1082** `e->lower_first = lower_first` | overwritten with **kernel-global** ids from `map_id_range_down(parent_map, ...)` (1072) |
| 1089 | `sort_idmaps` -> `cmp_extents_reverse` (838) sorts by `lower_first` | kernel-global ids |

So `cmp_extents_reverse` sorts by values that came into existence at 1082,
*after* the only check that constrained them. `mappings_overlap` said nothing
about the post-remapping ids. Distinctness of those ids is precisely the
statement that `map_id_range_down` is injective on the parent map restricted to
the extents' lower ranges — i.e. it **is** the injectivity property, one level
up the namespace tree.

Consequences, which shape the proof plan in `SPEC.md`:

- Reverse-sort uniqueness is **not** available as a premise. It is a corollary
  of parent-map injectivity.
- The proof cannot be circular. Injectivity of the `>5` binary-search path
  depends on `reverse` being sorted, which would depend on injectivity of the
  *same* map — so injectivity must be proved by **induction on namespace
  depth**: the parent map is already installed and already well-formed when
  1072 runs, so its injectivity is the induction hypothesis and the child's
  follows. The base case is `init_user_ns`, whose map is the identity.
- Independently, the re-mapping loop is a second reason non-overlap is not
  self-evidently preserved: two extents of the new map may resolve through
  *different* parent extents, and only the parent's own non-overlap keeps their
  images apart. That is `SPEC.md`'s `PRESERVE-LOWER` obligation.

I was wrong to write "the same argument runs for `cmp_extents_reverse`". It
does not, and finding out why turned a premise into the target's central
theorem.

### Amendment 2 — `map_write` splits into a validator and a line parser

`map_write` is 187 lines, of which the isolation-relevant part is the
extent validation and installation. The rest is `memdup_user_nul` on a
`__user` pointer, `strchr`/`skip_spaces`/`simple_strtoul` line splitting, and
mutex-protected publication. Proposal:

- **In the verified core:** the per-extent validation chain (`first`/
  `lower_first` ≠ `(u32)-1` at 1024, no-wrap at 1031/1033,
  `mappings_overlap` at 1038, the 340 cap at 1041), the parent-map
  re-mapping loop (1072), and the install step — i.e. everything that
  establishes the preconditions the lookup path depends on.
- **Extracted and differential-fuzzed, but only proved total-safe (no panic,
  no UB), not functionally correct:** the line parser. It is worth extracting
  because it has a real behaviour worth pinning down, and because my first
  attempt to state that behaviour was wrong in a way worth recording.

  At `map_write` **1004, 1009, 1014**,
  `extent.{first,lower_first,count} = simple_strtoul(pos, &pos, 10)` assigns a
  64-bit result to a `u32` field. The chain is `simple_strtoul`
  (`lib/vsprintf.c` 126) -> `simple_strntoull` (79) -> `_parse_integer_limit`
  (`lib/kstrtox.c` 58). **The line that decides everything is `lib/kstrtox.c`
  83**, the guard `if (unlikely(res & (~0ull << 60)))`:

  - `res < 2^60` — the **unchecked** branch at **90**, `res = res * base + val`.
    For base 10 the largest reachable product is `(2^60 - 1) * 10 + 9 ≈
    1.153e19 < 2^64`, so this branch *cannot* wrap. (For base 16 it is
    `(2^60 - 1) * 16 + 15 = 2^64 - 1` — exact fit. That is what the comment at
    80–82, "only if we are within range of it in the max base we support (16)",
    is buying.)
  - `res >= 2^60` — the **checked** branch at **84–88**: on overflow
    `res = ULLONG_MAX` and `overflow = KSTRTOX_OVERFLOW`. `simple_strntoull`
    then discards the flag (`cp += (rv & ~KSTRTOX_OVERFLOW)`, line 89, with the
    kernel's own `/* FIXME */` beside it) but keeps the saturated value.

  So on **this tree** the parser is exact below `2^64` and saturating at or
  above it, and there is no mod-`2^64` wrapping regime at all. Truncation to
  `u32` then gives:

  | Input | v7.2 accumulator | `-> u32` | Verdict at 1024 |
  |---|---|---|---|
  | `0` | 0 | 0 | accept `first=0` |
  | `4294967296` (`2^32`) | 4294967296 | 0 | accept `first=0` |
  | `4294967297` | 4294967297 | 1 | accept `first=1` |
  | `4294967301` | 4294967301 | 5 | accept `first=5` |
  | `99999999999999999999999` (`10^23 - 1`) | `ULLONG_MAX` | 4294967295 | **reject `-EINVAL`** |

  **The empirical probe disagrees on exactly the last row, and the probe is
  right about the kernel it ran on.** `uidmap-probe.txt` records
  `99999999999999999999999` being *accepted* as `first=4135583743`, and
  `4135583743 = (10^23 - 1) mod 2^32` exactly — a mod-`2^64`-wrap signature,
  not a saturation signature (saturation would give `4294967295`, which 1024
  rejects). The resolution is a kernel-version difference, not a reasoning
  error in either direction:

  > `6e30111dbb40` **"lib: fix `_parse_integer_limit()` to handle overflow"**,
  > Dmitry Antipov, 2026-05-19. `git describe --contains` -> `v7.2-rc1~77^2~64`.
  > It is the commit that *added* the `2^60` guard and the `ULLONG_MAX`
  > saturation (`git log -S'res = ULLONG_MAX' -- lib/kstrtox.c` returns it and
  > nothing else).

  The probe ran against the live host kernel, **6.8.0-138-generic**, which
  predates that fix and therefore wraps mod `2^64`. `~/linux-full` is
  v7.2-rc7+687, which contains it. Both readings are correct about different
  trees; the four smaller data points agree on both kernels because they never
  reach `2^60` and so take the unchecked branch either way.

  **Corrected statement, scoped to the target tree.** On
  `v7.2-rc7-687-ge172eee25cfe` the `uid_map` line parser accepts any decimal
  literal below `2^64` and silently reduces it mod `2^32`; a literal at or
  above `2^64` saturates to `ULLONG_MAX`, truncates to exactly `(u32)-1`, and
  is rejected by the sentinel check at 1024. On pre-`6e30111dbb40` kernels
  (including 6.8) there is no saturation and *every* literal is reduced mod
  `2^32`, so the only rejected input is one landing exactly on `(u32)-1` — the
  statement the probe measured. `SPEC.md` states both, labelled by kernel, with
  the five data points, and **not** as a vulnerability: 0 and 5 are legal
  values and every downstream check still applies.

  **Calibration note.** My original paragraph asserted both "no overflow check"
  and "saturates", which cannot both be true, and invented a mod-`2^64`
  wrapping regime that does not exist on this tree. It read as convincing
  because each link in the three-file chain was individually plausible. The
  general lesson is recorded in `SPEC.md` §8: any property derived by
  multi-file source reading, without either a proof or a measurement, is marked
  **[NEEDS EMPIRICAL CHECK]** rather than presented as settled — and a
  measurement must be labelled with the kernel it was taken on, which is what
  would have caught this immediately.

- **Out of scope, stated as assumptions:** `__user` access, `mutex_lock`, and
  the `smp_wmb`/`smp_rmb` publication protocol (see §5.4 — this is the
  important one).

### Amendment 3 — the admission policy joins the target

You are right that it was missing. `INVENTORY.md` §1.2 lists
`new_idmap_permitted` (1172) and `verify_root_map` (890) as load-bearing, §9
puts them in the dependency graph, and then neither the candidate list nor the
verified core mentioned them. That was an omission, not a decision: I scoped
candidate A around "where does this id map to" and never scored "may this task
install this map".

**Including them.** Scored on the same rubric, as an addition to A rather than
a standalone candidate:

| Dim | Score | Reason |
|---|:--:|---|
| Size | 5 | `verify_root_map` 890–930 (41) + `new_idmap_permitted` 1172–1212 (41) = **82 LOC**. Verified core goes 230 -> **312 LOC**. |
| Purity | 3 | Pure over the map, but calls out to `ns_capable` (1207), `file_ns_capable` (925, 1208) and reads `cred->euid` / `ns->owner` / `ns->flags`. These are the *environment*, and get parameterized as an opaque capability oracle — the `SPIKE-STUB` pattern from `~/kernel-c-to-rust-spike/c/`. |
| Arithmetic | 2 | Almost none. It is a policy conjunction, not arithmetic. |
| Consequence | 5 | Higher than the algebra's, arguably. A defect in the algebra mis-resolves an id inside a map the kernel agreed to install; a defect here installs a map it should have refused. `verify_root_map` is the only thing standing between an unprivileged namespace and a parent-uid-0 mapping, which is the fscap-forging path §2c describes. |
| Translatability | 5 | One `for` loop over extents plus straight-line boolean logic. Nothing Charon dislikes once the oracle is a parameter. |
| Marginal | 5 | No prior formal work found. |

Total **4.10** — below A's 4.55 on its own, because the arithmetic density that
makes A worth proving is absent here. But it is not a separate candidate: it
shares A's data model, A's `WellFormed` predicate, and A's extraction, so its
marginal cost is the 82 LOC and not a second spike. And it is a *consumer of
the algebra*: `new_idmap_permitted` 1188/1192 call `make_kuid`/`make_kgid` on
`ns->parent`, so the unprivileged-admission decision is only as sound as the
mapping functions A verifies. Excluding it would have left the spike proving
things about a map without ever saying who is allowed to install one.

**One boundary condition it contributes.** At 1184–1186 the unprivileged path
reads `new_map->extent[0]` **directly**, with no `nr_extents <= 5` dispatch —
sound only because the same expression is guarded by `nr_extents == 1`. In the
flat-array model that guard is what makes the access in-bounds, so it becomes
an explicit side condition rather than an incidental fact. Properties and
theorem statements are in `SPEC.md` §4.5.

## 5. Mechanical obstacles, and how each is handled

Per the honesty constraints: each of these is a real obstacle, each resolution
is a declared modelling decision, and each goes into `OPEN_CHALLENGES.md`.

### 5.1 `bsearch` is an indirect call through a function pointer

`map_id_range_down_max` (282) and `map_id_range_up_max` (372) call the
out-of-line `bsearch` (`lib/bsearch.c` 31) passing `cmp_map_id` as a
`cmp_func_t`. Charon/Aeneas cannot carry that.

*Resolution:* monomorphize — a binary search specialized to
`uid_gid_extent` with `cmp_map_id` inlined, keeping
`__inline_bsearch`'s exact loop shape (`num >>= 1`, and the `num--` on the
right branch). *Faithfulness argument:* the callback target is statically
unique — `cmp_map_id` is the literal argument at both of the only two call
sites — so the indirection carries no data and specializing it is
semantics-preserving in a sequential model. *Verification, not assertion:* the
differential harness links the **real** `lib/bsearch.c` with the **real**
indirect call, so any divergence between the monomorphized loop and the real
one shows up as a fuzzing divergence.

### 5.2 `struct uid_gid_map` is a union — the Binder-spike blocker class

`include/linux/user_namespace.h` 25–35 overlays
`{ extent[5]; nr_extents; }` with `{ *forward; *reverse; }`. This is the
construct that stopped the Binder spike
([AeneasVerif/aeneas#1199](https://github.com/AeneasVerif/aeneas/issues/1199)),
so it deserves a straight answer rather than optimism.

*Why it is avoidable here, unlike in Binder:* the union is a space
optimization, not a semantic one. `nr_extents` sits at offset 60, past the 16
bytes `forward`/`reverse` alias, so it is readable in both arms; and the code
caps the extent count at 340 (`map_write` 1041), so a fixed
`[UidGidExtent; 340]` plus `nr_extents` represents every reachable state. The
only thing the union does semantically is let `insert_extent` (789) clobber
`extent[0..1]` when it migrates to the heap — which is sound only because
`extent[]` is never read again after `forward` is set.

*Declared modelling decision:* the Rust model uses the flat array. The
"`extent[]` is never read after migration" property becomes a **named
side condition** discharged by inspection of the four readers
(`map_id_range_down_base` 300, `map_id_range_up_base` 349, `mappings_overlap`
745, `verify_root_map` 890 — each dispatches on `nr_extents <= 5` before
choosing storage), recorded in `OPEN_CHALLENGES.md`. It is **not** hidden
inside a definition.

*Risk if this is wrong:* the flat-array model would be unfaithful and the
theorems would be about a different program. This is the single largest
faithfulness risk in the target and the reviewer should attack it first.

### 5.3 Two lookup paths, one of which must be shown redundant

The `nr_extents <= 5` linear scan and the `> 5` binary search are different
algorithms over differently-ordered data. Their agreement is not a modelling
concern but the most interesting *theorem* in the target (`SPEC.md` will state
it), and it is where a real defect would live.

### 5.4 Concurrency is out of reach, and this bounds the whole result

`map_id_range_down` (318) and `_up` (384) read `map->nr_extents`, then
`smp_rmb()` (322, 388), then the extents. `map_write` writes extents, then
`smp_wmb()` (1101), then `nr_extents` (1102). `fs/mnt_idmapping.c`'s
`copy_mnt_idmap` (219) repeats the pattern with `READ_ONCE` (222) and refuses
`nr_extents == 0` (235). The invariant is: *a non-zero `nr_extents` implies
fully-initialized extent storage*, which combined with write-once
(`map_write` 980) is what makes lock-free reads safe.

**A sequential Aeneas model cannot express this.** The theorems in Phase 3
will be about the sequential semantics of an already-published map, and the
publication protocol will be an explicit hypothesis, not a conclusion. Stating
that up front matters more than any individual lemma: someone reading
"ID mapping verified" must not come away believing the barrier discipline was
checked. It was not, and this approach cannot check it. `OPEN_CHALLENGES.md`
will name it as requiring a different tool (a memory-model checker), not more
effort with this one.

## 6. Toolchain: one concrete finding before Phase 3

The stated pinning is Charon `909ff09a`, Aeneas `c2015b86`, Lean/mathlib
`v4.31.0`, stable rustc 1.94.0, LibAFL 0.15. Verified in this environment:

| Component | Status |
|---|---|
| `rustc` | 1.94.0 (4a4ef493e 2026-03-02) — matches. |
| Lean | `~/.elan/toolchains/leanprover--lean4---v4.31.0` present. **Do not run bare `lean --version`** — elan resolves to a default `v4.33.1` and starts a download; always run inside a project with a `lean-toolchain`. |
| Charon | `~/charon/bin/charon` at `909ff09` (emits LLBC **v0.1.220**) — matches. |
| Aeneas | ⚠️ `~/aeneas/bin/aeneas` reports `3a8586f-dirty` (**newer** than the pin; `c2015b86` is an ancestor, 2026-07-09 vs 2026-07-25), its `charon-pin` is `527ea8e3`, and it **rejects** the pinned Charon's output: *"this program supports llbc emitted by charon v0.1.225 but attempted to read a file emitted by charon v0.1.220"*. The tree also carries an uncommitted change to `src/extract/ExtractBase.ml`. |
| Aeneas (correct binary) | ✅ `~/aeneas-project/aeneas/bin/aeneas` reports `c2015b86` — the pin — and successfully re-translated the previous spike's LLBC (`~/kernel-c-to-rust-spike/verify/llbc/uvc_verify-charon-909ff09a-v0.1.220.llbc`) in 14.2 s. |

**Action:** Phase 3 uses `~/aeneas-project/aeneas/bin/aeneas`, not `~/aeneas`.
This will be pinned in `CLAUDE.md`. Nothing in `~/aeneas` was modified.

## 7. Sequence after A

1. **A** (this spike): the ID-mapping algebra. `SPEC.md` next.
2. **C**, narrowed to the new theorem: `seccomp_check_filter` ≡
   `io_uring_check_cbpf_filter` modulo the context-size constant. Cheap given
   A's infrastructure, and it answers a live sandbox-design question about
   whether io_uring's filter layer inherits seccomp's audited allowlist.
3. **E**: `cap_capable_helper`, reusing whatever A establishes about modelling
   namespace trees.
4. **D**: `tnum.c` — worth doing in this toolchain, but as a replication of
   known results, and labelled as such.
5. **B**: revisit only if a separately-justified cBPF semantics becomes
   available; not reachable without one.

## 8. Status

| Phase | State |
|---|---|
| 0 — isolation surface inventory | done — `INVENTORY.md`, all citations verified against the tree |
| 1 — target selection and scoring | done — this document |
| 2 — specification | not started — `SPEC.md` |
| 3 — Rust reimplementation and proofs | not started |
| 4 — differential equivalence evidence | not started |

No Rust written. No proof claimed. No vulnerability claimed.

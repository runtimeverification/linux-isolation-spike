# linux-isolation-spike

A formal-methods spike on the Linux kernel code that AI-agent sandboxes rest on.
Every container-style sandbox — whatever product wraps it — is a Linux process
confined by the same kernel primitives: namespaces, capabilities, seccomp,
cgroups, mount isolation. This repository inventories those primitives, picks
one small high-value piece, reimplements it in Rust, extracts the Rust into
Lean 4 through Charon and Aeneas, and proves properties about it. The target is
the **user-namespace ID-mapping table** in `kernel/user_namespace.c`. The
kernel reference is `torvalds/linux` at `v7.2-rc7-687-ge172eee25cfe`.

Why this table. "Root in the container, nobody on the host" is literally a
table of extents `(first, lower_first, count)`. Every file-ownership check,
every `chown`, every capability decision and every file capability a sandboxed
process can write is resolved by looking an id up in it. The same code also
drives idmapped mounts. If two container uids could map to one host uid, or a
container uid could map outside its granted range, the sandboxed process holds
a host identity it was never given. The table is small, arithmetic-dense, and
had no prior formal treatment we could find.

## Status by phase

| Phase | Content | State |
|---|---|---|
| 0 | inventory of isolation primitives, with machine-checked line references | done — `INVENTORY.md` |
| 1 | target scoring and selection | done — `ROADMAP.md` |
| 2 | specification: data model, `WellFormed`, properties, assumptions | done — `SPEC.md` |
| 3.1–3.2 | Rust reimplementation, Charon → Aeneas → Lean round trip | done — 15 definitions, no `sorry` in generated code |
| 3.3 | safety properties S1–S5 | **done — 28 theorems, no `sorry`, standard axioms only** |
| 3.4 | functional: injectivity, round-trip, write-path preservation | in progress |
| 3.5 | functional: agreement of the two lookup paths | not started |
| 3.6 | admission policy | not started |
| 4 | differential fuzzing against the C | not started |

`VERIFY-REPORT.md` is the authoritative statement of what is proved and under
which assumptions. This README summarizes it and does not go beyond it.

## What is proved

All theorems are in `verify/lean/Safety.lean`, against the Lean model that
Aeneas generated from the Rust (`verify/lean/Uidmap.lean`). Each one is
machine-checked. `#print axioms` on every one shows only `propext`,
`Classical.choice`, `Quot.sound`; the output is in
`verify/lean/axioms-step3.txt`.

- **S1 Total safety.** Every entry point returns `ok`, a controlled failure, or
  non-termination. There is no fourth, undefined-behaviour outcome. Every array
  access in the model is bounds-checked.
- **S2+S3 No panic and termination, lookups.** `make_kuid`, `from_kuid`,
  `map_id_down`, `map_id_up` and their range forms return a value, without
  panicking and without looping, on any map with at most 340 extents. Both
  lookup paths are covered: the linear scan used below 6 extents and the binary
  search used above. The binary search needs the 340 bound; the scan needs
  nothing. That bound is what the kernel's write path enforces at
  `map_write` 1041.
- **S2+S3 No panic and termination, write path.** `insert_extent` returns
  success and grows the map by exactly one, with no out-of-bounds write, on any
  map with fewer than 340 extents — the exact boundary the kernel enforces.
- **S4 No overflow.** Under the two well-formedness clauses the write path
  establishes (`count ≥ 1`, `first + count ≤ 2^32 − 1`), the kernel's
  `u32`-wrapping computation of `first + count − 1` equals the mathematical
  value.
- **S5 No stale read.** The model reproduces the C union's aliasing: growing
  the map past 5 extents destroys the first inline slots. S5 proves the lookups
  never depend on those slots once the map is past 5 extents, and never depend
  on the heap arrays below 6.

These are safety properties. They say the code does not crash, loop or read
out of bounds. They do not say it returns the right id.

## What is not proved

1. **Barrier discipline and concurrency.** The kernel publishes a map with a
   write barrier and reads it with a read barrier, lock-free. Every theorem
   here is about a map value already in memory. A sequential model cannot
   express the publication protocol, and this toolchain cannot check it.
   Nobody should conclude from this repository that the barrier discipline was
   checked. It was not.
2. **Model T is memory-safe by construction where the C is not.** The Rust
   model has a heap array that always exists. The C has a pointer that is NULL
   between growing the map and sorting it. The kernel's write path never
   publishes a map in that state, and we enumerated every writer to confirm it
   sequentially. But the model cannot exhibit the hazard, so it cannot find
   that class of bug. The same holds for the C's out-of-bounds reads generally:
   in the model they are controlled failures. This asymmetry is the point of
   the reimplementation and also its limit.
3. **Functional correctness.** Injectivity, round-trip, preservation of
   well-formedness by the write path, agreement of the two lookup paths, and
   the admission policy are specified in `SPEC.md` and not yet proved.
4. **Three assumptions the proofs route to testing, not proof.** The kernel's
   heapsort is replaced by a sort with the same contract. Its `bsearch` callback
   is specialized to a direct call. One parameter of the comparison function is
   passed by value to work around an Aeneas crash. All three are recorded with
   justification; the planned differential harness is what exercises them.
5. **The union.** The model's dispatch between the two union arms mirrors the
   C's four dispatch sites. That correspondence is checked by reading, not by
   proof.
6. Allocation-failure paths, the copy from user space, the text parser's
   functional correctness, and the gid/projid admission differences. See
   `SPEC.md` §7.

## Measured parser behaviour — not a finding

The `/proc/PID/uid_map` line parser assigns a 64-bit parse result to a 32-bit
field. Measured on the **host kernel 6.8.0-138-generic**, writing to a fresh
user namespace:

| Written | Installed |
|---|---|
| `0 1000 1` | `0 1000 1` |
| `4294967296 1000 1` | `0 1000 1` |
| `4294967297 1000 1` | `1 1000 1` |
| `4294967301 1000 1` | `5 1000 1` |
| `99999999999999999999999 1000 1` | `4135583743 1000 1` |

`4135583743 = (10^23 − 1) mod 2^32`. On 6.8 every literal is reduced mod
`2^32`. On the **target tree v7.2** the behaviour differs: commit
`6e30111dbb40` added saturation in `lib/kstrtox.c`, so literals at or above
`2^64` are rejected, incidentally, because the saturated value truncates onto
the `(u32)-1` sentinel. Literals below `2^64` are still reduced mod `2^32`.
The truncation site is `map_write` 1004/1009/1014. This is not a
vulnerability: the resulting values are legal and every later check still
applies. It is recorded because the same input gives different answers on the
two kernels, and a test harness that compiled the wrong `kstrtox.c` would
silently confirm the wrong one. Details in `SPEC.md` §6.

## Toolchain and reproduce

Pinned: Charon `909ff09` (LLBC v0.1.220, `--preset=aeneas`), Aeneas
`c2015b86`, Lean 4 with mathlib at `v4.31.0`, Rust stable 1.94.0, LibAFL 0.15.

```sh
cd rust && cargo test --release                       # 6 sanity tests
cd rust && PATH=$HOME/charon/bin:$PATH charon cargo --preset=aeneas
~/aeneas-project/aeneas/bin/aeneas -backend lean \
    verify/llbc/uidmap-charon-909ff09a-v0.1.220.llbc -dest verify/lean/
cd verify/lean && ./setup-local.sh && lake build       # Uidmap + Safety
cd verify/lean && ./axioms.sh                          # 42 lines, standard axioms
```

`setup-local.sh` points the Lean project at an already-built Aeneas backend so
`lake build` needs no network. `CLAUDE.md` has the full build notes.

## Open problems and the Aeneas reproducer

`OPEN_CHALLENGES.md` lists every gap, every assumption the theorems rest on,
and every toolchain blocker. One is worth calling out for Aeneas users:
**B-1**, a five-line program that crashes Aeneas `c2015b86` with an internal
`Unreachable` in abstraction merging. Branch on a `bool` read through a
reference, join the branch into a value, then use that value in a later
condition. The reproducer is `repro/B-1-bool-deref-join.rs`.

## Layout

- `INVENTORY.md`, `ROADMAP.md`, `SPEC.md` — phases 0–2
- `rust/` — the faithful Rust reimplementation and its sanity tests
- `verify/llbc/` — the pinned Charon output
- `verify/lean/` — the generated model, the theorems, the axiom audit
- `repro/` — toolchain reproducers
- `VERIFY-REPORT.md`, `OPEN_CHALLENGES.md` — results and gaps
- `uidmap-probe.sh` — the parser measurement above

License: GPL-2.0, matching the kernel code it reimplements.

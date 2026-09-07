# linux-isolation spike

Verification spike on Linux kernel isolation primitives, for an AI-agent
sandboxing threat model. Target: the user-namespace ID-mapping algebra in
`kernel/user_namespace.c`, plus the admission policy.

Phases: 0 inventory (done), 1 target selection (done), 2 specification (done),
3 Rust reimplementation and Lean proofs, 4 differential equivalence evidence.

## Environment

- Kernel sources, read-only, never modify: `~/linux-full`, at
  `v7.2-rc7-687-ge172eee25cfe`, branch `uvc-series-v1`. Three uvcvideo commits
  sit on top of upstream and touch only
  `drivers/media/usb/uvc/uvc_driver.c`. No inventoried file is modified.
- **The host kernel is not the target kernel.** The host runs 6.8.0-138-generic.
  Anything measured on the host is a statement about 6.8, not about
  `~/linux-full`. Label every measurement with the kernel it came from. The
  `lib/kstrtox.c` overflow behaviour differs between the two; see `SPEC.md` §6.
- Charon: `~/charon/bin/charon`, `909ff09`, emits LLBC v0.1.220.
- Aeneas: **use `~/aeneas-project/aeneas/bin/aeneas`** (reports the `c2015b86`
  pin). Do **not** use `~/aeneas/bin/aeneas`: it reports `3a8586f-dirty`,
  expects LLBC v0.1.225, rejects our Charon's output, and carries an
  uncommitted change to `src/extract/ExtractBase.ml` that is not ours to touch.
- Lean: toolchain `v4.31.0`, mathlib matching. Never run bare `lean --version`;
  elan resolves to a default `v4.33.1` and starts a download. Always run inside
  a project with a `lean-toolchain`.
- rustc stable 1.94.0. LibAFL 0.15.
- Prior art in this environment to reuse rather than reinvent:
  `~/kernel-c-to-rust-spike` (extraction scripts, Lakefile layout, report
  structure, and `fuzz/build.rs` including the `-fno-strict-overflow` note),
  `~/c2lean`.

## Calibration rule

Any claim reached by following logic across more than one source file must be
either empirically checked or explicitly marked `[NEEDS EMPIRICAL CHECK]`.
Do not present such a claim as settled.

This rule was introduced after a three-file chain of reasoning about
`simple_strtoul` produced a confident and false conclusion. Applying it has
since caught three more wrong readings (the `map_write` 1031 no-wrap bound, the
`init_user_ns` initializer, and the reverse sort key). The hit rate for
multi-file reasoning in this codebase is poor. Treat it accordingly.

Corollary: when a measurement and the source disagree, first ask whether they
are the same kernel, the same build flags, or the same branch, before
concluding either is wrong.

## Honesty constraints

- Never call a `sorry`-carrying result proved. Never write "verified" about
  anything not yet proved.
- Never claim a vulnerability, memory-safety bug or isolation break without a
  reproducing witness, and even then describe it as a spec violation in our
  reimplementation until confirmed against the C.
- Assumptions appear as explicit hypotheses in theorem statements, and the
  theorem-by-assumption matrix (`SPEC.md` §5) goes into `VERIFY-REPORT.md`
  beside the `#print axioms` output. The axiom audit alone understates what the
  results rest on, because `A-PUB` and `A-UNION` are claims about C that Lean
  cannot quantify over.
- `A-PUB` (barrier discipline and concurrency) is out of reach for a sequential
  Aeneas model. It is a tool gap, not an effort gap. It stays first on the
  exclusion list. Nobody reading our output should conclude the publication
  protocol was checked.
- If the pipeline blocks on a mechanical limitation (unions, `dyn` trait
  objects, raw casts, inline asm, function pointers), record it in
  `OPEN_CHALLENGES.md` and stop, rather than working around it with an
  unfaithful model.
- Equivalence claims are against the C as this tree compiles it, and nothing
  stronger.

## Artifacts

`INVENTORY.md`, `ROADMAP.md`, `SPEC.md`, `OPEN_CHALLENGES.md`,
`VERIFY-REPORT.md`, plus `check_citations.py`, `triage_misses.py`,
`uidmap-probe.sh` and their outputs. Commit after each phase.
## Build commands

```sh
# 1. The Rust reimplementation and its sanity tests
cd rust && cargo build --release && cargo test --release

# 2. Charon: Rust -> LLBC. Requires --preset=aeneas.
cd rust && PATH=$HOME/charon/bin:$PATH charon cargo --preset=aeneas
cp rust/uidmap.llbc verify/llbc/uidmap-charon-909ff09a-v0.1.220.llbc

# 3. Aeneas: LLBC -> Lean. MUST be the aeneas-project binary (see Environment).
~/aeneas-project/aeneas/bin/aeneas -backend lean \
    verify/llbc/uidmap-charon-909ff09a-v0.1.220.llbc -dest verify/lean/
cp verify/lean/Uidmap-charon-909ff09a-v0.1.220.lean verify/lean/Uidmap.lean

# 4. Lean. setup-local.sh wires the project to the already-built Aeneas
#    backend + mathlib with no network; plain `lake build` would start a fresh
#    mathlib4 clone instead. Run it once per checkout.
cd verify/lean && ./setup-local.sh && lake build

# 5. Axiom audit. Expect [propext, Classical.choice, Quot.sound] on every line.
cd verify/lean && ./axioms.sh
```

`verify/lean/lake-manifest.json` and `verify/lean/.lake/` are generated by
`setup-local.sh` and are not committed: the manifest holds an absolute path to
the local Aeneas checkout.

Note for the audit: `lake build` reports `declaration uses 'sorry'` for
`Aeneas/Std/Slice.lean:363`, `Slice.lean:586` and `StringIter.lean:13`. Those
are in the *Aeneas standard library*, not in our code. Step 2's audit confirms
empirically that our model does not reach them — it uses `Array _ 5#usize` /
`Array _ 340#usize` with checked indexing and no `Slice` at all — but that has
to be re-checked with `./axioms.sh` after every change, never assumed.

## Lemma index

Property tags are `SPEC.md`'s. `VERIFY-REPORT.md` holds the authoritative
status; this is the map from tag to where it lives.

| Tag | Property | Lean location | Status |
|---|---|---|---|
| — | the extracted model (15 defs) | `verify/lean/Uidmap.lean` | generated, `sorry`-free, axiom-clean |
| S1 | `TOTAL-SAFETY` | `verify/lean/Safety.lean` | step 3, not started |
| S2 | `NO-PANIC` | `verify/lean/Safety.lean` | step 3, not started |
| S3 | `TERMINATION` | `verify/lean/Safety.lean` | step 3, not started |
| S4 | `NO-OVERFLOW` | `verify/lean/Safety.lean` | step 3, not started |
| S5 | `NO-STALE-READ` (Model T) | `verify/lean/Safety.lean` | step 3, not started |
| F2 | `INJECTIVITY` | `verify/lean/Algebra.lean` | step 4, not started |
| F3 | `ROUNDTRIP` | `verify/lean/Algebra.lean` | step 4, not started |
| F5 | `PRESERVE` / `PRESERVE-LOWER` | `verify/lean/WritePath.lean` | step 4, not started |
| F4 | `AGREEMENT` | `verify/lean/Agreement.lean` | step 5, not started |
| F6 | `ADMISSION` + 3 lemmas | `verify/lean/Admission.lean` | step 6, not started |

## Phase 3 model choice

Results are in **Model T** (`SPEC.md` §1.3): the `struct uid_gid_map` union's
two arms are separate fields and `insert_extent` reproduces the clobber the two
pointer stores inflict on `extent[0]` and `extent[1].first`. Model T extracted
cleanly, so the Model F fallback was **not** used and `A-UNION` is an
obligation (S5) rather than an assumption. The one Aeneas blocker hit so far,
B-1 in `OPEN_CHALLENGES.md`, is unrelated to the union.

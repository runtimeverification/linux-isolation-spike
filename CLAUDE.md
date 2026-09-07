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
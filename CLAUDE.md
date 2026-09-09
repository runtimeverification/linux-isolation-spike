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
| S1 | `TOTAL-SAFETY` — `total_safety` + 5 entry-point instances | `verify/lean/Safety.lean` | **proved**, unconditional |
| S2+S3 | lookups: `cmp_map_id_spec`, `*_base_loop_spec`, `*_base_spec`, `bsearch_extent_loop_spec`, `bsearch_extent_spec`, `map_id_range_{down,up}_spec`, `map_id_{down,up}_spec`, `make_kuid_spec`, `from_kuid_spec` | `verify/lean/Safety.lean` | **proved**; hypothesis `nr_extents ≤ 340` only |
| S2+S3 | write path: `cast_usize_val`, `insert_extent_loop_spec`, `insert_extent_spec` | `verify/lean/Safety.lean` | **proved**; hypothesis `nr_extents < 340` |
| S4 | `NO-OVERFLOW` bridge: `last_val`, `id2_val` | `verify/lean/Safety.lean` | **proved**; hyps `WF-COUNT`, `WF-NOWRAP`. SPEC §4.1's literal `no_overflow_upper` lands with `WellFormed` in step 4 |
| S5 | `NO-STALE-READ` (Model T): `no_stale_read_down`, `no_stale_read_up`, `base_arm_only_down` | `verify/lean/Safety.lean` | **proved**; reduces `A-UNION` to a structural-correspondence check, does not eliminate it |
| — | abstract map `absFwd`/`absRev`, `WellFormed`, `SortedArms`, algebra lemmas, `init_user_ns_map_wf` | `verify/lean/Spec.lean` | **proved** (9 audited) |
| F1 | `down_sound`, `up_sound` (single id, both paths), `down_range_sound` (range, both paths) | `Algebra.lean`, `WritePath.lean` | **proved** |
| F2 | `INJECTIVITY` — `down_injective` | `verify/lean/Algebra.lean` | **proved**, both paths, `sorry`-free |
| F3 | `ROUNDTRIP` — `roundtrip_sound` (never an unrelated id), `roundtrip_complete_le5` | `verify/lean/Algebra.lean` | **proved**; `roundtrip_complete` above 5 rests on L-1 |
| F5 | `PRESERVE-LOWER` mathematics — `remap_disjoint`, `preserve_lower_list`; `insert_extent_fun`, `mappings_overlap_fun`, `nowrap_check_iff`, `lines_loop_fun`, `write_preserves_wf`, `reachable_wf` | `verify/lean/WritePath.lean` | mathematics **proved**; assembly proved modulo L-3 `sort_idmaps_fun` and L-4 `remap_install_fun` (`OPEN_CHALLENGES.md`) |
| F4 | `AGREEMENT` — core is L-1 `bsearch_complete` | `verify/lean/Agreement.lean` | step 5, not started |
| F6 | `ADMISSION` + 3 lemmas | `verify/lean/Admission.lean` | step 6, not started |

Step 4 audit: 93 declarations; `sorryAx` on exactly `bsearch_complete`,
`roundtrip_complete`, `sort_idmaps_fun`, `remap_install_fun`, and the three
that inherit (`lines_loop_fun`, `write_preserves_wf`, `reachable_wf`); saved
in `verify/lean/axioms-step4.txt`.

Step 3 audit: 42 declarations, all `[propext, Classical.choice, Quot.sound]`
(two on the strict subset `[propext, Quot.sound]`), no `sorryAx`; saved in
`verify/lean/axioms-step3.txt`. `Safety.lean`: 28 theorems, 0 `sorry`.

Proof idioms that worked here, for steps 4–6 (all against Aeneas `c2015b86`):
- Loops: `loop.spec_decr_nat measure inv post` gives no-panic + termination +
  postcondition at once; for a pair-state loop, `rintro ⟨a, b⟩ hinv; dsimp only`
  before `unfold body`, or `split` will hit the pair-match instead of the `if`.
- `step with <spec> as ⟨ v, h ⟩` — one id for a `True` post; `_`, not `-`, for
  an unwanted hypothesis. After `step`, `cont` goals are usually already
  reduced past `spec_ok`: use `all_goals (try constructor); all_goals scalar_tac`.
- A leading `simp only [lift, bind_tc_ok]` inlines every `lift (cast ..)`, so
  no later `step with UScalar.cast_inBounds_spec` will find a bind; use the pure
  `cast_usize_val` for bounds instead.
- Case-split a `match` under `⦃⦄` with `rcases x with _ | e`, not `split`.
- `UScalar.ShiftRight_IScalar_spec`'s width side condition needs
  `cases System.Platform.numBits_eq <;> simp [*]`.
- **`step … as ⟨…⟩` binding rule:** ids fill the *value's tuple components*
  first, then the post's conjuncts one at a time. For a pair result with a
  four-conjunct post write `as ⟨v1, v2, h1, h2, h3, h4⟩`; `as ⟨v, h⟩` on a pair
  silently makes `h` the second component. An `obtain` on the wrong thing then
  fails far away (`subst` "did not find equation", or `rcases` on an `Eq`
  silently substituting).
- After `step`, a `cont`/`ok` goal is usually already reduced past `spec_ok`
  *and* flattened with `and_assoc` — even under the spec predicate. Use a flat
  `refine ⟨…⟩`, or `apply (spec_ok _).mpr` then flat. `show` normalizes the
  unreduced tuple projections `(a, b, c).2.1` before `left`/`right`.
- `dsimp only` on a goal containing scalar literals can leave it "not
  type-correct under instances transparency" (a `decide` proof gets reduced),
  after which `simp` refuses to fire. Prefer `(spec_ok _).mpr` / `exact` by
  definitional unfolding, or `dsimp only at h₁ h₂` on specific hypotheses.
- `split` on a freshly unfolded folded-loop body (`map_write_body_loop0.body`)
  exceeds simp's step budget; use `by_cases h : c` + `rw [if_pos h]` /
  `rw [if_neg h]`. The folded body's `let x := …` is a real `let`; `rw` cannot
  see through it, so `dsimp only` first *before* unfolding is fine, after is
  not (see previous point).
- A `let (a, b, c) := (x, y, z)` produced by `bind_tc_ok` is a `match` that
  neither `simp only` nor `dsimp only` iota-reduces; restate the reduced form
  with `have h' : (if … then … else …) = ok r := h` — the `:= h` is checked by
  definitional unfolding, which does reduce it. `change` with `_` cannot infer
  `ite`'s `else` argument here.
- Multi-line record literals are rejected when the continuation line is
  indented left of the opening `{`; write one-line records, or a one-line
  `def mkMap …` and use that (`resMap` in WritePath.lean).
- `List.getElem?` in statements (`Remapped`, `dispatch_read`), not `getElem`:
  rewriting the list or the index under a dependent bound proof fails with
  "motive is not type correct".
- Big folded-loop theorems need `set_option maxHeartbeats 2000000 in` — placed
  *above* the doc comment, or Lean reports `expected 'lemma'`.

## Phase 3 model choice

Results are in **Model T** (`SPEC.md` §1.3): the `struct uid_gid_map` union's
two arms are separate fields and `insert_extent` reproduces the clobber the two
pointer stores inflict on `extent[0]` and `extent[1].first`. Model T extracted
cleanly, so the Model F fallback was **not** used and `A-UNION` is an
obligation (S5) rather than an assumption. The one Aeneas blocker hit so far,
B-1 in `OPEN_CHALLENGES.md`, is unrelated to the union.

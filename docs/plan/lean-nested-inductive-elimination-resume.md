# Resume here: Lean TL2.14 nested-inductive elimination

Status: paused cleanly after M0; M1 diagnostic preflight is next

Date paused: 2026-07-22

This is the single resume entry point for the current Lean work stream. Read
this file first when work resumes, then follow its links only as needed. The
authoritative full execution contract remains the
[TL2.14 P0--M6 plan](lean-nested-inductive-elimination-tl2.14-plan-2026-07-22.md),
and the decision gate remains
[proposed ADR-0355](../research/09-decisions/adr-0355-preregister-lean-nested-inductive-elimination.md).

## Resume contract

- Work in `/home/mjbommar/projects/personal/axeyum`.
- Do **not** change branches. Other agents may be editing the shared worktree.
- At pause time the active branch was `repro/smtcomp-scoring`, and local HEAD,
  its tracking ref, and the remote branch all resolved to
  `e102670ecbfe4645f732430dbf28ff1ccecf21a8`.
- Reverify the current branch and refs; do not switch back if another actor has
  intentionally advanced them.
- No partial M1 product edits existed at pause time in
  `crates/axeyum-lean-import/src/lib.rs` or
  `crates/axeyum-lean-import/tests/official_construct_matrix.rs`.
- The worktree contained unrelated concurrent FP, IR, BV, SMT-LIB, query,
  rewrite, benchmark, corpus, and review changes. Inspect ownership again and
  stage only files or hunks owned by this stream.
- Add, commit, push, and verify each bounded milestone. Never accumulate
  several milestones into an unpushed worktree.

## What is complete

The dependency correction, preregistration, and evidence freeze are complete
and pushed:

1. TL2.13 atomic mutual-inductive groups completed at `340cf721`.
2. P0 corrected the boundary and preregistered TL2.14 at `def1000f`:
   nested-inductive expansion/restoration is a kernel admission transformation;
   native well-founded/source recursion remains elaborator work in TL4.10.
3. M0 froze the official source and wire evidence at `e102670e`, without
   allowing Axeyum to observe or import the new streams.

The complete M0 narrative is
[lean-nested-inductive-elimination-m0-2026-07-22.md](lean-nested-inductive-elimination-m0-2026-07-22.md),
and its fail-closed machine contract is
[lean-nested-inductive-elimination-v1.json](lean-nested-inductive-elimination-v1.json).

### Frozen M0 evidence

- Positive source:
  `docs/plan/fixtures/lean-v4.30-nested-inductive-computation.lean`,
  SHA-256 `c5cadeaf11302d5ca9b5a60b2a3b72998ad994e7eb176ddc5de40ebfc05c475d`,
  2,917 bytes / 98 lines.
- Negative source:
  `docs/plan/fixtures/lean-v4.30-nested-inductive-negative.lean`,
  SHA-256 `aedb42cf5d4b8eccb24252ffeaab33ce10cdd5a21bf1ad36290e1ab87387e398`,
  260 bytes / 11 lines.
- Repeated positive compilation produced one OLEAN SHA-256:
  `d7d03cb863626f1ddc2a80b0dee3ae19fbc001dc2fb4ac60f6b9e27c7b7f53c2`.
- `roseAuxiliaryRecursorComputes` stream:
  SHA-256 `36fb9c6f85a99a7d6d1f6329a2cfe5265b148f0138e979d6d391d9e8879e07de`,
  36,706 bytes / 642 records.
- `indexedAuxiliaryRecursorComputes` stream:
  SHA-256 `a14ca423410c4f0a86c2a2cea193e5a76bd91428e348402b3dd32e1603481429`,
  40,119 bytes / 714 records.
- `repeatedContainerReusesAuxiliaryRecursor` stream:
  SHA-256 `af369edb2d9e0346a5457ba4c9cde6f3030ca08002dc931c5fb26709e0f74344`,
  37,771 bytes / 666 records.
- Aggregate official evidence: 114,596 bytes / 2,022 records.
- Exact pinned-Lean negative diagnostic:
  `(kernel) invalid nested inductive datatype
  'AxeyumNestedInductiveNegative.Box', nested inductive datatypes parameters
  cannot contain local variables.`
- `Rose`, `IndexedRose`, and `RepeatRose` each report `numNested = 1`.
  Two identical nested fields in `RepeatRose` reuse one auxiliary family.
- Wire recursor order is descriptive and varies:
  `Rose [Rose.rec_1, Rose.rec]`,
  `IndexedRose [IndexedRose.rec_1, IndexedRose.rec]`, and
  `RepeatRose [RepeatRose.rec, RepeatRose.rec_1]`. Later comparison must use
  checked names and owned rules, never array position.
- The existing nested construct still fails at line 248 with
  `Malformed("single-family inductive must export one recursor")`.
- The well-founded control completes with 35 declarations and zero axioms.
- Thirteen checker tests freeze the evidence and prevent premature product
  credit. No new M0 stream has been passed to Axeyum.

### Validation completed for M0

- The positive source compiled twice successfully and the negative source
  failed twice with the exact registered diagnostic.
- All three selected exports were byte-identical across two runs.
- `python3 scripts/check-lean-nested-inductive-elimination.py --check`
- `python3 -m unittest scripts.tests.test_lean_nested_inductive_elimination`
- `python3 scripts/check-parity-docs.py` with `DISAGREE=0`
- `python3 scripts/gen-lean-compatibility.py --check` with six registered
  decline codes
- `./scripts/check-foundational-resources.sh`
- `./scripts/check-links.sh`
- `git diff --check`
- `bash -n scripts/check.sh`

M0 changed only documents, fixtures, registrations, and checkers. A workspace
Rust build was deliberately not claimed: it was not required for the evidence
freeze, and unrelated concurrent Rust edits existed in the shared worktree.

## Exact next milestone: M1 diagnostic preflight

M1 is deliberately narrow. In `import_inductive` in
`crates/axeyum-lean-import/src/lib.rs`, the current single-family path checks
`types.len() == 1 && recursors.len() != 1` before recognizing `numNested`.
That turns the valid nested shape of one main plus one auxiliary recursor into
an accidental `Malformed` result.

The next implementation must:

1. Parse and validate the relevant inductive metadata, including `numNested`,
   before applying the non-nested singleton recursor-count policy, or add an
   equivalently narrow typed preflight.
2. Move the frozen nested construct outcome to exactly
   `ImportError::Unsupported { code: "inductive-nested", ... }`.
3. Produce no admitted declaration, partial publication, or `CompletedImport`.
4. Preserve the exact non-nested policy: malformed one-family declarations
   with zero or two recursors remain malformed when `numNested == 0`.
5. Repeat the frozen nested case twice and retain the well-founded and
   720/768/840 controls.
6. Keep all three new M0 computation streams outside the importer. M4, not M1,
   owns their first product observation.
7. Commit, push, and verify local/tracking/remote equality before M2.

Add focused importer tests in
`crates/axeyum-lean-import/tests/official_construct_matrix.rs` or the nearest
existing focused test surface. Include synthetic recursor-count variants so
the new preflight cannot accidentally weaken ordinary singleton validation.

Do not silently rewrite the historical official construct matrix. The M0
checker can project a future `tl2_14_update`, but M5 owns the append-only
assurance overlay and removal of the live nested decline. Before changing any
generated assurance artifact earlier, inspect its contract and amend the plan
explicitly if necessary.

## Remaining milestones after M1

- **M2 — native expansion and restoration:** implement private structural
  discovery, complete auxiliary-container group copying, fixed-point queuing,
  final-surface restoration, deterministic `.rec_N` publication, and
  transaction-wide rollback while reusing TL2.13's one atomic group checker.
- **M3 — deterministic generated grammar:** run at least 640 unique public-path
  profiles twice, close expansion/reuse/restoration mutation teeth, and retain
  exact 720/768/840 population descriptors.
- **M4 — importer and exact official declarations:** remove only the nested
  policy decline after native support, derive rather than trust `numNested` and
  recursor identities, import all frozen official streams twice, compare exact
  contracts, and close wire/publication mutations.
- **M5 — computation and assurance:** reproduce the pinned-Lean computations,
  require the registered cross-nested normal forms in Axeyum, append a
  history-preserving assurance overlay, and only then remove the live decline.
- **M6 — final closure:** run every bounded final gate, decide ADR-0355 from its
  preregistered exits, and synchronize PLAN, STATUS, roadmaps, generated docs,
  and the final handoff.

The detailed positive/negative matrices, mutation list, generated grammar,
stop conditions, and explicit non-claims remain binding in the
[full execution plan](lean-nested-inductive-elimination-tl2.14-plan-2026-07-22.md).

## First commands on resume

```sh
cd /home/mjbommar/projects/personal/axeyum
git branch --show-current
git rev-parse HEAD
git rev-parse '@{upstream}'
git status --short
python3 scripts/check-lean-nested-inductive-elimination.py --check
python3 -m unittest scripts.tests.test_lean_nested_inductive_elimination
sed -n '710,815p' crates/axeyum-lean-import/src/lib.rs
sed -n '1,300p' crates/axeyum-lean-import/tests/official_construct_matrix.rs
```

Then record a bounded M1 plan, inspect current ownership one more time, and
make the preflight/test edits with small reviewable patches.

## Tools and resource envelope

- Lean 4.30:
  `/home/mjbommar/.cache/axeyum-lean-gate-v430-audit/elan-home/toolchains/leanprover--lean4---v4.30.0/bin/lean`
- `lean4export`:
  `/home/mjbommar/.cache/axeyum-lean-system-research/lean4export/.lake/build/bin/lean4export`
- Run heavy processes with one worker through
  `systemd-run --user --scope --quiet -p MemoryHigh=3G -p MemoryMax=4G
  -p MemorySwapMax=512M`.
- Use repository-local temporary directories, one Cargo job, and one test
  thread. Do not run an unbounded or parallel-heavy workspace build.
- `just` was unavailable in the paused environment; use the documented
  underlying commands when it remains unavailable.

An OOM, signal, nondeterministic artifact, missing exact pin, weakened
population, required limit above 4 GiB, leaked temporary auxiliary name,
partial publication, or overlap with another actor's target file is a stop
condition. Preserve the evidence and amend ADR-0355 before broadening scope.

## Claims that remain false

Axeyum does not yet admit nested inductives. TL2.14 does not establish native
Lean source parsing, inductive-command elaboration, pattern/equation
compilation, structural or well-founded recursion elaboration, termination
checking, broad `Init`/`Std`/mathlib admission, full Lean-kernel parity, or a
replacement for official Lean.

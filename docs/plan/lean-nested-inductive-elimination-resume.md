# Resume here: Lean TL2.14 nested-inductive elimination

Status: M3 complete; M4 importer and exact official declarations next

Date paused: 2026-07-22

This is the single resume entry point for the current Lean work stream. Read
this file first when work resumes, then follow its links only as needed. The
authoritative full execution contract remains the
[TL2.14 P0--M6 plan](lean-nested-inductive-elimination-tl2.14-plan-2026-07-22.md),
and the decision gate remains
[proposed ADR-0355](../research/09-decisions/adr-0355-preregister-lean-nested-inductive-elimination.md).

## Resume contract

- Work in the isolated topic worktree
  `/home/mjbommar/projects/personal/axeyum-lean-nested` on branch
  `agent/lean/nested-inductive-elimination`.
- The topic branch tracks `origin/agent/lean/nested-inductive-elimination` and
  was created from synchronized `main` revision
  `48fece10d1c93cf8cf8df7c2d4875ea18cdafa8e`.
- M1's semantic implementation is
  `893afc1f0de3ca60972b3eaf4d84ff0b3d6c66e7`.
- M2's native kernel implementation is
  `96b6fbd4da7e20277b338f59983fbe7316b31d22`.
- M3's deterministic grammar and restoration-integrity implementation is
  `6a2afdd57c969bc1a847d77a85cc99552fa935b1`.
- Reverify the current branch, local HEAD, tracking ref, and remote ref before
  editing. Do not switch, reset, restore, or force any other live worktree.
- No partial M4 edits exist at this checkpoint. Inspect ownership again before
  changing importer policy or observing any frozen official stream.
- The integration checkout at `/home/mjbommar/projects/personal/axeyum` had
  unrelated dirty benchmark/corpus/review artifacts and remains untouched by
  this lane.
- Add, commit, push, and verify each bounded milestone. Never accumulate
  several milestones into an unpushed worktree.

## What is complete

The dependency correction, preregistration, evidence freeze, and diagnostic
preflight are complete and pushed:

1. TL2.13 atomic mutual-inductive groups completed at `340cf721`.
2. P0 corrected the boundary and preregistered TL2.14 at `def1000f`:
   nested-inductive expansion/restoration is a kernel admission transformation;
   native well-founded/source recursion remains elaborator work in TL4.10.
3. M0 froze the official source and wire evidence at `e102670e`, without
   allowing Axeyum to observe or import the new streams.
4. M1 corrected the nested diagnostic boundary at `893afc1f`: a well-shaped
   main-plus-auxiliary recursor population now returns typed
   `Unsupported("inductive-nested")` before admission, while ordinary malformed
   singleton counts retain their exact error.
5. M2 implemented native structural expansion, complete checked-container
   copying, fixed-point queuing, ordinary atomic group checking, source-surface
   restoration, deterministic `.rec_N` publication, and transaction-wide
   rollback at `96b6fbd4`.
6. M3 repeated the exact 640-case public grammar twice, froze descriptor digest
   `a20fe056c9443a37`, closed independent public-surface/dependency/iota
   observation, and forced transactional restoration mutations at `6a2afdd5`.
   The pre-semantic stop-review amendments are `ab5dbf99` and `d03ba0fc`.

The complete M0 narrative is
[lean-nested-inductive-elimination-m0-2026-07-22.md](lean-nested-inductive-elimination-m0-2026-07-22.md),
and its fail-closed machine contract is
[lean-nested-inductive-elimination-v1.json](lean-nested-inductive-elimination-v1.json).
The complete M1 result is
[lean-nested-inductive-elimination-m1-2026-07-22.md](lean-nested-inductive-elimination-m1-2026-07-22.md).
The complete M2 result is
[lean-nested-inductive-elimination-m2-2026-07-22.md](lean-nested-inductive-elimination-m2-2026-07-22.md).
The complete M3 result is
[lean-nested-inductive-elimination-m3-2026-07-22.md](lean-nested-inductive-elimination-m3-2026-07-22.md).

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
- The M0 baseline observed the existing nested construct fail at line 248 with
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

## M1 result

M1 parses consistent `numNested` metadata first, checks the claimed recursor
population as source-family count plus auxiliary count, and returns
`Unsupported("inductive-nested")` before any kernel admission. Missing or extra
nested recursors remain malformed; ordinary singleton records with zero or two
recursors retain the exact historical malformed message. The official nested
row and its direct-recursive control repeat twice, the well-founded import
still completes, and the 720/768/840 summaries remain exact. The complete
importer suite, warning-denied Clippy/rustdoc, M0 contracts, and documentation
gates pass. No M0 computation stream was observed by the importer and no
generated assurance artifact changed.

## M2 result

M2 adds a private rollback-aware checked-group index, structurally discovers
and deduplicates nested container applications, copies complete container
mutual groups, processes copied constructors to a fixed point, and checks the
expanded group once through TL2.13's ordinary atomic worker. It then rolls back
the temporary group, clears both environment-sensitive caches, recursively
restores family/constructor/recursor expressions, publishes exact string
`rec_N` auxiliary names, infers every final type and closed rule after complete
recursor staging, and registers only the source family group.

Twenty-three focused native tests cover repeated/distinct parameterizations,
outer and container groups, zero/one/two parameters and indices, universes,
higher-order and depth-two shapes, `Prop`/`Type`, empty owners, exact public
surface inference, typed negatives, bounds, name collisions, rollback/retry,
and the computation chain `Rose.rec -> Rose.rec_1 -> Rose.rec`. The complete
kernel and importer suites, retained 720/768/840 populations, strict Clippy,
strict rustdoc, and M0 no-observation contract pass. The importer remains at
the M1 nested decline and no M0 computation stream was observed.

## M3 result

M3 runs the exact preregistered 640-case grammar twice in fresh kernels with
byte-identical descriptor digest `a20fe056c9443a37`. The independent observer
checks exact public families, constructors, recursors, specialized keys,
motives, minors, per-rule dependency targets, inference, temporary-name
absence, and 320 main plus 462 auxiliary typed iota reductions. Sixteen
malformed private mutations prove exact whole-environment rollback and valid
retry; type-correct recursor mutations reject or change a named observation.

The independent audit triggered the registered stop condition before semantic
commit because temporary copied-constructor owner/index/type mutations were
not consumed by M2 restoration. Amendments `ab5dbf99` and `d03ba0fc` bind a
narrow validator for the already-checked temporary declaration surface. The
final audit found no semantic blockers. The complete kernel/importer suites,
strict tooling, retained 720/768/840 populations, and M0 contracts pass.
Semantic commit `6a2afdd5` is pushed with local/tracking/remote equality; the
importer and all frozen M0 streams remain unchanged.

## Exact next milestone: M4 importer and exact official declarations

M4 removes only the structural nested policy decline after native M2/M3
support. It must derive rather than trust group-wide `numNested`, auxiliary
recursor identity, and wire order; import the existing construct plus all three
frozen computation streams twice; compare exact checked family, constructor,
recursor, type, rule, owner, index, field, and publication contracts; and close
the preregistered wire metadata/order/type/rule/publication mutations. The
well-founded 35-declaration/zero-axiom root and exact 720/768/840/640 generated
controls remain mandatory.

The
[M4 exact importer plan](lean-nested-inductive-elimination-m4-plan-2026-07-22.md)
is frozen before implementation. It derives the auxiliary count from checked
main-recursor motive metadata, compares the complete name-keyed main/auxiliary
surface, binds four twice-imported official inventories, freezes 20 rejecting
wire/publication classes plus order non-authority controls, and leaves all
kernel, fixture, identity, assurance, and live-decline artifacts untouched.

M4 must not claim cross-nested normal-form computation merely because the
official declarations import. M5 owns reproduction of the registered normal
forms, the assurance overlay, and removal of the live decline.

## Remaining milestones after M3

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
cd /home/mjbommar/projects/personal/axeyum-lean-nested
git branch --show-current
git rev-parse HEAD
git rev-parse '@{upstream}'
git ls-remote --heads origin agent/lean/nested-inductive-elimination
git status --short
python3 scripts/check-lean-nested-inductive-elimination.py --check
python3 -m unittest scripts.tests.test_lean_nested_inductive_elimination
sed -n '1,460p' crates/axeyum-lean-kernel/src/inductive.rs
sed -n '1,365p' docs/plan/lean-nested-inductive-elimination-tl2.14-plan-2026-07-22.md
```

Then reverify M4 ownership and implement the frozen exact importer plan. Remove
only the structural nested decline without claiming M5 computation credit.

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

Axeyum's native kernel now admits the structurally registered nested-inductive
container shapes covered by M2. The official nested importer row still declines,
and TL2.14 does not establish native Lean source parsing, inductive-command
elaboration, pattern/equation
compilation, structural or well-founded recursion elaboration, termination
checking, broad `Init`/`Std`/mathlib admission, full Lean-kernel parity, or a
replacement for official Lean.

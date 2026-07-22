# Official Lean construct-matrix execution plan

Status: complete for the preregistered selected-family measurement population;
TL1.8 and TL2.16 remain PARTIAL for their broader populations

Date: 2026-07-22

Decision:
[accepted ADR-0351](../research/09-decisions/adr-0351-preregister-official-lean-construct-matrix.md)

Parent plans:

- [Lean system implementation plan](lean-system-implementation-plan-2026-07-21.md)
  (TL1.8, TL2.11--TL2.16);
- [Lean system compatibility roadmap](lean-system-compatibility-roadmap-2026-07-21.md);
- [Rust `lean4export` importer result](lean4export-rust-import-prototype-2026-07-21.md).

Current checkpoints:
[M0 and Stage A result](lean-official-construct-matrix-stage-a-2026-07-22.md)
and [Stage B result](lean-official-construct-matrix-stage-b-2026-07-22.md),
followed by the
[M3 current-product result](lean-official-construct-matrix-product-2026-07-22.md),
the [M4 assurance result](lean-official-construct-matrix-m4-2026-07-22.md), and
the [M5 final result](lean-official-construct-matrix-final-2026-07-22.md),
with the canonical source/wire registration in
[`lean-official-construct-matrix-v1.json`](lean-official-construct-matrix-v1.json).
The registration includes exact typed current-product outcomes and regenerates
the public assurance matrix without changing them. M5 closes the final bounded
gates, accepts the decision, and hands the primary semantic trajectory to
TL2.11 strict positivity.

## 1. Decision and outcome

The next Lean milestone is a **measurement artifact**, not an admission
implementation. Generate official Lean 4.30 exports for the recursive-indexed,
reflexive/higher-order, mutual, nested, and well-founded source families; pair
every unsupported row with the already-admitted direct-recursive control; then
publish a generated assurance-separated matrix showing what official Lean
accepted, what the exporter actually emitted, what the independent Python
reader observed, and where the Rust importer stopped.

This milestone advances TL1.8 and seeds TL2.16. It does **not** complete
TL2.11, TL2.12, TL2.13, TL2.14, or the full TL2.16 construct/root matrix. In
particular, no importer or kernel behavior may be broadened merely to make a
matrix row green.

The immediate output is a reliable map for the next trusted-kernel work:

```text
official source
  -> pinned official elaboration and checking
  -> pinned official core export
  -> independent wire inventory
  -> current Rust parse/translation/admission outcome
  -> stable first blocker and no-overclaim matrix
```

## 2. Why this comes next

The current exact official profile already has:

- flat inductives and declarations: dual-admitted;
- direct-recursive and parametric-recursive non-indexed inductives:
  dual-admitted;
- projections and Nat literals: dual-admitted on their exact selected roots;
- transactional whole-stream publication, a 226-case deterministic mutation
  corpus, and canonical declaration/dependency identities.

The next semantic tasks depend on facts that are still guessed rather than
measured:

- whether a minimal Vector-shaped source reaches the kernel's existing
  `RecursiveIndexedNotSupported` boundary;
- which accepted higher-order source shape official Lean marks
  `isReflexive=true`;
- the exact group/recursor layout for a minimal mutual family;
- how nested source syntax appears in the exported core group;
- what dependency closure and core declarations a minimal well-founded
  definition actually exports.

Implementing positivity, recursive-indexed recursors, or mutual motives before
freezing those forms would optimize against assumptions. This matrix removes
that uncertainty without widening the trusted surface.

## 3. Non-negotiable separations

### 3.1 Source family is not wire construct

“Nested” and “well-founded” name source-language mechanisms. Lean may elaborate
or lower them into mutual, reflexive, auxiliary, or ordinary core declarations.
The matrix therefore carries separate fields for:

- `source_family`;
- `official_source_accepted`;
- `wire_features` observed in the official export;
- `rust_parse`;
- `rust_translate`;
- `rust_admit`;
- `first_outcome`;
- `official_computation` and `axeyum_computation`, when applicable.

No source label grants a core-feature claim, and no parsed record grants
independent-admission credit.

### 3.2 Official acceptance is not independent checking

Official Lean compilation proves that the source is accepted by the pinned
official implementation. It does not prove that Axeyum checked it. A row is
`dual-admitted` only if:

1. pinned official Lean accepts the source;
2. the exact official export is independently admitted by Axeyum;
3. selected computations agree when the row has a computation witness; and
4. the required malformed/false control rejects.

### 3.3 Stable decline is a successful matrix result

For unsupported rows, success means exact official provenance, deterministic
bytes, independent inventory agreement, a typed stable first decline, and zero
published environment. It does not mean changing the importer to accept the
row.

### 3.4 Positivity remains a prerequisite

Official Lean will reject genuinely non-positive source declarations before an
export exists. The construct matrix may retain that official rejection as a
source negative, but it does not satisfy TL2.11. TL2.11 must separately enforce
and fuzz strict positivity inside the independent kernel before recursive
admission widens.

## 4. Frozen case families

The exact source spelling is frozen in phase M1 before product measurement. The
following semantic case set is fixed now. Renaming for Lean module hygiene does
not change the case set.

| Case ID | Source family | Required shape | Role | Pre-measurement hypothesis |
|---|---|---|---|---|
| `direct-recursive-control` | direct recursive, non-indexed | existing `MiniNat` plus parametric `MiniList` fixture | positive control beside every negative | exact existing stream remains dual-admitted with 11 declarations and zero axioms |
| `recursive-indexed` | Vector-shaped family | one explicit index family; a base constructor and a recursive constructor whose recursive field changes the index | measures recursion plus indices | official export is accepted; current Rust reaches a typed recursive-indexed kernel decline |
| `reflexive-higher-order` | Acc-shaped family | recursive occurrence beneath a constructor function field, with explicit relation/index parameters | measures `isReflexive` and higher-order induction hypotheses | official export is accepted and reports a reflexive core group; current Rust declines before admission |
| `mutual` | two-family mutually recursive tree | two inductive types, cross-family recursive fields, and at least one base constructor | measures multi-motive group/recursor shape | official export contains one group with two types; current Rust returns `inductive-mutual` |
| `nested` | rose-tree-shaped nested recursion | recursive occurrence under a separately declared list-like type former | measures official nested lowering and `numNested`/auxiliary declarations | official export is accepted; exact wire classification is deliberately not guessed |
| `well-founded` | terminating non-structural definition | one small function accepted only with an explicit well-founded/termination argument and one concrete computation witness | measures elaborator-produced closure rather than inventing a wire category | official export is accepted; exact dependency/core blocker is deliberately not guessed |
| `non-positive-source-negative` | invalid inductive source | one recursive occurrence in a negative position | official source-side teeth control | pinned official Lean rejects and no NDJSON artifact is assigned |

The recursive-indexed row must use a custom small index family where practical,
not import the whole standard `Vector` closure. The reflexive row should mirror
the pinned `Init.WF.Acc` constructor shape while remaining namespaced and
minimal. The well-founded witness must be small enough for two bounded official
runs and must not depend on an unpinned tactic package.

## 5. Two-stage preregistration

The official elaborator is part of what is being measured, so exact wire
expectations cannot honestly be frozen before seeing its output. Use two stages
without looking at the Axeyum result between them.

### Stage A — freeze source cases

Before exporting:

1. commit the Lean source fixture;
2. freeze each case ID, selected declaration root, intended source family, and
   computation witness;
3. compile every positive source and confirm the negative source fails;
4. record pinned Lean/exporter commits and the exact commands;
5. do not run the Rust importer on any new stream yet.

Source edits after Stage A require a new source hash and an explicit plan/ADR
amendment. Failed syntax or elaboration may be corrected before the Stage A
commit; it is development, not a result.

### Stage B — freeze official wire observations

After Stage A, but still before the Rust importer sees the streams:

1. export every selected root twice;
2. require byte-identical outputs;
3. run only the independent Python reader/census;
4. freeze exact stream hash, bytes, records, N/L/E/D counts, group metadata,
   `numIndices`, `numNested`, `isRec`, `isReflexive`, motives, minors, and
   dependency roots in the registration;
5. classify source family and observed wire features separately;
6. commit the Stage B registration.

Only then run the Rust importer. An outcome that contradicts the hypothesis is
reported; it is not “fixed” by changing the frozen fixture.

## 6. Planned artifacts

### 6.1 Exact inputs

- `docs/plan/fixtures/lean4export-v4.30-construct-matrix.lean` — the frozen
  positive source cases and computation witnesses;
- `docs/plan/fixtures/lean4export-v4.30-construct-matrix-negative.lean` — the
  official non-positive rejection control;
- one target-specific `.ndjson` file per positive case, named by case ID, so a
  broad dependency closure cannot hide the first blocker of a smaller row;
- the existing
  `docs/plan/fixtures/lean4export-v4.30-recursive-shapes.ndjson` as the immutable
  direct-recursive control.

Every retained stream is the exact stdout bytes from the exporter. Do not
pretty-print, reorder, normalize, or concatenate records.

### 6.2 Registration and generated result

- `docs/plan/lean-official-construct-matrix-v1.json` — canonical registration
  and measured data;
- `docs/plan/generated/lean-official-construct-matrix.md` — generated public
  matrix;
- `scripts/check-lean-official-construct-matrix.py` — fail-closed validator and
  renderer;
- focused Python tests for hash/count/feature drift and false credit;
- `crates/axeyum-lean-import/tests/official_construct_matrix.rs` — exact Rust
  outcomes, direct-recursive pairings, repeatability, and transactional failure.

The JSON is the machine-readable source of truth. The Markdown is regenerated,
not hand-edited. Rust outcome rows must identify the exact `ImportError` variant
and payload; stringified `Debug` output is not a stable gate.

### 6.3 Retention boundary

Commit a new stream only if it is at most 1 MiB and the complete new matrix
fixture set remains at most 2 MiB. If a row exceeds either bound:

- retain source, command, exact byte/record counts, and SHA-256;
- give it source/export inventory credit only;
- do not give it normal exact-fixture or Rust regression credit until TL1.9
  provides the content-addressed artifact path;
- do not silently raise the threshold after seeing the row.

## 7. Execution phases

### M0 — environment and baseline verification

1. Verify the repository toolchain pin and current branch/remote identity.
2. Verify Lean 4.30.0 commit
   `d024af099ca4bf2c86f649261ebf59565dc8c622`.
3. Verify `lean4export` v4.30.0 commit
   `a3e35a584f59b390667db7269cd37fca8575e4bf` and format 3.1.0.
4. Regenerate the existing flat and direct-recursive streams byte-for-byte.
5. Re-run the current importer baseline before adding matrix expectations.

Exit: both historical fixture hashes and current admission reports are
unchanged. Any drift stops the matrix until provenance is repaired.

### M1 — author and freeze official source cases

1. Use one namespaced module with independent declarations where possible.
2. Keep roots minimal and target them separately with `lean4export -- ROOT`.
3. Add one closed computation witness per positive family where official
   reduction is meaningful.
4. Compile with pinned Lean using one worker under the hard memory wrapper.
5. Confirm the non-positive source fails for the intended reason.
6. Commit the source fixture and Stage A registration before producing any new
   NDJSON stream.

Exit: every positive source compiles, the negative source fails, roots and
source hashes are frozen, and no new Rust result has been observed.

### M2 — reproduce and freeze official exports

1. Export each root twice from clean transient `.olean` inputs.
2. Compare exact bytes and SHA-256.
3. Run the independent Python format/topology/feature inventory.
4. Record source-to-wire lowering explicitly, especially nested and
   well-founded rows.
5. Apply the retention boundary.
6. Commit Stage B wire observations before product measurement.

Exit: every retained stream is byte-identical across two runs and every row has
an exact official provenance record. A nondeterministic row receives no fixture
credit.

### M3 — measure the current Rust boundary

1. Import the direct-recursive control before each unsupported case.
2. Require its exact 11-declaration, zero-axiom pass each time.
3. Import every new retained stream twice.
4. Match exact typed outcomes:
   - `ImportError::Unsupported { code, .. }` for importer policy boundaries;
   - `ImportError::Kernel { source, .. }` for independent kernel boundaries;
   - success only when a completed owned environment is returned.
5. On every failure, prove no `CompletedImport` or partial kernel is exposed.
6. If any row unexpectedly admits, stop credit until official/Axeyum
   computation and malformed-control gates are designed and pass.

Exit: Python and Rust inventories agree on the exact stream population; every
current failure has a stable first outcome and completion-only publication
holds.

### M4 — generate the assurance matrix

Generate one row per case with at least:

- tool/source/stream identities;
- selected root and source family;
- official source acceptance;
- official computation result, if present;
- stream bytes/records and N/L/E/D counts;
- observed wire features and inductive metadata;
- Python parsed/inventoried result;
- Rust parsed, translated, admitted, and computed states;
- exact first outcome;
- direct-recursive control identity;
- axiom and declaration/dependency identity counts when import succeeds;
- assurance class and explicit non-claims.

Allowed assurance classes are:

- `official-source-rejected`;
- `official-export-inventory-only`;
- `parsed-declined`;
- `translated-kernel-declined`;
- `independently-admitted`;
- `dual-admitted-computation-checked`.

The generator must reject impossible promotions, such as `dual-admitted` with
no independent admission or `independently-admitted` after any decline.

### M5 — validation, documentation, and handoff

Required bounded gates:

1. exact source/stream hashes and two-run reproduction;
2. independent Python tests;
3. focused Rust matrix tests plus all existing importer tests;
4. warning-denied Clippy and rustdoc for the importer/kernel slice;
5. compile-fail publication doctest;
6. compatibility/axiom-ledger/parity-document checks;
7. foundational resources and documentation links;
8. focused formatting and diff hygiene;
9. explicit recording of unrelated pre-existing workspace failures rather than
   claiming a clean whole workspace.

Update PLAN, STATUS, both Lean roadmaps, the docs index, and the final result
document. Add/commit/push after Stage A, Stage B, product measurement/tooling,
and final documentation rather than carrying the full milestone uncommitted.

## 8. Resource and reproducibility policy

- all Lean compilation/export and Rust build/test commands run under a hard
  4 GiB memory cap; for Lean 4.30 this milestone uses a cgroup
  (`MemoryMax=4G`) rather than `ulimit -v`, because an address-space cap aborts
  the runtime during thread creation even at one worker;
- Lean uses one worker; Rust uses at most two jobs;
- no broad `Init`, `Std`, or mathlib export is part of this milestone;
- transient modules and `.olean` files live outside the repository or in an
  ignored scratch directory and are removed after hashing;
- no network access is needed once the already-pinned toolchain/exporter are
  verified;
- exporter stdout is captured directly; diagnostics go elsewhere;
- exact commands and environment variables are stored in the registration;
- every committed stage ends with local HEAD, tracking ref, and remote ref
  equality checks.

## 9. Stop conditions

Stop and document rather than improvising when:

1. a positive source does not compile under pinned Lean;
2. the negative source compiles;
3. two exporter runs differ;
4. the source family lowers to a different wire family than expected;
5. Python and Rust disagree on stream population or topology;
6. the importer panics, exceeds its declared limits, or exposes partial state;
7. a currently unsupported row unexpectedly admits;
8. a fixture crosses the retention boundary;
9. a test requires more than 4 GiB or broad unbounded parallelism;
10. unrelated dirty files overlap a target path.

Cases 4 and 7 are scientifically useful observations. They trigger an explicit
registration/result amendment and soundness review, not a source rewrite to
recover the hypothesis.

## 10. Completion criteria

This matrix milestone is complete only when:

1. all six positive/control families and the source-negative case have frozen
   source identities;
2. every retained positive stream reproduces byte-for-byte twice;
3. every retained stream has exact official and independent Python inventory;
4. the direct-recursive control passes beside every Rust decline;
5. every Rust outcome is typed, repeated, and completion-only;
6. source family and observed wire construct remain separate fields;
7. the generated matrix cannot promote parser/exporter evidence into checker
   credit;
8. all bounded gates pass or pre-existing failures are named precisely;
9. PLAN/STATUS/roadmaps state the measured result and next task without a parity
   overclaim;
10. all intended files are added, committed, pushed, and local/tracking/remote
    refs agree.

At completion, mark TL1.8 **PARTIAL with expanded exact coverage** and TL2.16
**PARTIAL with a generated selected construct matrix**. Do not mark either
phase DONE until their full stated populations are covered.

## 11. Trajectory after the matrix

The primary trusted-kernel sequence remains:

1. **TL2.11 strict positivity** — preregister and fuzz rejection before any
   recursive admission widening;
2. **TL2.12 recursive-indexed and reflexive/higher-order induction
   hypotheses** — implement against the now-frozen official forms;
3. **TL2.13 mutual inductive groups** — multiple motives/shared minors;
4. **TL3.1--TL3.3 prelude export, ledger classification, and namespace-safe
   composition** may proceed before the XL frontend task;
5. **TL2.14 nested/well-founded native frontend lowering** only after TL2.13
   and TL4.12 supply its declared dependencies.

TL1.5 property fuzzing is dependency-ready and remains a bounded independent
importer-hardening lane. It must not displace TL2.11 as the prerequisite for
semantic recursive admission, and it must reuse rather than duplicate the
matrix fixtures and TL1.4 mutation vocabulary.

## 12. Explicit non-claims

This plan and its eventual matrix do not establish:

- full Lean kernel parity;
- native Lean parsing, elaboration, tactics, modules, Lake, LSP, compiler, or
  `.olean` compatibility;
- `Init`, `Std`, or mathlib import coverage;
- positivity enforcement merely because official Lean rejected one source;
- recursive-indexed, reflexive, mutual, nested, or well-founded independent
  admission merely because their official sources export;
- authenticated producer completion for format 3.1 streams, which have no
  footer;
- any performance result.

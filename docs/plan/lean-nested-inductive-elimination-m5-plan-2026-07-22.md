# Lean nested-inductive elimination M5: computation and assurance plan

Date: 2026-07-22

Status: preregistered by the pushed commit containing this document; no M5
Axeyum normal-form assertion may predate that checkpoint

Parent:
[TL2.14 P0--M6 plan](lean-nested-inductive-elimination-tl2.14-plan-2026-07-22.md)

Importer prerequisite:
[M4 exact official import](lean-nested-inductive-elimination-m4-2026-07-22.md)

Machine authority:
[M0 source/wire registration](lean-nested-inductive-elimination-v1.json)

Decision gate:
[proposed ADR-0355](../research/09-decisions/adr-0355-preregister-lean-nested-inductive-elimination.md)

Baseline documentation checkpoint: `5d3e83338a42b1f49807c00aeaff9ae5e413907e`

Importer semantic checkpoint: `f03dfcdf2b3e49d86a5bb9ad00aeef20c99926ee`

## Boundary and ownership

M5 adds explicit computation evidence for the three M0-selected nested theorem
roots, then appends the corresponding current assurance overlay. Declaration
import by itself is not computation credit.

The implementation/evidence lane owns exactly:

- `crates/axeyum-lean-import/tests/official_nested_inductive_groups.rs` for
  theorem extraction, proof inference, equality-side checks, and exact
  registered normal forms;
- `docs/plan/lean-official-construct-matrix-v1.json` for one append-only
  `tl2_14_update` block;
- `scripts/check-lean-official-construct-matrix.py` and
  `scripts/tests/test_lean_official_construct_matrix.py` for exact TL2.14
  overlay validation and fail-closed mutations;
- `scripts/check-lean-nested-inductive-elimination.py`,
  `scripts/check-lean-mutual-inductive-groups.py`, and
  `scripts/check-lean-strict-positivity-m3.py`, with their existing tests, only
  as needed to strip the later TL2.14 overlay from historical hash views while
  requiring the current overlay to exist;
- `docs/plan/lean-compatibility-v1.json`,
  `docs/plan/generated/lean-compatibility.md`, and
  `scripts/tests/test_lean_compatibility.py` to remove only the obsolete live
  `inductive-nested` decline after computation succeeds; and
- `docs/plan/generated/lean-official-construct-matrix.md` plus the M5 result
  and live planning reconciliation.

The historical checker test ownership is exact:

- `scripts/tests/test_lean_nested_inductive_elimination.py`;
- `scripts/tests/test_lean_mutual_inductive_groups.py`; and
- `scripts/tests/test_lean_strict_positivity_m3.py`.

The result/live-document checkpoint owns exactly
`docs/plan/lean-nested-inductive-elimination-m5-2026-07-22.md`,
`docs/plan/README.md`, the parent TL2.14 plan, the resume handoff, `PLAN.md`,
and `STATUS.md`. M6 owns ADR disposition and complete project-state, roadmap,
research-question, P6.0, and decisions-index reconciliation.

M5 does not change kernel or importer semantics, fixture/source/stream bytes,
declaration identity, M0 registration, historical Stage B/product/TL2.12/TL2.13
blocks, ADR status, or TL4.9/TL4.10 source-elaboration ownership. ADR-0355 and
TL2.14 remain open for M6 final closure.

## Independent source confirmation

Compile the unchanged M0 source
[`lean-v4.30-nested-inductive-computation.lean`](fixtures/lean-v4.30-nested-inductive-computation.lean)
twice with the exact executable
`/home/mjbommar/.cache/axeyum-lean-gate-v430-audit/elan-home/toolchains/leanprover--lean4---v4.30.0/bin/lean`,
`-j1`, and the registered `systemd-run --user --scope` limits:

- `MemoryHigh=3G`;
- `MemoryMax=4G`;
- `MemorySwapMax=512M`; and
- separate repository-local output directories.

For repetitions 1 and 2, the argv after the resource runner is exactly:

```text
/usr/bin/time -v /home/mjbommar/.cache/axeyum-lean-gate-v430-audit/elan-home/toolchains/leanprover--lean4---v4.30.0/bin/lean -j1 -o target/tl214-m5-run<1|2>/AxeyumNestedInductiveComputation.olean docs/plan/fixtures/lean-v4.30-nested-inductive-computation.lean
```

Both runs must exit zero and produce the already-frozen OLEAN SHA-256
`d7d03cb863626f1ddc2a80b0dee3ae19fbc001dc2fb4ac60f6b9e27c7b7f53c2`.
Record elapsed milliseconds and maximum RSS separately. Do not regenerate or
rewrite any retained NDJSON stream.

## Exact Axeyum computation contract

Extend the existing twice-imported M4 test. For each selected theorem:

1. retrieve the exact exported `Declaration::Theorem` by qualified name;
2. infer the proof value and require definitional equality with its type;
3. decompose the type as `Eq <type> <lhs> <rhs>`;
4. require `<lhs>` and `<rhs>` to be definitionally equal;
5. require `<rhs>` to be definitionally equal to the registered constructor
   normal form; and
6. recursively WHNF-normalize application spines and compare the normalized
   left side with the normalized registered constructor term.

The exact selected population is:

| ID | theorem | required normal form | report N/L/E/D/admitted/axioms |
|---|---|---|---:|
| `auxiliary-recursion-computation` | `AxeyumNestedInductiveComputation.roseAuxiliaryRecursorComputes` | `MiniNat.succ (MiniNat.succ (MiniNat.succ MiniNat.zero))` | 122/8/494/17/34/0 |
| `indexed-container-computation` | `AxeyumNestedInductiveComputation.indexedAuxiliaryRecursorComputes` | `MiniNat.succ (MiniNat.succ (MiniNat.succ MiniNat.zero))` | 134/8/554/17/34/0 |
| `repeated-container-reuse-computation` | `AxeyumNestedInductiveComputation.repeatedContainerReusesAuxiliaryRecursor` | `MiniNat.succ (MiniNat.succ (MiniNat.succ (MiniNat.succ (MiniNat.succ MiniNat.zero))))` | 122/8/518/17/34/0 |

All three computations run twice. The construct row remains admission-only and
the complete M4 mutation/order/nonpublication suite remains unchanged.
Every completed report must retain zero axioms, zero axiom identities, and one
declaration identity per admitted declaration.
Rename the existing Rust-only case label `repeated-container-computation` to
the registered ID `repeated-container-reuse-computation`; no alias may enter
the machine overlay.

The immutable stream bindings and registered transitions are:

- auxiliary recursion: SHA-256
  `36fb9c6f85a99a7d6d1f6329a2cfe5265b148f0138e979d6d391d9e8879e07de`,
  36,706 bytes / 642 records,
  `Rose.rec -> Rose.rec_1 -> Rose.rec -> Rose.rec_1`;
- indexed container: SHA-256
  `a14ca423410c4f0a86c2a2cea193e5a76bd91428e348402b3dd32e1603481429`,
  40,119 bytes / 714 records,
  `IndexedRose.rec -> IndexedRose.rec_1 -> IndexedRose.rec -> IndexedRose.rec_1`;
  and
- repeated-container reuse: SHA-256
  `af369edb2d9e0346a5457ba4c9cde6f3030ca08002dc931c5fb26709e0f74344`,
  37,771 bytes / 666 records,
  `RepeatRose.rec -> one reused RepeatRose.rec_1 -> RepeatRose.rec on both heads`.

## Append-only assurance overlay

After the computation test is green and its semantic checkpoint is pushed,
append `tl2_14_update` after `tl2_13_update` in the current construct-matrix
registration. Bind:

- the pushed computation-test revision and exact test path;
- two pinned-Lean source runs and their one frozen OLEAN digest;
- two Rust runs per selected computation under one build job/test thread;
- the nested construct outcome at 70/6/322/10, 22 declarations, zero axioms,
  and 22 declaration identities;
- the three exact fixture hashes, byte/record counts, selected theorems, normal
  forms, and 34-declaration/zero-axiom reports; and
- measured Lean and Rust elapsed/RSS values.

The `tl2_14_update` keys are ordered exactly as
`measured_date`, `source_revision`, `product_test`, `runs_per_case`,
`resource_runner`, `memory_max`, `rust_jobs`, `rust_test_threads`, `lean_jobs`,
`lean_source_runs`, `lean_olean_sha256`, `lean_elapsed_ms`,
`lean_max_rss_kib`, `rust_gate_elapsed_ms`, `rust_gate_max_rss_kib`, `outcomes`,
and `computations`. Its one outcome is `nested`. Its computation keys are
ordered `auxiliary-recursion-computation`, `indexed-container-computation`,
and `repeated-container-reuse-computation`. Each computation object retains
the existing TL2.12/TL2.13 field order: `path`, `sha256`, `bytes`, `records`,
`runs`, `completed`, `reduction_checked`, `theorem`, `normal_form`, `report`.
The outcome field order is `variant`, `runs`, `report`, `line`, `code`,
`message`; report order is `names`, `levels`, `expressions`,
`declaration_records`, `admitted_declarations`, `axioms`, `axiom_identities`,
`declaration_identities`.

The current seven-row generated matrix must then report six independently
admitted rows, four computation-checked rows, zero current declines, and the
one official-source negative. The nested row becomes
`dual-admitted-computation-checked`; its boundary names all three companion
computation streams and normal forms. Remove the stale current
`misclassified as malformed` rendering and assertion. No historical blocker
inventory is rewritten. Exact assurance-class counts are four
`dual-admitted-computation-checked`, two `independently-admitted`, and one
`official-source-rejected`.

The checker must reject at least these independently addressable drift classes:

1. missing/extra TL2.14 overlay fields;
2. source revision or product-test path drift;
3. run/resource/pin/measurement-shape drift;
4. nested construct outcome/report drift;
5. computation population or order drift;
6. fixture path, hash, byte, or record drift;
7. theorem-name drift;
8. normal-form drift;
9. completed/reduction-checked/run-count drift;
10. impossible assurance-class promotion or demotion;
11. rewritten historical M0/TL2.12/TL2.13 bytes; and
12. historical hash views that accidentally include the TL2.14 overlay.

Historical views are explicit: the mutual M0 checker removes `tl2_13_update`
and `tl2_14_update`; the strict-positivity M3 checker removes those same two
overlays while requiring current TL2.12/TL2.13/TL2.14 presence; and the nested
M0 checker continues removing only `tl2_14_update` while now requiring that
the current overlay exists. The recursive-IH checker and frozen Stage B/product
blocks require no edit.

## Live decline transition

The intermediate M4 branch is intentionally not merge-ready because the live
compatibility registry still points `inductive-nested` at an importer marker
that M4 truthfully removed. Do not relocate that marker to a historical file
or add a dead source literal.

Only after all three Axeyum computations and the append-only overlay validate:

1. remove the single `inductive-nested` decline-code object from
   `lean-compatibility-v1.json`;
2. regenerate `generated/lean-compatibility.md`;
3. require the compatibility test to assert that the code is absent; and
4. run the generator/checker suite until the aggregate branch is green.

The other five live decline codes remain exact. If any computation or overlay
gate fails, retain the nested decline, record the blocker, and stop before an
assurance promotion.

## Required gates

- pinned Lean source compile twice with equal frozen OLEAN digest;
- one focused nested importer test invocation in which each selected
  computation imports and reduces twice;
- complete M4 nested import/mutation/order tests;
- complete importer and kernel suites;
- exact 640 nested plus retained 720 mutual, 768 recursive-IH, and 840
  positivity populations;
- well-founded 35-declaration/zero-axiom control twice;
- warning-denied importer Clippy and rustdoc;
- direct `rustfmt --edition 2024 --check` on the owned Rust test, never
  workspace `cargo fmt`;
- M0 nested, TL2.12, TL2.13, strict-positivity, construct-matrix, and
  compatibility checkers and unit tests;
- generated documents, parity docs, foundational resources, links, shell
  syntax, and `git diff --check`; and
- pathspec-only commits, push, and local/tracking/remote equality.

## Checkpoint sequence

1. commit and push this M5 plan before the first new normal-form assertion;
2. implement, audit, test, commit, and push the Rust computation checkpoint;
3. rerun pinned Lean and record measurements;
4. append and validate the assurance overlay, then remove the obsolete live
   decline and regenerate both current documents;
5. commit/push M5 evidence and reconcile the resume handoff to M6.

Any need for a kernel/importer semantic change, fixture rewrite, identity
change, broader normalizer, source-elaboration claim, or historical evidence
rewrite is a stop-and-review event.

Stop before assurance promotion if either pinned-Lean output digest differs,
the two digests differ from each other, either compile fails or exceeds the
resource envelope, any selected root/identity drifts, any theorem is absent or
not an inferred `Eq` proof, any side/normal-form check fails, any report,
axiom/identity count, or fixture binding drifts, a broader normalizer or product
semantic change is required, a historical hash cannot be preserved by
excluding only the registered TL2.14 overlay, the pre-transition compatibility
failure differs from the one known stale marker, the compatibility registry
would need a substitute marker, the aggregate remains red after truthful
decline removal/regeneration, or any retained control regresses.

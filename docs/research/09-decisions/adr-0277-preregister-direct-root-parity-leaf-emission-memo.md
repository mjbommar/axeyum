# ADR-0277: Preregister direct-root parity-leaf emission memo

Status: accepted
Date: 2026-07-19

Result state: exact structural gate passed; performance gate rejected; candidate
removed from production

## Context

ADR-0276 partitions all 107,000 parity/parity duplicate attempts on the fixed
corrected-wide-v3 population into one cell: the first and later clauses come
from the same leaf of the same owner, and both leaf shapes are
`a2-f0-t0-d2-r0-x0`. There are no repeated or complementary inputs and no
cross-leaf or cross-owner overlap. ADR-0261's normalized duplicate-leaf removal
therefore remains rejected; the opportunity is repeated *emission of one
logical leaf*, not multiple equivalent leaves.

A positive direct root is encoded with constant-true output. A two-input parity
leaf emits exactly two binary clauses. Reasserting that same direct root visits
the same owner/leaf again and the global clause index rejects its two clauses.
The measured cell authorizes a narrower producer-side memo that avoids only
those later visits.

## Decision

Add one encoder-local deterministic set keyed by `(owner AIG node, leaf index)`.
Consult it only when all of the following are true:

- emission phase is `root`;
- the direct root is positive and its output is `Const(true)`;
- the AND-tree leaf is `Parity`; and
- forward implication encoding is selected.

The first visit inserts the key and emits the leaf normally. A later visit to
the same key returns before truth-table clause generation. Do not memoize
ordinary literals, not-AND leaves, non-root gates, negative roots, reverse
directions, different owners, or different leaf indices. Do not change AIG
planning, helper skipping, variable allocation, the global collision-safe
clause index, or root/lift maps.

This is a generator memo, not an IR rewrite or parity simplifier. The key uses
structural identity already fixed by the encoder plan; it does not compare or
normalize semantic leaf contents.

## Tests and exact structural gate

Tests must begin red and then prove:

- repeated assertions of one positive direct root emit each parity leaf once;
- distinct leaf indices and distinct owners remain distinct;
- negative roots, non-root parity gates, and non-parity leaves are unchanged;
- a single visit still emits the exact two-clause parity truth table;
- ordinary and candidate encoders produce byte-identical DIMACS, roots,
  variable bindings, verdicts, and lifted original-term replay; and
- the memo is encoder-local and deterministic.

Commit implementation and tests before reading the fixed corpus through the
candidate. One clean detached profiled run must preserve the exact ADR-0276
population, decisions, manifest/Z3 agreement, 88 SAT replays, AIG nodes, CNF
variables, emitted clauses, and every nonselected origin row. Relative to the
accepted ADR-0276 artifact, it must produce exactly these aggregates:

| Counter | Baseline | Required candidate | Required delta |
|---|---:|---:|---:|
| Clause attempts | 396,270 | 289,270 | -107,000 |
| Exact duplicates | 119,260 | 12,260 | -107,000 |
| Declared/visited literals | 1,085,685 | 764,685 | -321,000 |
| False constants dropped | 186,123 | 79,123 | -107,000 |
| Canonical attempted literals | 894,543 | 680,543 | -214,000 |
| Canonical binary attempts | 255,330 | 148,330 | -107,000 |
| Primary occupied/exact hits | 119,260 | 12,260 | -107,000 |
| Emitted clauses | 271,991 | 271,991 | 0 |

The parity-overlap population must become exactly zero. Tautology causes,
primary vacant probes, collision work, nonbinary length buckets, and every
non-parity origin cell must remain byte-for-structure identical. Any different
delta rejects the candidate and forbids timing.

## Implementation boundary

Candidate commit `9533c508` adds one `BTreeSet<(AigNodeId, usize)>` to the
one-shot encoder. `should_emit_parity_leaf` returns early only for a later
root-phase, constant-true-output visit with the same owner and leaf index. Gate
phase, constant-false output, different owner, and different leaf-index calls
do not share or populate the memo.

The repeated-equality-root test began red at 12 clause attempts versus the
single-root requirement of 4. It now preserves byte-identical CNF and variable
bindings, all three root records, the single-root attempt count, and zero
parity-overlap duplicates. A second focused test exercises every registered
scope distinction directly.

Pre-observation gates pass:

- all 309 `axeyum-cnf` library tests;
- all 21 focused `axeyum-solver` library tests;
- all 44 `axeyum-bench` binary tests;
- strict all-target/all-feature Clippy and warnings-as-errors rustdoc for the
  three affected crates;
- `axeyum-solver`'s no-default `qfbv` check and `axeyum-bench`'s no-default
  check; and
- the documentation link checker and clean-diff gate.

No corrected-wide-v3 query has been run through the candidate. The next action
is exactly one clean detached profiled structural run, not timing.

## Observed structural result

The clean detached artifact-v37 run at `900f6997` passes all 162 decision,
manifest/Z3, 88 SAT replay, family, and per-query structure gates. The
independent analyzer frozen at `13ca0d2b` compares the accepted ADR-0276
artifact and reports every registered delta exactly:

- clause attempts and duplicates: -107,000 each;
- declared and visited literals: -321,000 each;
- false constants: -107,000;
- canonical literals: -214,000;
- canonical binary attempts and primary occupied/exact probes: -107,000 each;
- emitted clauses, every other construction counter, and every nonselected
  origin row: unchanged; and
- parity overlap: exactly zero, leaving 12,260 other duplicates.

The retained structural
[`artifact.json`](../../../bench-results/glaurung-direct-root-parity-memo-20260719/artifact.json)
has SHA-256 `14b42944...60ee`; its
[`analysis.json`](../../../bench-results/glaurung-direct-root-parity-memo-20260719/analysis.json)
has SHA-256 `71830237...91bd`. This exact pass authorized the conditional timing
protocol and no broader change.

## Conditional unprofiled performance protocol

Only after the exact structural gate passes, compare baseline source
`6ff05905` with the committed candidate using production unprofiled encoders.
Prebuild both release executables, then run six order-balanced pairs in the
fixed sequence `B,C,C,B,B,C,C,B,B,C,C,B` over the unchanged 162-query corpus.
Use raw rewrite-off `sat-bv`, in-process Z3, one job, and ADR-0276's exact
deterministic limits; omit `--profile-cnf-construction`.

Fail closed unless every process preserves 162/162 decisions, manifest/Z3
agreement, all 88 original-model replays, and identical per-query outcomes,
AIG nodes, CNF variables, and emitted clauses. Config, environment, corpus,
linkage, and order identities must match except for registered source/binary
identity.

For each process sum per-query Axeyum `cold_total_ms`. Accept only if:

- the six candidate/baseline ratios have geometric mean at most `0.97` and a
  deterministic paired-bootstrap 95% upper bound below `1.0`;
- neither baseline nor candidate run-total CV exceeds 3%; and
- no family-level paired geometric mean exceeds `1.02`.

Retain and reject any correctness, structural, identity, variance, aggregate,
or family failure. Do not tune thresholds, broaden memo scope, combine smaller
origin cells, or use profiled time as performance evidence.

## Observed performance result

Distinct frozen baseline/candidate executables were run in the exact 12-process
order. All processes preserve 162/162 decisions, manifest/Z3 agreement, 88 SAT
replays, and per-query AIG/CNF/emitted-clause structure. The paired candidate /
baseline ratios are `0.92203, 0.94796, 1.01559, 0.93189, 0.98175, 0.96439`.

The aggregate speed gates pass: geometric mean `0.96009` and exhaustive
deterministic bootstrap 95% upper bound `0.98146`. Acceptance still fails:

- baseline CV is 3.4250%, above 3%;
- candidate CV is 3.0152%, above 3%; and
- mixed and trivial family geomeans are 1.04918 and 1.32691, above 1.02.

The remaining family geomeans are arithmetic 0.94914, comparison 0.87996,
register-slice 0.99655, and slice-partial 0.92897. The trivial row's tiny
absolute duration does not permit post-observation relaxation of the
unconditional family gate.

The retained
[`timing-analysis.json`](../../../bench-results/glaurung-direct-root-parity-memo-20260719/timing-analysis.json)
has SHA-256 `7a68f696...4816`; all twelve raw artifacts are retained beside it.
Candidate code and its candidate-only regressions were removed at `4fc45767`.

## Consequences

ADR-0277 was the only production experiment selected by ADR-0276. Its exact
structural mechanism is real, but the full preregistered performance contract
rejects it. Production encoding returns to pre-candidate behavior. Do not rerun
to select a lower-variance sample, weaken the family gate, or reuse the same
107,000-clause population for another post-hoc candidate. The ADR-0259--0277
duplicate-clause lane is closed. Strict sort errors, replay, proof work, warm
retention, concretization policy, and symbolic memory remain unchanged.

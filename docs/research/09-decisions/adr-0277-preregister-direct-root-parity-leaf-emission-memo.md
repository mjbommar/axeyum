# ADR-0277: Preregister direct-root parity-leaf emission memo

Status: accepted
Date: 2026-07-19

Result state: zero-row candidate preregistration; no implementation or timing

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

## Consequences

ADR-0277 is the only production experiment selected by ADR-0276. If its exact
structural gate fails, remove it before timing. If timing fails, remove it while
retaining the negative evidence. Strict sort errors, original-model replay,
proof work, warm retention, Glaurung concretization policy, and symbolic memory
remain unchanged.

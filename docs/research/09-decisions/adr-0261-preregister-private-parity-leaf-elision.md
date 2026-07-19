# ADR-0261: Preregister private parity-leaf elision

Status: accepted
Date: 2026-07-19

Result state: rejected at the fixed structural gate; timing not run

## Context

ADR-0260 attributes 107,000 of 119,260 exact duplicate clause attempts
(89.7199%) to the same positive direct-root AND-tree owner emitting the same
forward parity clause. The cell occurs in 29 queries and its largest query owns
only 9.9738%, so it is the sole cell that passes the preregistered 50% / 10-query
/ 50% rule.

Every selected duplicate is binary. A two-input private parity leaf emits two
clauses, so the cell represents 53,500 redundant parity-leaf encodings. The
global clause index already removes the generated duplicates; the opportunity
is to avoid regenerating them, not to alter the final CNF or replace its index.

## Decision

Implement one bounded candidate in private positive-root AND-tree planning.
Normalize a parity leaf by:

- moving each input-literal inversion into the expected parity bit;
- sorting the remaining positive AIG node literals deterministically; and
- retaining multiplicity rather than introducing a new XOR-cancellation rule.

Within one AND-tree owner, retain the first normalized `(inputs, expected)`
leaf and omit later identical leaves from clause generation. Continue retaining
every occurrence's private helper nodes in the skip plan so no bypassed helper
can be referenced elsewhere. Do not deduplicate ordinary literal leaves,
not-AND leaves, different owners, non-root gates, or merely overlapping parity
clauses.

The candidate is an upstream generator elision, not a semantic rewrite. The
existing clause index remains the final collision-safe guard.

## Correctness and structural gates

Tests must begin red and then prove:

- normalized input order and inversion placement identify equivalent parity
  leaves while distinct expected bits and input multisets remain distinct;
- only later identical parity leaves under the same eligible owner are elided;
- helper-node skipping, root mappings, variable bindings, and SAT replay remain
  valid;
- ordinary and candidate encoders produce byte-identical DIMACS and roots over
  crafted, exhaustive small-width, and seeded wider AIGs; and
- forced fingerprint collisions and non-parity duplicate paths are unchanged.

From a clean candidate commit, one profiled fixed-population verification must
preserve all 162 verdict/oracle/replay gates, every AIG/CNF variable and emitted-
clause count, and reduce exactly:

- clause attempts and duplicate clauses by 107,000 each; and
- canonical attempted literals by 214,000.

No other origin cell may change. A different structural delta rejects the
candidate or requires a new ADR; it is not explained after observation.

## Implementation boundary

Candidate commit `8b95d42a` made private positive-root AND-tree collection perform one deterministic
post-collection pass. For every parity leaf it folds complemented inputs into
the expected bit, replaces them with positive node literals, sorts those
literals, and retains only the first identical `(literals, expected)` key in a
`BTreeSet`. Literal multiplicity is unchanged. The pass is called only when the
owner is a positive direct root; ordinary literal and not-AND leaves are not
keys. `helper_nodes` is never filtered, so every elided occurrence's private
implementation nodes remain in the skip plan.

The focused test began red because the helper did not exist. It now covers
input order, inversion normalization, distinct expected bits, retained
multiplicity, non-parity leaves, and unchanged helper bookkeeping. All 305 CNF
library tests, 880 all-feature solver library tests, 43 all-feature benchmark
binary tests, and strict all-target/all-feature Clippy for all three affected
crates passed before observation. The implementation was committed before the
fixed run and removed from production after rejection.

## Observed result

The clean detached run at
`8b95d42aa264c94c30df14fb9d114a6973b6a62c` passes all 162
decision/manifest/Z3/replay gates and preserves every per-query DAG, AIG, CNF
variable, and emitted-clause count. It changes none of the selected structural
counters:

| Counter | Baseline | Candidate | Required delta | Observed delta |
|---|---:|---:|---:|---:|
| Clause attempts | 396,270 | 396,270 | -107,000 | 0 |
| Exact duplicates | 119,260 | 119,260 | -107,000 | 0 |
| Canonical attempted literals | 894,543 | 894,543 | -214,000 | 0 |
| Emitted clauses | 271,991 | 271,991 | 0 | 0 |

The independent analysis is byte-identical to ADR-0260's accepted analysis.
The retained
[`artifact.json`](../../../bench-results/glaurung-cnf-private-parity-leaf-elision-20260719/artifact.json)
has SHA-256 `33638089...6621`; its
[`analysis.json`](../../../bench-results/glaurung-cnf-private-parity-leaf-elision-20260719/analysis.json)
has SHA-256 `17134ac5...066`.

ADR-0260 established equal clauses from the same owner and parity-emission
template, not identical normalized enclosing leaves. ADR-0261's stronger
mechanism inference is false on this population. The preselected non-exact-
delta rule rejects the candidate, so the unprofiled timing protocol below was
not run.

## Unprofiled performance protocol

Timing acceptance uses the production unprofiled monomorph. Prebuild baseline
commit `1bce10fd` and the candidate commit, then run six order-balanced paired
release repetitions (`B,C,C,B,B,C,C,B,B,C,C,B`) over the unchanged 162-query
corrected-wide-v3 representative. Each process uses raw rewrite-off `sat-bv`,
in-process Z3, one job, and ADR-0260's exact deterministic limits, but omits
`--profile-cnf-construction`.

Fail closed unless every repetition has 162/162 decisions, manifest/Z3
agreement, all 88 SAT replays, identical per-query outcomes/AIG nodes/CNF
variables/emitted clauses, matching config/environment/corpus identities, and
no fallback or error.

For each repetition, sum per-query Axeyum `cold_total_ms`; pair by the declared
schedule. Accept the candidate only if:

- the six candidate/baseline total-time ratios have geometric mean at most
  `0.97` and a deterministic paired-bootstrap 95% upper bound below `1.0`;
- neither baseline nor candidate run-total CV exceeds 3%; and
- no family-level paired geometric mean exceeds `1.02`.

Profiled timing is diagnostic and excluded. If any correctness, structural,
environment, variance, aggregate, or family gate fails, retain the measurement
and reject the candidate. Do not tune the threshold, widen scope, or combine
the smaller origin cells.

## Consequences

This was the one experiment ADR-0260 authorized. Its structural failure closes
the origin-selected candidate and the current duplicate-origin lane. The
no-op production change is removed; its commit and complete negative evidence
remain retained. Any future cold-clause candidate needs new preregistered leaf-
shape or clause-overlap evidence rather than reinterpretation of this origin
cell. Warm retention, SAT tuning, Glaurung concretization policy, and symbolic
memory remain unchanged.

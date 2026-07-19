# ADR-0261: Preregister private parity-leaf elision

Status: accepted
Date: 2026-07-19

Result state: candidate implementation and local validation complete; fixed
real-query observation not yet started

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

Private positive-root AND-tree collection now performs one deterministic
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
crates pass. No corrected-wide-v3 query has been observed on this candidate.
Commit this boundary before running the fixed structural verification.

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

This is the one experiment ADR-0260 authorizes. A pass removes redundant cold
construction work without changing CNF; a fail closes this origin-selected
candidate on the current population. Either outcome leaves warm retention,
SAT tuning, Glaurung concretization policy, and symbolic memory unchanged.

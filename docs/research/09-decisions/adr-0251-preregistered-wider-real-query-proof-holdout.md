# ADR-0251: Preregister a wider real-query proof holdout

Status: accepted
Date: 2026-07-19

Result state: preregistered; no holdout query observed

## Context

ADR-0234 and ADR-0235 certify all 74 UNSAT rows in the corrected five-driver
162-query representative manifest, including killable whole-certificate
process isolation. The corrected full corpus contains 30,628 unique real
queries (21,333 SAT and 9,295 UNSAT), so the representative proves the method
but remains a narrow proof denominator.

Running the full 9,295-UNSAT certificate population immediately would be a
large resource commitment and would not distinguish a planned denominator from
a finishers-only sample. The next step needs a materially wider, exact,
reproducible population selected before certificate completion or timing is
observed.

## Decision

Create `corrected-wide-v3-proof-holdout-v1`, a 1,024-query population disjoint
from every row in ADR-0234/0235's representative manifest. Bind the source
manifests by SHA-256:

- full 30,628-query manifest:
  `c3cad70caff90d7f1528196e306cbb45808c14f839f07e742aac6ad2f0ade75c`;
- excluded 162-query representative manifest:
  `7818686bc26c56646775eb2f557e1e4edb36e4e8254a8c410fe0333da1ba2064`.

The selector first removes all representative content hashes. It groups the
remaining rows by the already-recorded family and expected verdict, takes the
lexicographically smallest content hashes under fixed quotas, then globally
sorts the result by content hash:

| Stratum | Quota |
|---|---:|
| arithmetic / SAT | 170 |
| arithmetic / UNSAT | 170 |
| comparison / SAT | 6 |
| register-slice / SAT | 170 |
| register-slice / UNSAT | 170 |
| slice-partial / SAT | 169 |
| slice-partial / UNSAT | 169 |

The result is exactly 515 SAT and 509 UNSAT. The representative already
contains every full-corpus mixed row, the only trivial row, and every
comparison/UNSAT row; this holdout adds all six remaining comparison/SAT rows.
The combined evidence union will therefore contain 1,186 unique real queries
and retain complete rare-stratum coverage.

Selection uses no Axeyum/Z3 outcome beyond the pre-existing manifest verdict,
no proof/certificate status, and no timing. The committed selector is
`scripts/select-glaurung-proof-holdout.py`; the generated manifest is
`corpus/glaurung-proof-populations/corrected-wide-v3-proof-holdout-v1.json`
with SHA-256
`67c7f14f5f2f8db1eaa1bb17649cf3623e268e3f7ea678cbe53326bfa8cd899b`.
The machine-readable registration fixes every source, quota, execution, and
acceptance field beside it.

## Execution and acceptance

Run two CPU-3-pinned clean detached processes from the commit containing this
registration using artifact v34's raw/full, proof-producing SAT-BV route:

- end-to-end cooperative proof-search deadline: 1,000 ms;
- killable whole-worker timeout: 1,500 ms;
- per-query solver timeout: 30,000 ms;
- deterministic resource/node/CNF bounds unchanged from ADR-0235;
- in-process Z3 comparison, manifest comparison, and SAT model replay required;
- one benchmark worker and one manifest-validation worker.

All 1,024 rows must decide as the manifest's exact 515 SAT / 509 UNSAT split.
Every SAT model must replay, every UNSAT must carry independently checked CNF
DRAT, and all 509 UNSAT rows must enter the end-to-end attempt partition. Z3 or
manifest disagreement, missing CNF proof, satisfiable contradiction,
certificate recheck failure, worker/protocol error, source drift, or repeated
per-query status drift rejects.

Cooperative expiry or hard worker timeout remains an explicit `not-certified`
coverage miss. It is retained in the 509-row denominator and is not a solver
verdict, a proof failure, or permission to drop the row. Do not change the
fixed deadlines after observing the holdout and call the adapted result this
experiment.

## Validation before execution

Four selector tests cover deterministic hash-first selection, representative
exclusion, quota shortage, nonmember/duplicate rejection, malformed source
manifests, and exact registration/selector/manifest hashes and counts. The
selector reproduces the committed manifest byte for byte. Independent JSON
inspection confirms 1,024 rows, 515 SAT, 509 UNSAT, exact quotas, and zero
representative overlap. No selected query has yet been run by this protocol.

## Consequences

This is a correctness/deployability denominator, not a solver-performance
experiment. Its verdict-balanced hash strata are deliberately not a
prevalence-weighted sample, so any certification percentage describes this
registered holdout only. CNF DRAT coverage and stronger end-to-end faithfulness
remain separate statements.

The result cannot change the concretization default, establish finding recall,
or reopen symbolic memory. Preserve a rejected or partially not-certified
outcome exactly; do not replace it with an easier finishing subset.

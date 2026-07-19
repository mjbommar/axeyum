# ADR-0252: Materialize the exact real-query proof holdout before execution

Status: accepted
Date: 2026-07-19

Result state: materialization preregistered; corrected holdout not yet executed

## Context

ADR-0251 preregistered a 1,024-query manifest selected from a 30,628-query
corpus. The first execution paired that selected manifest with the full corpus
root. `axeyum-bench` correctly rejected the pair before query execution because
29,604 discovered `.smt2` files were not listed by the selected manifest. It
exited 1, produced no artifact, and exposed no solver, proof, certificate, or
timing outcome from a selected query. An exact clean-detached reproduction has
byte-identical stdout and stderr. The attempt is preserved under
`bench-results/glaurung-real-query-proof-holdout-20260719/attempt-1-membership-rejection/`.

The benchmark's exact-membership check is a useful fail-closed property and
must not be weakened to admit subset manifests over larger roots. The execution
protocol instead needs an isolated corpus root containing exactly the already
selected files.

## Decision

Materialize the exact ADR-0251 selection into a new isolated directory before
either corrected repetition. The tested
`scripts/materialize-glaurung-proof-holdout.py` route must:

1. verify the fixed full-manifest SHA-256;
2. verify the fixed selected-manifest SHA-256;
3. require every selected row to be an exact full-manifest member by path,
   content hash, expected verdict, and family;
4. verify every selected source query's content hash before creating output;
5. copy exactly those 1,024 files and verify their destination bytes;
6. write the selected manifest byte for byte as `manifest-v1.json`;
7. independently enumerate the output and require exactly the selected 1,024
   `.smt2` paths; and
8. refuse any existing destination.

The machine-readable registration binds the materializer SHA-256. The corrected
two-run campaign inherits every ADR-0251 execution and acceptance field. It
does not change a selected hash, quota, verdict balance, repetition count,
deadline, resource bound, oracle, replay requirement, or certification gate.

## Evidence before corrected execution

The rejected command and its exact reproduction both exit 1 with empty stdout,
the same 2,397,983-byte stderr SHA-256
`a94cc71dd0cbb68840b0a37745e427528363986770127fd54b985e329a493c57`,
and no result artifact. The retained failure record fixes zero selected queries
executed, zero missing selected files, and 29,604 unlisted files.

Four materializer tests cover exact membership and byte preservation, source
content drift before destination creation, nonmember selection, manifest-hash
drift, and overwrite refusal. They pass together with ADR-0251's four selector
tests. No corrected holdout query was run before this decision and its
machine-readable registration were committed.

## Alternatives

Weakening `axeyum-bench` to ignore unlisted corpus files is rejected because it
would make a manifest cease to define the complete measured population.
Editing the 30,628-query corpus in place is rejected because it is destructive
and would destroy source identity. Symlinking without content re-verification
is rejected because it leaves the execution dependent on later source changes.

## Consequences

The corrected run gains an explicit, reproducible packaging boundary while the
original fail-closed benchmark invariant remains intact. The first attempt is
not discarded or relabeled; it remains a pre-execution protocol rejection.
Any future materialization or execution drift rejects rather than authorizing
an easier subset or adapted resource policy.

# ADR-0576: Job-shop machine orders are replayable witnesses

Status: accepted
Date: 2026-08-26
Index-summary: Import compact machine-job permutations by deterministic earliest-schedule reconstruction and independent replay

## Context

ADR-0565 admitted complete operation start matrices as portable job-shop witnesses. Public
benchmark archives also commonly publish a smaller representation: one row per machine, with
each row giving a permutation of job identifiers. The representation determines machine edges
but does not itself state operation start times, and arbitrary rows can conflict with job-chain
edges to form a cycle. Treating a displayed makespan or an unchecked conversion as a witness
would violate the independent-replay boundary.

This became concrete for `abz7`. A current archive exposes 15 machine rows for its published
makespan 656 result, while the local search had independently reached only 657.

## Decision

Add strict parsing for the zero-based machine-job permutation convention and a deterministic
constructor for its earliest feasible schedule. The constructor forms the full precedence DAG
from consecutive operations in every job and consecutive jobs on every machine, then computes
stable topological longest paths. It rejects dimension errors, non-permutations, malformed
operation metadata, overflow, and cycles. Before returning, it runs the existing independent
schedule checker over all precedence, non-overlap, and makespan conditions.

Expose this route in `certify_job_shop` as `--machine-order-witness`. The reconstructed schedule
may be serialized, but the command also pins it into the independently generated bounded CNF and
requires a replayed SAT result. Machine-order and start-matrix inputs are mutually exclusive.

## Evidence

Positive, repeated-job, and cyclic-order controls exercise the generic importer. The published
15-row `abz7` input reconstructs a 300-operation schedule of makespan 656. With exact job windows,
Axeyum pins that schedule into the 175,770-variable / 1,696,774-clause formula and returns
`sat-replayed` in the end-to-end command.

## Alternatives

- Trust the archive's displayed 656 value: rejected because a scalar is not a witness.
- Convert the rows only in the research package: rejected because this public interchange format
  recurs across job-shop archives and the validation boundary belongs with the typed semantics.
- Accept partial machine rows: deferred; completion search would be a different contract from
  deterministic witness import.

## Consequences

Compact historical schedules can now enter Axeyum without a bespoke script or trusted timestamp
conversion. This establishes only the upper bound described by the rows. Optimality still requires
an independently checked refutation of makespan 655, and no novelty is claimed for the published
schedule or the standard precedence-DAG construction.

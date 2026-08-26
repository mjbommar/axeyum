# ADR-0575: Bounded job-shop FlatZinc is a proof interchange

Status: accepted
Date: 2026-08-26
Index-summary: Export exact bounded job-shop models on the solver-and-checker shared DRCP surface

## Context

Axeyum's time-indexed SAT/DRAT route is complete but did not settle `abz7@655` in sustained
calibration. Current Pumpkin supports scheduling-specific lazy-clause generation and DRCP
proof logging, while FznDrcpCheck checks DRCP directly against FlatZinc with a checker proved
sound in Rocq. Importing a solver status would violate Axeyum's evidence boundary; exporting
an exact model on the independently checked predicate surface permits an external search
engine without trusting it.

Pumpkin's solver accepts a private `pumpkin_disjunctive_strict` predicate that its checkers do
not parse. The shared surface instead contains `int_lin_le` and `pumpkin_cumulative`.
Positive-duration unit-demand cumulative scheduling at capacity one has exactly the required
machine non-overlap semantics.

## Decision

Add `job_shop_to_pumpkin_flatzinc`. It validates the classical permutation-job-shop shape and
emits, deterministically:

- one integer start variable per operation, bounded only by its defining job-chain prefix and
  suffix durations;
- one `int_lin_le` constraint for each adjacent job precedence; and
- one `pumpkin_cumulative` constraint per machine, with every demand and capacity equal to one.

The exporter refuses malformed dimensions, machines, duplicate visits, zero durations,
overflow, or a bound already contradicted by one job chain. It performs no search-derived
domain narrowing. The model is an external proof interchange, not kernel evidence by itself:
an infeasibility claim requires a full DRCP proof checked against the exact emitted bytes.

## Evidence

- The two-job unit test checks exact domains, precedence, cumulative constraints, stable schema,
  and fail-closed rejection below a job's duration sum.
- For `ft06@54`, Axeyum emits a 3,404-byte model with SHA-256
  `e4671a168ce26b4c0824e83656c4f43baafd0c86ea62bde3d88f75f539dc65c8`.
  Pumpkin at commit `a1b77f2f...a3993c41b6bc4b` returns UNSAT in 0.01 seconds and emits a
  19,396-byte full gzipped DRCP proof.
- Pumpkin's independent Rust checker accepts that proof. FznDrcpCheck at commit
  `d67a9adb...ce88673b3fadc8`, built from its Rocq development under Coq 8.20.1, independently
  accepts the uncompressed proof.
- Weakening the first machine duration from three to two makes both checkers reject inference
  1887 as unsound. Exit zero therefore depends on proof validity, not process completion.
- Focused tests, all-target/all-feature Clippy, and deterministic regeneration of the live
  `abz7@655` model are green. The latter is 29,156 bytes with SHA-256
  `09968a6443d08858de126de22505730d8ec69efacea7e31c46d551947c1d81fe`.

## Consequences

Axeyum can dispatch exact bounded job-shop lower-bound questions to a scheduling-aware
proof producer while retaining a small, independently checkable admission boundary. The
generated FlatZinc, DRCP proof, checker version, and hashes must travel together. This does
not make external propagation trusted and does not certify `abz7` until its long-running
proof completes and checks; an interrupted proof prefix has no evidentiary value.

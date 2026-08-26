# Imported Nat.mod operation registration

Date: 2026-08-26

## Result

The 3/3 imported `Nat.mod` remainder family is now one typed authoritative
operation: `authoritative-mathlib-nat-modeq-remainder-family-v1`. It names
exactly the three still-open arithmetic `Nat.ModEq` facts, one shared candidate
receipt, a fixed two-binder search budget, and the existing independent
transport/application checker.

The reviewed gate does not trust the eligibility summary. It validates every
external capsule's bytes, SHA-256, record count, and read-only mode, then runs
three fresh release-mode source transports, bounded searches, and theorem
admissions. All three replay the committed goal, proof, declaration, binder,
term-count, dependency-count, footprint, and target-isolation identities.

Registration raises the reusable multi-target operation count but settles zero
facts. That separation is intentional: proof feasibility, dispatch authority,
and durable ledger mutation are three different claims.

## Receipt shape

This family cannot reuse the older dependency-free ModEq receipt unchanged.
Each accepted theorem retains exactly one direct theorem dependency: the
transported behavior contract used in its proof. The probe therefore now emits
stable goal, proof, declaration, admitted-declaration, and dependency identities
needed by an authoritative per-fact execution receipt.

The execution design follows ADR-0554: although the operation is multi-target,
each execution and transaction binds exactly one frontier-selected fact.

## Next falsifiable step

Extend the authoritative executor, transaction builder, and settled-fact replay
to consume this registered driver while preserving its one checked theorem
dependency. Then select each fact from a fresh frontier and settle it through a
clean crash-safe transaction. Until those executions exist, all three facts
must remain open.

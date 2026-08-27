# ADR-0595: Colouring Hamming balls compose with weighted cardinality

Status: accepted
Date: 2026-08-27

## Context

ADR-0594 made fixed-prefix tail repair typed and explicit. At the next Rado frontier, fixing
positions was too rigid: the relevant question became whether a new point can be accommodated by
changing at most a bounded number of colours anywhere in an existing checked witness. Rebuilding
cardinality logic inside the colouring layer would duplicate ADR-0583's generic weighted-at-most
CNF composition.

## Decision

`ColouringProblem::encode_with_witness_hamming_ball` composes the canonical colouring formula
with the existing bounded weighted-at-most encoder. For every compared point, the counted literal
is the negation of its witnessed-colour literal. Canonical exactly-one clauses make that literal
true exactly when the point changes colour. Later points are unrestricted.

The method returns `WeightedAtMostEncoding`, not a bare formula, so a satisfying model can be
projected back to the canonical variable namespace. Mathematical credit still requires evaluating
that projection against the unrestricted canonical formula and independently replaying the family
relation. Restricted UNSAT proves only a Hamming-neighbourhood statement and requires its own
checked proof; a solver status line is not evidence.

## Evidence

An exhaustive small control checks both sides of the boundary: a one-point mutation is rejected
at radius zero with checked DRAT and accepted at radius one. A SAT model at the center is projected,
decoded, and replayed against the canonical formula. Length, palette, literal-range, and resource
limits fail closed through typed errors. All five focused colouring-guidance tests and all-target,
all-feature Clippy pass.

On the open 405-point Rado instance, a bounded diagnostic reported UNSAT at radii zero through 22;
radius 23 exceeded 120 seconds. No proof was retained, so this is explicitly uncredited telemetry.

## Alternatives

Hand-written sequential counters were rejected as duplicate machinery. Min-conflicts alone was
rejected as unable to measure a precise neighbourhood. Treating solver-reported restricted UNSAT
as a lower-distance theorem was rejected because it has no independently checkable certificate.

## Consequences

Any colouring family can now search a deterministic bounded repair neighbourhood while reusing one
audited cardinality encoder. The result type preserves the source-model projection needed for the
trusted replay boundary. Large restricted refutations remain optional search diagnostics until a
proof producer and checker complete.

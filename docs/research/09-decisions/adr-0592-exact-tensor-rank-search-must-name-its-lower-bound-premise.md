# ADR-0592: Exact tensor-rank search must name its lower-bound premise

Status: accepted
Date: 2026-08-26

## Context

Tensor-rank encodings normally ask for rank *at most* a budget, so zero rank-one summands are
valid padding. Requiring every summand to be nonzero is not an unconditional symmetry breaker:
a tensor of smaller rank need not have an exact-budget decomposition with nonzero padding.

For `P_6`, Wang's independently replayed certificate proves rank at least 16. A rank-at-most-16
query may therefore use the exact-rank normal form, provided the producer command names the
checked rank-15 exclusion rather than silently changing the ordinary bounded query.

## Decision

`TensorRankEncoding::formula_with_exact_rank_nonzero_summands` returns an explicit augmentation
of the unchanged bounded formula. Each rank-one tensor is nonzero exactly when all three factor
vectors are nonzero, so it adds one positive disjunction per factor and summand, with no new
variables. The polynomial driver exposes this only as
`--exact-rank-after-checked-lower RANK_MINUS_ONE`, rejects any other number, and refuses to mix
the mode with a pinned witness.

The API documentation and CLI output retain the premise. Formula statistics are printed from
the actual selected terminal formula rather than the unaugmented encoding.

## Evidence

The independently checked `P_2` rank-two DRAT supplies a small lower-bound premise. Its
rank-three exact formula remains SAT, lifts, independently replays, and every lifted factor is
nonempty. The augmentation adds exactly `3 * budget` clauses. Warning-denied Clippy and Rustdoc
pass.

For `P_6@16`, the complete polynomial-action formula grows from 105,262 to 105,310 clauses,
keeps 26,489 variables, occupies 1,811,206 bytes, and has SHA-256
`bc932196d924c73136cac41566c4a0c08bac2ddd363a70443581d8880a2c7815`. CaDiCaL seed 2615 is
running without a short cutoff. Its incomplete proof stream has no mathematical status.

## Alternatives

- Make nonzero summands the default: rejected because that changes at-most-rank semantics.
- Trust the brief's lower bound: rejected; the exact upstream certificate was replayed before
  this premise was used.
- Encode only one nonzero factor: rejected; a rank-one tensor is zero when any factor is zero.

## Consequences

Exact-rank tensor consumers can remove zero padding through a generic, premise-explicit route.
The lower-bound certificate remains a separate required artifact. This reduction neither finds
a rank-16 decomposition nor proves its absence.

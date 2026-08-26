# ADR-0568: Matrix-tensor search normalizes one summand under the stabilizer

Status: accepted
Date: 2026-08-26
Index-summary: Normalize one matrix-multiplication rank-one summand by factor rank and order only the remaining terms

## Context

ADR-0567 removes permutation of rank-one terms but leaves the change-of-basis stabilizer of
the matrix-multiplication tensor untouched. A naive stabilizer lex-leader over the whole
symbolic decomposition is expensive, and pinning an orbit representative in slot zero while
also comparing that slot with the sorted remainder can be unsound: the representative need
not be the smallest term.

The classical de Groote action supplies a smaller complete normalization. In any nonzero
summand, interpret the first factor as an `m x n` matrix `A`. Invertible row and column changes
send `A` to `diag(I_q,0)`, where `q=rank(A)`. Coupled inverse changes on the other two factors
preserve the matrix-multiplication tensor.

## Decision

Add `encode_matrix_tensor_rank_with_normalized_first_factor(m,n,p,...)`. It builds the target
itself, requires a nonzero summand in slot zero, and constrains its first factor to one of the
`min(m,n)` rank-normal forms. A selector records the rank. The second and third factors of
slot zero must be nonzero. Slots one onward—not slot zero—are lexicographically ordered.

This is complete for every nonzero matrix-multiplication tensor: choose any nonzero summand,
move it to slot zero, apply the stabilizer normalization to its first factor, and sort the
remaining summands. The generic and term-order-only encoders remain byte-stable.

Witness pinning accepts a pre-normalized first term and canonicalizes only the remaining
terms and zero padding. It rejects a valid decomposition whose first term is not one of the
declared forms rather than pretending to apply an unrecorded basis transformation.

## Evidence

- Strassen's first term already has the rank-two diagonal form. At budget eight, the formula
  sorts a padded zero among slots one onward, solves, lifts to seven terms, and replays.
- Swapping a different valid Strassen term into slot zero is rejected at the normalization
  boundary even though the unordered decomposition itself still replays.
- Wang's `<3,2,4>` rank-20 witness has rank-one form `[0]` in slot zero; it pins, solves in
  7 ms, lifts, and independently replays all 576 coefficients.
- The normalized rank-19 question has 22,641 variables / 89,206 clauses. CaDiCaL 3.0.1
  reached 300 seconds / 117,376 KiB without a model or proof. The verdict is interrupted.

## Consequences

Axeyum now has a matrix-specific, completeness-argued stabilizer reduction rather than an
unqualified symmetry heuristic. The open interval remains `[19,20]`; neither a timeout nor
normalization proves a rank bound. More stabilizer reduction requires a composable orbit
cover or a symbolic action with its own completeness checker.

The normalization is classical prior mathematics. Current Scholar, arXiv, web, and reference
toolkit searches recover the isotropy/de Groote action and equivalent-polyadic-decomposition
literature. No novelty claim attaches to the technique or the interrupted run.

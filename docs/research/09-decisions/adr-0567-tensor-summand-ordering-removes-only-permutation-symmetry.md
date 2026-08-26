# ADR-0567: Tensor summand ordering removes only permutation symmetry

Status: accepted
Date: 2026-08-26
Index-summary: Optionally lex-order GF(2) rank-one summands without changing the bounded tensor-rank question

## Context

ADR-0564's complete bounded-rank encoding gives every rank-one summand a numbered slot even
though tensor addition is commutative. A rank-`r` decomposition consequently appears in up to
`r!` slot orders. The open `<3,2,4>` rank-19 baseline reached its time limit without a result,
and the programme identified symmetry—not formula size—as the likely obstruction.

Existing retained CNFs and DRAT proofs bind the unsymmetrized encoding, so changing the
default formula would invalidate reproducibility. Term ordering is also standard lex-leader
symmetry breaking, not a novel mathematical technique.

## Decision

Keep `encode_tensor_rank` byte-for-byte stable and add the opt-in
`encode_tensor_rank_with_ordered_terms`. It compares each adjacent pair of concatenated
`a || b || c` factor vectors lexicographically with `false < true`. Tseitin variables encode
bit equality and equal prefixes; every first difference `1,0` is forbidden.

This restriction is complete: permuting rank-one summands does not change their sum, and every
finite list has a sorted representative. Padded zero summands sort first. Witness pinning
therefore canonicalizes the supplied term list and padding before adding units. Model lifting
and independent coefficient replay remain unchanged.

## Evidence

- Exhaustive two-bit tests compare all 16 ordered pairs with the intended numeric/lex order.
- A reversed Strassen witness with one padded zero term pins, solves, lifts to seven nonzero
  terms, and independently replays under the ordered encoding.
- Wang's unsorted `<3,2,4>` rank-20 witness canonicalizes, solves in 8 ms, lifts, and replays
  all 576 coefficients.
- The open rank-19 formula grows from 21,806 variables / 85,824 clauses to 22,688 / 89,388.
  CaDiCaL 3.0.1 reached 300 seconds and 7,140,981 conflicts without a model or proof. This is
  an interrupted performance measurement, not rank evidence.

## Consequences

Axeyum can remove the complete summand-permutation symmetry while preserving old artifacts
and the exact decision question. The failed open-cell run shows this symmetry alone is not
the frontier solution. Further work must address tensor stabilizer/basis symmetries or use a
different algebraic search; any such restriction needs its own completeness argument.

Current Scholar, arXiv, web, and toolkit searches explicitly recovered prior lex-leader term
ordering and general SAT symmetry literature. No novelty claim attaches to the breaker.

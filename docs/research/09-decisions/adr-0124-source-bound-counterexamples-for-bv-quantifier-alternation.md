# ADR-0124: Source-bound counterexamples for BV quantifier alternation

Status: accepted
Date: 2026-07-11

## Context

The remaining public cvc5 quantified-BV UNSAT unknown
`small-pipeline-fixpoint-3` is a closed formula with prefix
`forall* exists*` and a quantifier-free Bool/BV matrix. A concrete outer
trajectory can make the matrix false for every inner trajectory, but ADR-0100
handles only universal prefixes whose body can be evaluated at one complete
assignment. Enumerating either 32-bit domain is infeasible, while accepting a
search-produced outer trajectory without proving the residual existential body
impossible would violate the project's evidence contract.

## Decision

**Admit a narrow closed Bool/BV `forall+ exists+` counterexample certificate
whose concrete outer bindings are checked by source-instantiating the exact
matrix, replacing existential binders with fresh free constants, and rechecking
a source-bound QF_BV DRAT refutation of that residual formula.**

Admission requires one source assertion with a nonempty universal prefix
followed by a nonempty existential prefix, unique Bool/BV binders, a closed
quantifier-free Bool/BV matrix, and explicit size caps. Candidate generation is
restricted further to an implication whose antecedent mentions only universal
binders. It solves the antecedent and deterministic one-binder perturbations to
obtain candidate outer assignments. Search is untrusted: only a candidate whose
fully instantiated matrix yields an `UnsatProof` accepted by
`recheck_for_bool_terms` becomes evidence.

The checker repeats prefix validation, binding order and sort checks, constant
substitution, deterministic existential freshening, exact source-to-CNF
regeneration, and DRAT/LRAT checking. Thus a valid certificate proves that one
outer assignment makes `exists inner. matrix` false, which refutes the original
universal. As with ordinary QF_BV `UnsatProof`, the term-to-AIG-to-CNF reduction
is the existing explicit trusted reduction; the quantifier instantiation and
stored proof are not trusted.

## Evidence

`small-pipeline-fixpoint-3` moves from unknown to source-bound certified UNSAT
in five optimized samples of 62.063, 65.440, 62.282, 64.536, and 63.692 ms
(median 63.692 ms). The public cvc5 quantified-BV slice is now 32 SAT / 10
UNSAT / 1 unknown / 11 unsupported, with 42 expected-status agreements, no
disagreement, error, or replay failure, and five-run PAR-2 samples 5.613183,
5.614123, 5.613303, 5.613392, and 5.613350 seconds (median 5.613350 seconds).

The dominance audit independently certifies and checks all 42 decisions. The
target is classified `bv-alternation-counterexample-unsat`, has an empty trust
ledger, and correctly declines Lean reconstruction; total Lean coverage is 8/10
UNSAT and dominance is 40/42. The direct-Z3 quantified-BV suite now covers
1,320 cases and controls with zero disagreement; its 64 new alternation cases
split into 32 checked ADR-0124 UNSAT certificates and 32 agreed SAT controls.

Four focused tests cover the public target and reject changed/missing/reordered
bindings, changed proof text, stale assertions, free symbols, Int binders,
reversed prefixes, non-implication matrices, and existential symbols in the
antecedent. The workspace Clippy gate is clean.

## Alternatives

- **General QSAT or BV quantifier elimination.** Deferred: it is a much larger
  engine and proof surface than the measured case requires.
- **A transition-system-specific syntactic theorem.** Rejected for the first
  slice: the generic outer-witness plus residual-QF proof has a smaller trusted
  semantic argument and applies beyond one benchmark naming convention.
- **Trust the candidate inner solve.** Rejected: an UNSAT verdict must carry a
  source-bound checked artifact.
- **Use only the end-to-end bitblast miter artifact.** Deferred until its stored
  faithfulness proof can itself be rebound to regenerated source terms during
  consumer replay.

## Consequences

One useful finite-state alternation class gains checked UNSAT evidence without
finite-domain enumeration. Search remains deliberately incomplete and may
decline. General alternation, open formulas, functions, arrays, arithmetic,
Skolem functions, proof serialization above the QF instance, and Lean
reconstruction remain open.

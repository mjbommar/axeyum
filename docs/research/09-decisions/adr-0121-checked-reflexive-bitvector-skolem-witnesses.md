# ADR-0121: Checked reflexive bit-vector Skolem witnesses

Status: accepted
Date: 2026-07-11

## Context

ADR-0096 gives satisfiable `forall* exists` assertions a replayable Skolem
certificate, but materialization currently accepts only affine `Int` and `Real`
recipes. The public cvc5 regression `issue4328-nqe` is the exact finite-domain
theorem

```smt2
(forall ((a (_ BitVec 32)))
  (exists ((b (_ BitVec 32))) (bvsle a b)))
```

and has the global witness `b := a`. Axeyum therefore leaves a public SAT row
undecided even though substitution reduces the untouched source body to the
primitive reflexivity fact `bvsle a a`.

General BV Skolem synthesis would require explicit modular-polynomial semantics,
piecewise witnesses, or quantifier elimination. None is needed for this row, and
silently interpreting ADR-0096's rational affine recipe modulo `2^w` would make
the certificate format ambiguous.

## Decision

**Extend ADR-0096 only with an exact same-width bit-vector identity witness and
prove the substituted source body with the independent small checker before
returning SAT.**

For a bit-vector existential, `AffineSkolemWitness` has one accepted
interpretation:

- `terms` contains exactly one original-arena universal variable term;
- that term has the existential's exact `Sort::BitVec(width)`;
- its coefficient is exactly one; and
- `constant` is exactly zero.

The checker independently re-matches the exact `forall* exists` prefix,
validates binder identity and width, materializes only that identity in a cloned
arena, substitutes it into the untouched quantifier-free body, and accepts only
when its small Boolean checker proves the result. The checker learns syntactic
reflexivity for non-strict signed and unsigned BV order (`bvsle x x`,
`bvule x x`); equality reflexivity is already supported. Unsupported relations,
strict comparisons, non-identical operands, offsets, multiple terms,
non-unit coefficients, composite BV atoms, nested quantifiers, and multiple
existentials decline.

Canonical model replay validates an attached certificate before attempting
finite enumeration. This prevents a width-at-most-16 `forall`/`exists` theorem
from taking combinatorial evaluator time or rejecting an otherwise valid
certificate as unchecked, while the existing exact certificate-count gate still
rejects duplicate, stale, or unchecked artifacts.

Search remains untrusted. It proposes each same-sort leading universal as an
identity witness in deterministic binder order. If no proposal passes the
certificate checker, BV witness search stops before the existing arithmetic
bound synthesizer. The existing `Model`, `check_model`, and `Evidence::Sat`
routes carry and replay the accepted certificate without a new public result
variant.

## Acceptance

- `issue4328-nqe` moves from `unknown` to replayed and evidence-certified SAT,
  with an empty trust ledger and no mutation of the caller's arena.
- Signed and unsigned non-strict reflexive theorems across representative widths
  agree with Z3; strict, reversed/non-reflexive, width/sort, polarity, nesting,
  and certificate-tamper cases fail closed.
- The public cvc5 quantified-BV slice gains the target decision with zero
  disagreement, error, or replay failure and without regressing existing rows.
- Solver, evidence, MBQI, quantified differential, bounded-instance, benchmark,
  static documentation/resource, and reference gates pass.

## Evidence

- The target witness substitutes to `bvsle a a`, whose truth follows directly
  from reflexivity of the SMT-LIB signed non-strict order at every width.
- cvc5 handles nested quantification by recursively eliminating nested formulas
  through a subsolver in
  `references/cvc5/src/theory/quantifiers/cegqi/nested_qe.cpp`. Z3's generic BV
  MBP solve plugin currently isolates positive equalities in
  `references/z3/src/qe/mbp/mbp_solve_plugin.cpp`. The proposed checker is much
  narrower than either general route and exposes its complete trusted boundary.
- ADR-0096 already establishes the arena-stable recipe, exact-source
  substitution, canonical model replay, and search/checker separation used by
  this extension.

Accepted results:

- `issue4328-nqe` moves from `unknown` to replayed SAT with one exact identity
  certificate. Five optimized public-corpus runs put its solve-time median at
  0.008736 ms.
- The 54-row cvc5 quantified-BV slice moves from 29 SAT / 9 UNSAT / 5 unknown /
  11 unsupported to 30 / 9 / 4 / 11. Every run has zero disagreement against
  declared statuses, errors, or model replay failures. Five-run PAR-2 median is
  7.00692 seconds (the committed artifact is 7.00760 seconds).
- The dominance audit checks and certifies all 39 decisions. The new row is a
  dominant candidate with `quantified-skolem-sat` evidence and an empty trust
  ledger; the division has 38/39 dominant candidates and Lean-checks 8/9 UNSAT.
- A 64-case direct-Z3 matrix requires all 32 signed/unsigned identity cases to
  be jointly SAT and replayed across widths 1 through 64. Together with the
  existing suites, all 1,128 direct-Z3 quantified-BV cases have zero
  disagreement; 900 bounded-instance cases also pass.
- Exact recipe tampering (constant, coefficient, composite atom, foreign
  symbol, and width mismatch), strict/non-reflexive controls, caller-arena
  preservation, evidence replay, and width-16 finite-domain replay all fail
  closed or certify as specified. Moving certificate validation before finite
  enumeration fixes the discovered combinatorial replay path without trusting
  search.
- Solver 863/863, witness 14/14, certificate 12/12, evidence 69/69, MBQI 13/13,
  and benchmark 7/7 pass. Quantified LIA remains 12/12; the Bitwuzla control is
  5/5 (one SAT, four UNSAT) with no replay failure. Workspace Clippy, warning-
  denied rustdoc, generated matrices, foundational resources (137 concepts / 174
  packs), links, formatting/diff hygiene, and all 26 reference clones pass.

## Alternatives

- **Interpret every rational affine recipe modulo the BV width.** Rejected: it
  changes the meaning of a public certificate type and requires a substantially
  broader modular-arithmetic checker.
- **Enumerate all BV values.** Rejected: width 32 makes enumeration impractical,
  while syntactic identity proves the theorem independently of width.
- **Trust the search-side substitution or a QF solver result.** Rejected: public
  SAT credit must replay against the original assertion through a smaller,
  independent checker.
- **Implement general nested BV QE first.** Deferred: it is needed for the wider
  alternating-QSAT frontier, but is unnecessary risk and complexity for this
  exact public decide-rate increment.
- **Teach the checker strict reflexivity as false and reason through arbitrary
  negation.** Deferred unless demanded by a measured target; the SAT route needs
  only positive non-strict reflexivity.

## Consequences

- One exact and useful BV Skolem class becomes replayable without weakening the
  quantified-model contract or adding native-solver reliance.
- `AffineSkolemWitness` remains affine over `Int`/`Real`; for BV its only defined
  form is the explicitly documented identity encoding above.
- General BV witness functions, modular offsets/arithmetic, piecewise Skolems,
  nested QE/QSAT, serialization, and Lean reconstruction remain open.

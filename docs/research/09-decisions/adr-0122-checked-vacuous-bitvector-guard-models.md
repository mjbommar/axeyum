# ADR-0122: Checked vacuous bit-vector guard models

Status: accepted
Date: 2026-07-11

## Context

ADR-0121 recovers a first nested quantified-BV SAT row with an identity Skolem,
but the next public cvc5 blocker, `issue5365-nqe`, has deeper alternation:

```smt2
(exists ((a (_ BitVec 32)))
  (forall ((b (_ BitVec 32)) (c (_ BitVec 32)))
    (exists ((d (_ BitVec 32)) (e (_ BitVec 32)))
      (forall ((g (_ BitVec 32)))
        (exists ((f (_ BitVec 32)))
          (=> (= (_ bv0 32) a) consequent)))))
```

The theorem does not require general BV QE or inner Skolem synthesis. Choosing
`a != 0` makes the implication antecedent false, so the matrix is true for every
assignment to every inner binder. Axeyum's existing top-level skolemization is
equisatisfiable search, but it replaces the original binder with an internal
free symbol and carries no original-assertion witness certificate. Crediting its
residual result directly would violate mandatory original-query replay.

## Decision

**Represent this class with a dedicated outer-witness certificate and grant SAT
only when an independent original-IR checker proves an exact false equality
guard below an arbitrary direct Bool/BV quantifier prefix.**

The public `QuantifiedGuardSatCertificate` records the untouched assertion, the
outer existential binder, and one concrete BV witness. The checker independently
requires:

- exactly one outer `exists` binder whose sort is `BitVec(width)`;
- a witness of that exact width;
- at least one direct nested `forall`/`exists` binder, with every binder unique
  and of sort Bool or BitVec;
- a matrix whose root is binary implication;
- an antecedent that is binary equality between the exact outer binder term and
  one same-width BV constant, in either operand order; and
- a witness unequal to that constant.

The consequent is deliberately opaque. Once the exact antecedent is false, the
implication is true for every assignment, and every admitted inner existential
domain is nonempty. The checker therefore neither traverses the consequent nor
calls the broad solver stack. Any changed polarity, Boolean connective,
nonconstant guard side, binder reuse, sort mismatch, missing nested prefix,
stale assertion, or malformed witness declines.

Untrusted search tries deterministic all-zero and one BV witnesses at every
supported width; at least one differs from any constant. Search and checking
live in separate modules. The accepted certificate is stored in `Model`, and
canonical `check_model` validates it before evaluator replay. `Evidence::Sat`
uses the same route.

## Acceptance

- `issue5365-nqe` moves from unknown to replayed, evidence-certified SAT with an
  empty trust ledger.
- The checker accepts both guard operand orders and all BV widths, including the
  wide-BV representation, while exact tamper/shape/polarity/sort negatives fail
  closed.
- A direct-Z3 differential matrix covers supported guarded alternation plus
  satisfiable and unsatisfiable near misses with zero verdict disagreement;
  `unknown` remains permitted outside the certificate class.
- The public cvc5 quantified-BV slice gains exactly the target decision with no
  disagreement, error, replay failure, or existing-row regression.
- Solver/evidence/MBQI/quantifier/benchmark suites plus workspace static,
  documentation, resource, matrix, and reference gates pass.

## Evidence

- `issue5365-nqe` is replayed SAT in a five-run optimized median of 0.004147
  ms. The public cvc5 quantified-BV slice is now 31 SAT / 9 UNSAT / 3 unknown /
  11 unsupported, with 40 oracle agreements, no disagreement, error, or model
  replay failure, and five-run PAR-2 median 6.54204 seconds.
- The dominance audit independently certifies and checks all 40 decisions; 39
  are dominant candidates. The target is classified `quantified-guard-sat`,
  has an empty trust ledger, and is dominant. Lean reconstructs 8/9 UNSAT rows.
- The direct-Z3 quantified-BV suite now covers 1,192 cases and controls with no
  disagreement. Its 64-case vacuous-guard matrix admits and replays all 32
  exact cases, agrees on 10 UNSAT controls, and safely declines the remaining
  out-of-class cases.
- Solver 863/863, guard 5/5, Boolean-model 6/6, quantified-certificate 13/13,
  evidence 69/69, bounded-instance, direct-Z3, and bench 7/7 suites pass.
  Workspace Clippy, rustdoc, generated matrices, links, foundational resources,
  rules-as-code, formatting, diff, and all 26 reference-presence checks pass.
  The broader workspace test run reaches one independent open performance
  ratchet: `frontier_bv_reduction` measures 28 against its committed baseline
  30, including on an isolated rerun. The baseline is intentionally unchanged.
- Propositional implication makes the proof local: `false => P` is true for any
  `P`, independent of alternation depth and the operators in the consequent.
- cvc5's nested-QE route recursively invokes quantifier elimination subsolvers
  (`references/cvc5/src/theory/quantifiers/cegqi/nested_qe.cpp`), while its valid
  witness framework keeps witness axioms explicit
  (`references/cvc5/src/proof/valid_witness_proof_generator.cpp`). Z3 checks
  quantified model interpretations by refuting the negated instantiated
  quantifier (`references/z3/src/smt/smt_model_checker.cpp`). Axeyum's exact
  false-guard checker is a smaller complete proof for this class.
- ADR-0096/0098/0107/0121 already establish that quantified SAT artifacts live
  in `Model`, replay against untouched source assertions, and cannot inherit
  trust from candidate search.

## Alternatives

- **Trust top-level skolemization plus the residual solver result.** Rejected:
  the internal symbol is not a replayable witness for the original assertion.
- **Extend the affine Skolem certificate again.** Rejected: this theorem proves
  SAT by an outer guard assignment, not an affine witness for a `forall* exists`
  prefix; conflating the formats obscures both checkers.
- **Inspect or solve the consequent after finding a false guard.** Rejected:
  it adds irrelevant work and trusted surface to a complete propositional proof.
- **Implement general nested BV QE/QSAT first.** Deferred: required for the
  remaining hard alternation frontier, but strictly unnecessary for this public
  row and not Pareto-positive compared with the constant-time exact checker.
- **Accept arbitrary guard formulas by evaluation.** Deferred until measured.
  Exact symbol-to-constant equality keeps the first contract auditable and
  complete for the target class.

## Consequences

- Deep quantifier alternation can be certified SAT when controlled by one exact
  outer BV equality guard, without fabricating inner Skolem functions.
- `Model` gains a third deterministic quantified certificate family, and the
  canonical exact-certificate-count invariant expands accordingly.
- General free-BV models, non-equality guards, nested Boolean guard structure,
  multiple assertions, piecewise Skolems, BV QE/QSAT, serialization, and Lean
  SAT witness reconstruction remain open.

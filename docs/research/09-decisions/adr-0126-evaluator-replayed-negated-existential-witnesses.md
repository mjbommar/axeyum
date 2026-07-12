# ADR-0126: Evaluator-replayed negated-existential witnesses

Status: accepted
Date: 2026-07-11

## Context

The three smallest unsupported UNSAT rows in the public cvc5 quantified-BV
slice assert the negation of a closed existential whose quantifier-free body has
a concrete Bool/BV witness. `NUM878`, `ari-syqi`, and `ari118-bv-2occ-x` contain
only five to seven source DAG nodes, yet remain unsupported because the generic
quantifier routes do not turn a model of the existential body into independently
checkable evidence for the original negated assertion.

ADR-0100 already establishes the dual trust contract for closed universals:
untrusted QF search proposes binder values, while a small checker evaluates the
untouched original body. Z3's NNF tactic likewise exposes the logical duality by
rewriting a negated existential to a universal with a negated body. The current
cases do not require general quantifier elimination, QSAT, or a new trusted
rewrite.

## Decision

**Admit a bounded closed Bool/BV `not (exists+ body)` fragment and certify its
UNSAT result by evaluating the untouched original body to true under a complete
typed existential witness.**

The public certificate carries the exact top-level assertion and one
`(SymbolId, Value)` pair per existential binder in outer-to-inner order. The
checker requires:

- the certificate assertion is one of the original query assertions and has
  exactly the top-level shape `not (exists+ body)`;
- the prefix is nonempty, has unique Bool/BitVec binders, and contains at most
  128 binders;
- the body is closed, quantifier-free, application-free, Bool-sorted, uses only
  Bool/BitVec terms, and has at most 4,096 distinct DAG nodes;
- carried binder IDs, order, value sorts, and count exactly match the source
  prefix; and
- direct evaluation of the untouched original body under those bindings returns
  `Bool(true)`.

The checker performs no substitution, rewriting, or solver call. Untrusted
search may clone the arena, replace binders with deterministic fresh constants,
solve the positive body through the ordinary QF path, and extract model values.
It returns evidence only after the original-IR checker accepts it. Solver and
evidence dispatch try this route before broader quantified fallbacks. The
evidence has an empty trust ledger; Lean reconstruction is a separate boundary.

## Evidence

The target source formulas have immediate witnesses: zero satisfies
`x * x = x` in `NUM878`; zero differs from 12 in `ari-syqi`; and zero/zero
satisfies `x * y = x` in `ari118-bv-2occ-x`. All operators already have exact
SMT-LIB BV semantics in the ground evaluator. The three rows move from
unsupported to checked UNSAT in median 3, 0, and 3 ms respectively.

The public cvc5 quantified-BV slice moves to 32 SAT / 14 UNSAT / 0 unknown / 8
unsupported, with 46 expected-status agreements, no disagreement, error, or
model-replay failure. Five optimized PAR-2 samples are 3.508581, 3.508276,
3.508230, 3.508589, and 3.508604 seconds (median 3.508581 seconds). The
dominance audit certifies and checks all 46 decisions; all three targets have
taxonomy `negated-existential-witness-unsat`, empty trust ledgers, and correctly
decline Lean reconstruction. Total dominance remains 40/46 and Lean coverage is
8/14 UNSAT.

Six focused tests cover all targets, certificate mutation, source-shape
admission, a satisfiable neighbor, both hard caps, and 64 generated direct-Z3
controls. Together with the existing quantified-BV matrices, 1,400 direct-Z3
cases and controls agree with no disagreement.

Reference implementations support the decomposition without becoming part of
the trusted argument: Z3's `src/tactic/core/nnf_tactic.h` contains the explicit
negated-existential dualization, while cvc5's CEGQI implementation constructs
candidate witness terms. Axeyum deliberately checks concrete values directly
against source IR instead of trusting either transformation or search.

## Alternatives

- **Reuse the ADR-0100 certificate variant.** Rejected: the source matcher and
  evaluator acceptance polarity differ, and a distinct evidence kind keeps
  audits and future Lean reconstruction unambiguous.
- **Normalize `not exists` to `forall not` and use ADR-0100.** Rejected: that
  would add a trusted rewrite or require carrying and checking a transformed
  assertion when direct source evaluation is smaller.
- **Return UNSAT from the successful existential search alone.** Rejected:
  search, substitution, and model projection are untrusted by project policy.
- **Admit Int/Real or nested quantifiers immediately.** Deferred: the measured
  frontier is finite Bool/BV, and broader domains require separate model and
  proof contracts.
- **General QSAT or quantifier elimination.** Deferred: these three cases need
  one source-replayed witness, not a complete quantified engine.

## Consequences

The smallest negated-existential BV contradictions become independently
checkable with no new trusted reduction. The route remains intentionally
incomplete: open bodies, functions, arrays, arithmetic binders, nested
quantifiers, larger prefixes, and larger bodies decline. A successful
certificate proves only that one original assertion is false, which is
sufficient to refute the conjunction represented by the query.

# ADR-0128: Checked vacuous-existential-prefix counterexamples

Status: accepted
Date: 2026-07-12

## Context

After ADR-0127, `issue2031-bv-var-elim` is the smallest isolated UNSAT class
among the seven unsupported rows in the public cvc5 quantified-BV slice. Its
single assertion has the shape

```text
exists y2 y3. forall y5 y6.
  not (-65*y6 + -93*y5 = 69)                 (mod 2^32)
```

The existential binders do not occur in the universal body. The assertion is
therefore equivalent to the remaining universal over the nonempty BV domains,
and one solution of the modular equality falsifies that universal. This is a
smaller theorem than general BV quantifier elimination or QSAT, but it is not
covered by ADR-0100 because that certificate deliberately requires the
universal block at the assertion root.

The local reference sources separate the same concerns. cvc5's
`QuantifiersRewriter::computeMiniscoping` calls `computeArgVec2` and rebuilds a
quantifier after removing variables that do not occur; its BV variable
elimination separately computes active arguments and uses an inversion solver
only for occurring variables. Z3's `unused_vars_eliminator` scans a quantifier
body, removes unused declarations, and remaps the retained de Bruijn variables;
its QSAT engine then recursively handles alternating quantifier levels. These
are useful search and architecture references, not trusted evidence for an
Axeyum verdict.

## Decision

**Certify UNSAT for one exact nonempty `exists+ forall+` Bool/BV assertion when
the existential block is syntactically vacuous and a complete concrete
assignment makes the untouched quantifier-free universal body false.**

The public certificate carries the original assertion and one
`(SymbolId, Value)` pair per universal binder in outer-to-inner order. The
checker requires:

- the assertion belongs to the original query and has Bool sort;
- the source has a nonempty leading existential block followed immediately by
  a nonempty universal block;
- the complete prefix has at most 128 pairwise distinct Bool/BV binders;
- the complete source assertion has at most 4,096 distinct DAG nodes and every
  term is Bool/BV-sorted;
- the body is Bool-sorted, quantifier-free, and contains no `Apply`;
- every body symbol is exactly one of the universal binders, which proves both
  existential vacuity and closure;
- the carried IDs, order, values, and sorts exactly match every universal
  binder; and
- direct evaluation of the untouched original body under those values returns
  `Bool(false)`.

For nonempty Bool/BV domains, if no existential variable occurs in `phi`, then
`exists e. forall u. phi(u)` is equivalent to `forall u. phi(u)`. A concrete
`u0` with `phi(u0) = false` refutes the latter and therefore the original
assertion. This proof does not depend on how the assignment was found.

Untrusted search clones the arena, replaces only universal variables with fresh
symbols, and asks the ordinary QF solver for a model of `not phi`. It projects
typed universal values from that model, fills irrelevant universal variables
with their well-founded defaults, and must pass the independent original-IR
checker before solver or evidence dispatch returns UNSAT. The evidence has an
empty trust ledger. Lean reconstruction is a separate future boundary.

## Evidence

`issue2031-bv-var-elim` moves from unsupported to checked UNSAT. Five optimized
backend samples are 0.129, 0.130, 0.124, 0.130, and 0.122 ms (median 0.129 ms).

The public cvc5 quantified-BV slice is now 32 SAT / 16 UNSAT / 0 unknown / 6
unsupported, with 48 expected-status agreements and no disagreement, error, or
model-replay failure. Five PAR-2 samples are 2.529082, 2.529085, 2.529641,
2.529659, and 2.529213 seconds (median 2.529213 seconds). The dominance audit
certifies and checks all 48 decisions. The target has taxonomy
`vacuous-exists-universal-counterexample-unsat`, an empty trust ledger, and
correctly declines Lean reconstruction; total dominance remains 40/48 and Lean
coverage is 8/16 UNSAT.

Six focused tests cover the public target, binding/source mutation, nonvacuous,
open, reversed, nested, function, and no-universal forms, both hard caps, a
satisfiable vacuous neighbor, and 64 generated UNSAT/SAT pairs checked directly
against static Z3. The cumulative quantified-BV direct-Z3 suite covers 1,592
cases and controls without disagreement.

## Alternatives

- **Silently broaden ADR-0100.** Rejected: the additional prefix-removal theorem
  is a distinct evidence taxonomy and deserves explicit source checks,
  negatives, measurement, and an ADR.
- **Skolemize the existential prefix and trust the resulting search verdict.**
  Rejected: equisatisfiable preprocessing is not an independently replayable
  proof of UNSAT against the original assertion.
- **Apply general BV inversion to the measured equality.** Deferred: inversion
  may be useful candidate generation, but the direct evaluator certificate
  proves a broader bounded class with a smaller trusted checker.
- **Accept free symbols or functions in the body.** Rejected for this route:
  direct evaluation would need additional assignments or function models. A
  source-bound residual proof is a separate contract.
- **General alternating QSAT/QE.** Deferred: this class needs only vacuity plus
  one universal counterexample, not a complete elimination engine.

## Consequences

Closed Bool/BV universal counterexamples remain checkable when wrapped in one
or more genuinely vacuous existential binders. Nonvacuous prefixes, open
bodies, functions, arrays, arithmetic binders, reversed or additional
alternation, proof serialization, and Lean reconstruction remain unsupported
by this route and require separately checked contracts.

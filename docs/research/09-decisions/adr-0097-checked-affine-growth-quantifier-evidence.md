# ADR-0097: Checked affine-growth quantifier evidence

Status: accepted
Date: 2026-07-11

## Context

The next measured P2.6 quantified-LIA blocker is cvc5's
`repair-const-nterm.smt2`. Its assertion has the form

```text
forall xs. not (c*x - ite(x = p, a, b) >= t)
```

where `c` is a positive integer constant, `x` is one of the integer binders,
and `p`, `a`, `b`, and `t` contain no bound variable. The assertion is false
for every interpretation of those four terms, but ordinary e-matching has no
ground trigger from which to discover the unbounded counterexample.

cvc5's general arithmetic CEGQI implementation isolates arithmetic bounds and
can use virtual infinity when a variable has no finite bound
(`references/cvc5/src/theory/quantifiers/cegqi/ceg_arith_instantiator.cpp`).
Z3's MBQI/MBP stack solves the broader projection problem. Axeyum needs the
measured decision now without claiming that a target-shaped recognizer is a
general infinity or MBP implementation. ADR-0095 also requires every targeted
CEGQI schema to arrive with an original-IR checker rather than leave another
bare quantified `Unsat` result.

## Decision

Admit exactly the positive-coefficient affine-growth universal above through
two genuine ground instances, and certify its `Unsat` result with a separate
checker that independently re-matches the original assertion.

Let

```text
q = div(b + t, c) + 1.
```

SMT-LIB Euclidean division for `c > 0` gives
`b + t = c*d + r`, with `0 <= r < c`. Thus both `q = d + 1` and `q + 1`
satisfy `c*x - b >= t`. They are consecutive integers, so at most one equals
`p`. At the other value the `ite` selects `b`, the comparison is true, and its
negation is false. Therefore the universal assertion is false regardless of
`a`.

The search route:

1. independently recognizes the narrow shape in `qinst_egraph`;
2. substitutes `q` and `q + 1` for `x`, producing two ordinary instances;
3. returns `Unsat` only if the existing QF solver refutes the ground assertions
   plus both instances.

The evidence route does not call that matcher or the QF solver. It re-peels a
nonempty, unique, all-`Int` universal prefix and requires:

- exactly `not (>= lhs t)`;
- exactly `lhs = c*x - ite(x = p, a, b)`, accepting only the IR's subtraction
  or addition-with-`-1` spelling;
- `c > 0` and `x` among the binders;
- no binder in `p`, `a`, `b`, or `t`, and no other binder occurrence in the
  body.

The typed certificate records the original assertion, active binder,
coefficient, pivot, both branches, and threshold. Rechecking regenerates those
fields from the caller's original arena and compares the complete certificate.

## Evidence

- The committed cvc5 regression is declared `unsat` and is the measured next
  row in the 12-file quantified-LIA slice.
- The two-candidate argument above is total over all integer values and does
  not depend on a finite search bound or model guess.
- The positive coefficient is load-bearing: it supplies the Euclidean
  remainder bound and ensures affine growth toward positive infinity.
- Two consecutive candidates are load-bearing: a single candidate can equal
  the pivot and select the unconstrained then branch.
- Five focused integration tests pass: the real target solves and carries
  checked evidence; a tampered coefficient is rejected; a satisfiable
  binder-dependent near miss is not certified; both quantifier fallbacks
  terminate on a five-binder near miss; and 64 symbolic positive cases plus 64
  satisfiable binder-dependent controls agree with statically linked Z3.
- The fresh 12-row release corpus run moves 5/12 to 6/12 solely by deciding
  `repair-const-nterm` in about 1.3 ms. All six decisions match cvc5's committed
  statuses (`DISAGREE=0`), with no errors or model-replay failures.
- The six-decision evidence audit reports certified 4/6, rechecked 6/6, zero
  mismatches/errors/timeouts, and `int-affine-growth-unsat` on the target with
  no trust steps. Lean UNSAT remains 0/5, so no division dominance is claimed.

## Alternatives

- **Add a large numeric constant.** Rejected: no finite constant dominates an
  arbitrary free integer `b`.
- **Use only `div(b+t,c)+1`.** Rejected: it may equal `p`, selecting arbitrary
  `a` and leaving the assertion satisfiable at that instance.
- **Implement virtual infinity or general Presburger MBP first.** This is the
  strategic destination, but it is substantially larger than the measured
  row. The exact schema is additive and does not misrepresent itself as that
  engine.
- **Trust the two generated instances as evidence.** Rejected: it would trust
  the search matcher and recreate the evidence debt ADR-0095 closed.

## Consequences

- `repair-const-nterm` can become a fast, checked quantified-LIA `Unsat`
  decision if the ground solver validates the instances.
- The schema stays deliberately narrow; nested Boolean quantifiers, arbitrary
  piecewise arithmetic, non-positive coefficients, and binder-dependent branch
  terms still decline.
- This adds a second reusable targeted-CEGQI proof pattern while leaving broad
  arithmetic CEGQI/MBP and Lean reconstruction open.
- The accepted slice does not imply general arithmetic CEGQI or MBP; those
  remain required for broader Pareto coverage.

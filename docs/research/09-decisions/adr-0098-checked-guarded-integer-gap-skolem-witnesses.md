# ADR-0098: Checked guarded unit-gap Skolem witnesses

Status: accepted
Date: 2026-07-11

## Context

The next measured P2.6 quantified-LIA row is cvc5's
`sygus-infer-nested.smt2`:

```text
forall x y. x <= y + 1 or exists z. y < z and z < x
```

The corpus census called this a piecewise-Skolem problem, but the original
formula shows that diagnosis is too broad. One affine witness works globally:
`z := y + 1`. When `x <= y + 1`, the guard is true. Otherwise
`y + 1 < x`, while `y < y + 1` always holds. This argument uses only ordered
addition, so the same theorem and witness are valid over `Int` and `Real`.

The current witness search and ADR-0096 checker require a prenex
`forall* exists` prefix, so neither can use an existential in positive position
under `or`. cvc5 handles the regression with nested pre-skolemization plus its
SyGuS-inference preprocessing
(`references/cvc5/src/preprocessing/passes/sygus_inference.cpp` and
`preSkolemQuantNested`). Z3 has general nested-quantifier pulling machinery in
`references/z3/src/ast/normal_forms/pull_quant.cpp`. Axeyum should add the
sound positive-position extraction boundary, but must still preserve its
trusted-small original-query replay rule.

## Decision

Permit untrusted witness search to pull one direct existential through a binary
positive `or`, and extend `QuantifiedSkolemSatCertificate` checking with an
independent exact checker for the guarded unit-gap theorem.

The search transformation is:

```text
guard or exists z. body(z)  <=>  exists z. guard or body(z)
```

provided `z` does not occur in `guard` and the binder's `Int` or `Real` domain
is nonempty. Search may then reuse the existing affine bound synthesis and QF
validity sub-check. This transformation only proposes a witness; it does not
certify the result.

The independent checker accepts exactly a nonempty, unique universal prefix
whose body, modulo swapping the two `or` children and the two `and` children,
is one consistently `Int`- or `Real`-sorted instance of:

```text
upper <= successor
or
exists z. z > lower and z < upper
```

It additionally requires:

- the existential binder is distinct from every universal binder;
- `lower`, `upper`, and `successor` contain only universal symbols and no
  quantifier;
- affine normalization proves `successor = lower + 1`;
- the certificate witness contains only universals, has the existential's
  `Int` or `Real` sort, and affine normalization proves `witness = successor`.

Those checks prove the original nested assertion directly. The checker does
not call the search transformation, witness-validity sub-solver, or broad
solver stack. The existing prenex affine/reflexive theorem boundary is
unchanged. The shared certificate payload is an arena-stable affine recipe over
original-arena atoms, rather than a synthesized clone-local `TermId`.

## Evidence

- The ordered-addition proof is exhaustive: either `upper <= lower + 1`, or
  its negation implies `lower + 1 < upper`; `lower < lower + 1` is
  unconditional over both SMT-LIB `Int` and `Real`.
- The unit margin in the guard is load-bearing. A merely dense-order theorem
  with guard `upper <= lower` would need a different witness over `Real` and
  is false over `Int` when `upper = lower + 1`.
- A witness chosen only from one strict bound is already proposed by the
  existing synthesis (`z > lower` gives `lower + 1`); the missing boundaries
  are positive nested-existential extraction and original-formula checking.
- The target, `Real` analogue, tampered witness, missing-unit-margin, negative
  polarity, and untouched-original-arena replay tests pass. A deterministic
  64-seed static-Z3 sweep varies `Int`/`Real`, affine lower bounds, and child
  order; all positive cases agree, and 32 integer missing-margin negatives are
  rejected by Axeyum and refuted by Z3.
- Fresh release measurement of the 12-row quantified-LIA slice is 7/12
  (sat 2, unsat 5, unknown 1, unsupported 4), `DISAGREE=0`, with no errors or
  model-replay failures. The seven-decision audit checks 7/7 and certifies 5/7;
  both SAT rows are dominant candidates with zero trust holes. Lean UNSAT is
  still 0/5 and two older UNSAT rows remain bare, so division dominance is not
  claimed.

## Alternatives

- **Add a piecewise `ite` witness.** Rejected for this row: `lower + 1` works in
  both guard regions, so an `ite` would add certificate surface without
  capability.
- **Blindly prenex every nested quantifier.** Rejected: polarity changes under
  `not`/implication and mixed quantifiers require a real NNF/QSAT transform with
  proof bookkeeping.
- **Trust the search-side QF validity result.** Rejected: it would violate the
  original-query replay contract established by ADR-0096.
- **Extend the generic Boolean-affine checker until it proves arbitrary
  Presburger tautologies.** Deferred: that is a broader checked proof calculus,
  not necessary for this measured theorem.

## Consequences

- `sygus-infer-nested` becomes a checked SAT row without an empty model or a
  fabricated piecewise interpretation.
- Positive `or`-nested existential extraction becomes reusable untrusted search
  plumbing, while public credit remains limited by independently implemented
  certificate schemas.
- General nested quantifier pulling, gap witnesses without the exact unit
  guard, multiple existentials, arbitrary Boolean polarity, serialization,
  and Lean reconstruction remain open.
- The remaining incomplete quantified-LIA row is nested-QE UNSAT
  `issue4433-nqe`; the four Boolean-heavy rows remain unsupported.

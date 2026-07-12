# ADR-0095: Checked Euclidean-residue quantifier evidence

Status: accepted
Date: 2026-07-11

## Context

The first counterexample-guided quantified-LIA increment decides the cvc5
`clock-3` and `clock-10` regressions by instantiating

```text
forall s m. k*m + s != t or s < 0 or s >= k
```

at `s := mod(t,k)` and `m := div(t,k)`, for a positive constant `k`. Search is
sound because it builds a genuine universal instance and transfers `unsat` only
after the ordinary quantifier-free solver refutes that instance. However,
`produce_evidence` would otherwise record the result as bare `Unsat(None)`: the
new quantifier-instantiation reduction would have no independently checkable
artifact, contrary to the foundational DAG and the P2.6 proof-integration gate.

The question is whether to generalize the Alethe quantifier calculus immediately,
trust the instantiation search, or add a small checker for the exact mathematical
schema that moved the benchmark.

## Decision

**Certify the exact Euclidean-residue universal with a separate structural
checker over the original IR, exposed as
`Evidence::UnsatIntEuclideanResidue`; do not trust or replay the search trace.**

The checker independently re-matches all of these conditions:

- exactly two nested `Int` universal binders;
- exactly three disjuncts: `not(k*m+s=t)`, `s<0`, and `s>=k`;
- a strictly positive integer constant `k`;
- distinct quotient/remainder binders, each used in its exact role;
- a dividend `t` containing neither binder and no nested quantifier;
- no extra disjunct, weakened bound, or alternate arithmetic shape.

For an accepted shape, SMT-LIB Euclidean integer semantics supplies the explicit
counterexample `m=div(t,k)`, `s=mod(t,k)`: recomposition holds and the remainder
lies in `[0,k)`, so every disjunct is false. `Evidence::check` re-runs this
checker against the original assertions and compares the regenerated certificate
byte-for-byte at the typed-ID level. The evidence carries no trust-ledger step.

## Evidence

- The executable IR semantics already pins `IntDiv`/`IntMod` to
  `t = k*(div t k) + mod t k` and `0 <= mod t k < |k|` for `k != 0`.
- Fresh current-tree measurement moved exactly `clock-3` and `clock-10`, from
  2/12 to 4/12 quantified-LIA decisions, with no disagreement or replay failure.
- Positive tests cover both moduli; negative tests cover a weakened upper bound,
  zero modulus, and an extra true disjunct. Evidence tests require certified
  status, empty trust steps, successful re-check, and rejection of a tampered
  modulus.
- The search matcher remains in `qinst_egraph`; the evidence checker is a
  separate module with its own traversal and arity checks.

## Alternatives

- **Extend generic `forall_inst` Alethe emission through div/mod elimination.**
  Deferred, not rejected. It would be more general and is the route to external
  Carcara/Lean parity, but it also requires proving that the generated quotient,
  remainder, and linearization constraints correspond to the original symbolic
  instance. That is a larger proof-calculus increment than the two-row schema.
- **Store the chosen witness terms and re-run `check_auto`.** Rejected: this
  would make evidence depend on the same broad solver stack that produced the
  answer rather than a small independent checker.
- **Leave `Unsat(None)`.** Rejected: the result is mathematically simple enough
  to certify, and P2.6 explicitly requires proof integration after each new
  `unsat` route.
- **Broaden the matcher to affine variants or non-constant moduli.** Rejected
  until benchmark evidence and a correspondingly general checker justify the
  additional trusted surface.

## Consequences

- The two current Euclidean-residue decisions become certified, with zero
  trust-ledger holes, while ordinary `solve` keeps its replay-gated
  counterexample-instantiation architecture.
- This is an in-tree structural certificate, not yet an Alethe or Lean artifact;
  kernel reconstruction for symbolic Presburger instantiation remains open.
- Future CEGQI schemas need their own exact checker or a general checked
  instantiation calculus before they receive certified evidence credit.
- The next quantified coverage work can focus on the classified nested and
  large-Boolean blockers without carrying forward an evidence debt from this
  increment.

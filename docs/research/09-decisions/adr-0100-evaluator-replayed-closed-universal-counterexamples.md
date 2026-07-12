# ADR-0100: Evaluator-replayed closed-universal counterexamples

Status: accepted
Date: 2026-07-11

## Context

After ADR-0099, the 12-file quantified-LIA division has eight decisions and no
incomplete rows, but two UNSAT decisions still carry bare evidence:

```text
ARI176e1:
  forall U V. not (3*U = 22 + (-5)*V)

issue5279-nqe:
  forall a b. a = ite(b, 0, 1)
```

Both are false closed universal sentences. Concrete counterexamples are
`U=4,V=2` and `a=2,b=false`, respectively. The existing untrusted
`refute_closed_universal` search already proves this semantic class by replacing
the binders with fresh constants and solving the negated quantifier-free body,
but it discards the model and therefore cannot produce transferable evidence.

cvc5's nested-QE implementation and Z3's polarity-aware quantifier pulling are
broader search and transformation mechanisms. Neither is needed to check a
concrete counterexample to a closed universal sentence.

## Decision

Add a generic `ClosedUniversalCounterexampleCertificate` containing:

- the exact original top-level assertion `TermId`; and
- one `(SymbolId, Value)` binding per universal binder, in outer-to-inner order.

The untrusted producer peels a nonempty universal prefix, admits only a closed
quantifier-free scalar body, substitutes fresh constants, and asks the ordinary
QF solver for a model of the negated body. It projects the fresh-symbol values
back to the original binders and self-checks the resulting certificate before
publishing it.

The independent checker does not invoke substitution, preprocessing, or any
solver. Against the untouched original arena and assertion list it:

1. requires the carried assertion to occur as a top-level assertion;
2. peels its complete nonempty `forall` prefix and rejects duplicate binders;
3. rejects every nested quantifier, free symbol, uninterpreted-function
   application, and non-scalar binder sort;
4. requires exactly one binding per binder in the original order and requires
   each value's sort to equal the declared binder sort; and
5. evaluates the original quantifier body under those bindings and accepts only
   the exact result `Bool(false)`.

The initial scalar admission is `Bool`, `BitVec`, `Int`, and `Real`. This is an
evidence contract, not a completeness claim: unsupported values or a QF search
that returns `unknown` simply decline to produce the certificate.

## Evidence

- The two measured bare rows have explicit evaluator-checkable witnesses.
- Replaying the original body makes arithmetic normalization and Boolean/ITE
  simplification producer details rather than trusted proof steps.
- Tampered assertion IDs, binder IDs/order, values, value sorts, open bodies,
  nested quantifiers, UF applications, and true universal bodies must be
  rejected in focused tests.
- A deterministic static-Z3 differential sweep will cover generated false and
  valid closed universals before this ADR is accepted.
- Acceptance additionally requires the quantified-LIA evidence audit to move
  from 6/8 to 8/8 certified decisions with no disagreement, audit error, trust
  hole, or timeout.
- All focused checks pass, including both measured rows, value/sort/order/
  length/assertion tampering, open/nested/UF declines, and a valid universal.
  A static-Z3 sweep checks 64 generated false universals and 64 valid controls.
- Fresh release measurement remains 8/12 (sat 2, unsat 6, unsupported 4), with
  `DISAGREE=0`, no errors, and no model-replay failures. The audit checks and
  certifies 8/8 decisions; both upgraded rows carry
  `closed-universal-counterexample-unsat`, empty trust ledgers, and no audit
  error or timeout. Lean UNSAT remains 0/6.

## Alternatives

- **Add exact certificates for the two formulas.** Rejected: the common proof
  object is simply a counterexample assignment, and duplicating arithmetic and
  ITE matchers would add policy without adding assurance.
- **Store the fresh ground instance or QF proof.** Rejected: that makes the
  checker trust or reconstruct the producer's substitution. Evaluating the
  original body under original binder IDs is smaller and more direct.
- **Re-run the solver in `Evidence::check`.** Rejected: evidence checking must
  not reproduce the untrusted search engine.
- **Admit open universals.** Rejected: a binder counterexample can depend on
  free-symbol values. A complete certificate for that class would also need a
  proof that every free-symbol assignment is covered.
- **Admit nested quantifiers.** Rejected: evaluating an infinite-domain nested
  quantifier is not ground replay. ADR-0099 retains its separate checked theorem.

## Consequences

- False closed universal sentences can carry a compact zero-trust-hole UNSAT
  artifact whenever QF search finds one concrete counterexample.
- `ARI176e1` and `issue5279-nqe` can become certified without encoding their
  surface syntax as permanent theorem schemas.
- This does not implement quantifier elimination, quantifier alternation,
  open-formula CEGQI certificates, UF/function witnesses, or proof-producing
  infinite-domain validity.

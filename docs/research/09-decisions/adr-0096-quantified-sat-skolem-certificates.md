# ADR-0096: Quantified SAT Skolem certificates

Status: accepted
Date: 2026-07-11

## Context

The quantified solver already synthesizes terms for restricted
`forall x. exists z. body(x,z)` formulas and validates the substituted body with
a quantifier-free solve. Its public result is nevertheless an ordinary empty
`Model`. That model cannot replay the original assertion: the ground evaluator
correctly refuses to enumerate `Int` or `Real`, and it carries neither the
Skolem term nor a proof that the term works for every universal assignment.

This is no longer only latent API debt. The public cvc5 regression
`issue4849-nqe` is satisfiable by the identity Skolem `b := a`, but crediting that
row with an empty model triggers the benchmark's mandatory original-query replay
alarm. The open research question asks whether to add function models, a separate
quantified-SAT artifact, or weaken replay.

## Decision

**Keep `CheckResult::Sat(Model)`, extend `Model` with deterministic typed Skolem
certificates, and make a canonical model checker accept an infinite-domain
quantified assertion only when its certificate independently proves the exact
original assertion.**

The first certificate records the original assertion, its leading universal
binders, the single existential binder, and an owned affine witness recipe. The
recipe is a deterministic ordered sum of original-arena atoms with rational
coefficients plus a constant; it never stores a synthesized clone-local
`TermId`. Its
checker independently:

- re-matches the exact `forall* exists` prefix and quantifier-free body;
- checks binder identities, sorts, recipe ordering/uniqueness, integral
  coefficients for `Int`, and that every atom is quantifier-free, same-sort,
  original-arena, and contains no existential or foreign bound symbol;
- materializes and substitutes the witness only in a cloned arena, preserving
  the original arena and stable term IDs;
- proves the resulting open formula with a deliberately small partial checker:
  Boolean composition plus exact affine normalization over `Int`/`Real`, with
  syntactic reflexivity as a primitive case;
- rejects every unsupported or non-tautological shape rather than calling the
  broad solver stack.

`check_model` is the canonical SAT replay front door. It evaluates ordinary and
finite-domain assertions exactly as before, and consults a certificate only when
evaluation reports an unsupported infinite quantifier domain. Every certificate
must correspond to an original assertion and every unevaluable assertion must
have exactly one valid certificate. `Evidence::Sat` and the benchmark replay path
use this same check.

The witness search remains untrusted. A proposed term may receive `sat` credit
only after the separate certificate checker accepts it. Search and checking stay
in different modules and do not share the affine implementation.

## Evidence

- `issue4849-nqe` substitutes `b := a` into equality of two identical `ite`
  terms, reducing directly to reflexivity without an oracle or infinite-domain
  enumeration.
- Existing `forall-exists` tests exercise successor, equality, two-sided, and
  multi-parameter affine witnesses over both `Int` and `Real`; these are within
  the small checker's normalization boundary.
- The benchmark's cloned-backend lifecycle exposed and now pins the
  representation boundary: a synthesized `x+1` recipe replays against an
  untouched original arena even when that composite term exists only in the
  solver clone.
- cvc5 represents valid witnesses explicitly in
  `references/cvc5/src/proof/valid_witness_proof_generator.{h,cpp}`. Z3's model
  checker obtains Skolem interpretations and substitutes them into quantified
  bodies in `references/z3/src/smt/smt_model_checker.cpp`. Both references keep
  witness terms/model interpretations explicit rather than treating an empty
  ground assignment as a quantified model.

## Alternatives

- **Return the empty ordinary model after the search-side QF validation.**
  Rejected: callers cannot replay it, and reusing the search trace is not an
  independent check.
- **Make `eval` enumerate or sample unbounded `Int`/`Real`.** Rejected: finite
  sampling cannot establish a universal theorem and would turn a sound
  unsupported result into an unsound success.
- **Add a new `CheckResult::SatQuantified` variant.** Rejected for now: the
  certificate is part of the satisfying interpretation/evidence, and storing it
  in `Model` preserves the established backend and consumer result shape.
- **Immediately add arbitrary first-class Skolem functions and a general
  quantifier proof calculus.** Deferred, not rejected. ADR-0098 handles one
  guarded nested existential with the same global affine recipe, but genuinely
  piecewise/general witnesses still need that broader route.
- **Call `check_auto` again from the certificate checker.** Rejected: it would
  duplicate the broad search stack rather than implement trusted-small checking.

## Consequences

- Existing restricted `forall-exists` SAT results become genuinely replayable
  through the public solver checker instead of carrying unchecked empty models.
- The identity witness can soundly recover `issue4849-nqe`; malformed, stale, or
  tampered certificates fail replay.
- Direct callers that currently use `eval(model.to_assignment())` should use
  `check_model` when quantified SAT is possible. Ground and finite-domain behavior
  is unchanged.
- The certificate proves satisfiability but is not yet an Alethe/Lean artifact.
  General piecewise Skolem functions, serialization, external proof exchange,
  and kernel reconstruction remain explicit follow-up work.

# ADR-0103: Nested-XOR quantifiers to Lean

Status: accepted
Date: 2026-07-11

## Context

ADR-0099 certifies one exact nested quantified theorem:

```text
forall a b.
  xor (xor (a = pa) (b = pb))
      (forall c.
        ite(a = pa, t, e) = ite(c = pc, t, e))
```

where `t != e`. Its original-IR checker accepts harmless orientation changes:
either outer XOR child order, either selector equality order, signed constants,
and either ITE-equality operand order. `issue4433-nqe` carries this certificate
with zero trust holes, but before this ADR its Lean route declined.

The two Euclidean-residue rows need a general division/remainder theorem in the
integer prelude. This nested-XOR theorem does not: three concrete universal
applications, propositional reasoning, and adjacent-integer disequality are
enough. It is therefore the next proof increment with no arithmetic trusted-base
expansion.

## Decision

Add a public certificate-to-Lean reconstruction route for the complete checked
ADR-0099 class. It first regenerates and compares the certificate against the
untouched assertion, then:

1. translates Boolean XOR as `Not (Iff p q)`;
2. translates the checked same-branch selector equality as `Iff` of its guards
   (valid because the certificate proves both ITEs have the same distinct
   branches);
3. introduces only the original outer universal as the query hypothesis;
4. applies the active and passive pivots, proving the first XOR false;
5. uses one standard classical excluded-middle axiom to derive the nested
   universal from the outer XOR;
6. applies the nested binder at the deterministic adjacent off-pivot value; and
7. closes the resulting false guard equality with the existing integer ring and
   order axioms.

Every intermediate proof is kernel-gated against its expected proposition: the
selector `Iff`, selector falsity, normalized outer XOR, derived nested universal,
nested instance, active equality, and off-pivot disequality.

Outer witness substitution is independently materialized in a cloned arena
before translating the closed nested proposition. This is required to avoid
using still-open outer de Bruijn variables after `forall` application.

Signed SMT literals are normalized through the integer ring proof. They are not
treated as definitionally equal: `(- 4)` translates as `neg(4)`, while a carried
`-4` witness has the normalizer's repeated-negative-one representation.

## Evidence

- `issue4433-nqe` reconstructs through the public certificate API and generic
  `prove_unsat_to_lean_module` router as `ProofFragment::IntNestedXor`.
- A signed/swapped control with pivots `5`, `-4`, `3` and branches `7`, `-2`
  reconstructs, covering the complete ADR-0099 orientation contract.
- A certificate whose `then_value` is changed to `else_value` is rejected before
  proof construction.
- The initial tests caught two implementation errors rather than accepting a
  proof: a loose outer de Bruijn variable at excluded-middle admission, and a
  signed-literal type mismatch at the selector `Iff`. Both now have permanent
  stage gates.
- Acceptance requires a fresh quantified-LIA audit with Lean UNSAT 3/7 and
  dominant candidates 5/9, while evidence remains checked/certified 9/9 and
  mismatches, audit errors, timeouts, and trust holes remain zero.

## Alternatives

- **Use a certificate-refuter axiom.** Rejected for the same reason as ADR-0102:
  it kernel-checks an opaque theorem application, not the quantified proof.
- **Hard-code the exact corpus orientation.** Rejected: ADR-0099 already defines
  a reusable semantic class and its certificate accepts signed/swapped forms.
- **Translate integer ITE as a new opaque function.** Rejected: the certificate
  proves this exact same-branch selector equality is equivalent to `Iff` of the
  guards, so an opaque bridge is unnecessary.
- **Wait for a combined general Alethe quantifier/arithmetic/Boolean tail.**
  Deferred: that remains the broader architecture, but this certificate already
  supplies a small independently checked proof boundary.

## Consequences

- One more quantified-LIA UNSAT decision gains genuine kernel reconstruction
  without adding a new arithmetic theory axiom.
- The generated module depends on the input universal, the existing logic and
  integer preludes, and classical excluded middle; it has no theorem-specific
  refuter.
- Euclidean residue, affine growth, and finite equality partition remain the
  four uncredited quantified-LIA UNSAT rows.


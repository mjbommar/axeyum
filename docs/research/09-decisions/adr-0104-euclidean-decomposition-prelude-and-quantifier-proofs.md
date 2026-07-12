# ADR-0104: Euclidean decomposition prelude and quantifier proofs

Status: accepted
Date: 2026-07-11

## Context

After ADR-0103, four quantified-LIA UNSAT rows lack Lean reconstruction. Two are
the ADR-0095 Euclidean-residue theorem:

```text
forall s m. k*m+s != t or s<0 or s>=k
```

for positive literal `k`. A genuine proof must obtain quotient/remainder
witnesses for an arbitrary free dividend `t`. Declaring query-specific witness
constants and assumptions would merely replace a certificate-refuter axiom with
three equally opaque query-specific premises.

The current `IntPrelude` is a discretely ordered commutative ring. It has enough
ring/order machinery to close the three instantiated disjuncts once a Euclidean
decomposition is available, but it intentionally has no division, remainder, or
general division-algorithm theorem.

## Decision

Extend `IntPrelude` with one standard integer theorem and no new operations:

```text
euclidean_decomposition :
  forall t k, 0 < k ->
    exists q, exists r,
      t = k*q+r /\ 0<=r /\ r<k
```

This is a genuine theorem of `Z`, so adding it preserves the consistency
argument from ADR-0042: the standard integers remain a model of every prelude
axiom. The kernel type-checks the theorem's dependent type at admission. The
theorem is intentionally existential rather than exposing `div`/`mod` function
symbols; the proof needs witness existence, not a public computational
division API or total-by-zero semantics.

Add a certificate-specific Lean reconstruction route for the canonical
ADR-0095 spelling used by `clock-3` and `clock-10`. It must:

1. regenerate and compare the original-IR certificate;
2. encode the original universal over the arbitrary dividend constant;
3. apply `euclidean_decomposition` to the positive literal modulus;
4. eliminate both existential witnesses;
5. instantiate the original universal with remainder/quotient in binder order;
6. project recomposition and both bounds from the conjunction; and
7. eliminate the three-way disjunction, contradicting each branch by equality
   or order irreflexivity.

The first Lean slice may decline harmless syntactic orientations accepted by
the evidence checker; public evidence remains broader than public proof
reconstruction. Broadening requires proof tests for each orientation and must
not silently canonicalize the input hypothesis without a proof.

## Acceptance

- Prelude tests infer the exact theorem type; query tests reject malformed
  witness/bound variants before proof construction.
- `clock-3` and `clock-10` reconstruct through both the certificate API and the
  generic router.
- A tampered modulus is rejected before proof construction, and satisfiable or
  weakened controls do not reconstruct.
- A fresh audit reports Lean UNSAT 5/7 and dominant candidates 7/9, with evidence
  checked/certified 9/9 and zero mismatches, audit errors, timeouts, or trust
  holes.
- Workspace Clippy, warning-denied rustdoc, links, foundational resources, and
  the established focused solver/evidence/bench test split pass before this ADR
  becomes accepted; any known whole-aggregate blocker is recorded explicitly.

## Alternatives

- **Add `div` and `mod` operations plus recomposition/bound axioms.** Rejected:
  it expands the public proof vocabulary and must specify total zero-divisor
  semantics, while these proofs only need existential witnesses.
- **Declare local quotient/remainder constants with three assumptions.**
  Rejected: those assumptions are query-specific theorem bridges and do not
  reduce proof trust.
- **Use the executable ADR-0095 checker as a refuter axiom.** Rejected: evidence
  replay and kernel reconstruction remain separate assurance layers.
- **Derive Euclidean division from the existing ring/discreteness axioms in the
  tiny kernel.** Deferred: mathematically possible but requires induction/
  well-order infrastructure far beyond this bounded reconstruction increment.

## Consequences

- The integer trusted prelude grows by one explicit, standard theorem. This is a
  real trusted-base change and is recorded as such, unlike ADR-0102/0103.
- The same theorem can support the affine-growth proof later without adding
  division functions.
- Arbitrary-modulus, noncanonical-orientation, and computational div/mod proof
  surfaces remain out of scope.

## Validation

- The integer-prelude test applies `euclidean_decomposition` at an abstract
  dividend and checks its inferred type is definitionally equal to the exact
  nested quotient/remainder existential with recomposition and both bounds.
- `clock-3` and `clock-10` reconstruct through the direct certificate API and
  generic proof router as `IntEuclideanResidue`; a tampered modulus and a
  satisfiable weakened upper bound are rejected.
- Fresh release audit artifact:
  `/tmp/axeyum-quant-lia-adr0104-audit.json`. All 9 decided rows are evidence
  checked and certified; Lean checks 5/7 UNSAT rows and 7/9 decisions are
  dominant candidates. Mismatches, audit errors, timeouts, and trust holes are
  all zero.
- No external `lean` executable was installed on the validation host, so the
  generated source was checked by the in-tree Lean kernel and renderer but not
  by an additional Lean subprocess.
- Focused all-feature reconstruction tests pass 3/3; integer-prelude tests 6/6;
  solver library 829/829; evidence 69/69; bench 7/7; capability/support goldens
  2/2 and 12/12. Workspace all-target/all-feature Clippy, warning-denied
  rustdoc, links, formatting/diff hygiene, and foundational resources (137
  concepts, 174 packs) pass. The pre-existing Sturm nontermination still
  prevents a whole-workspace aggregate claim.

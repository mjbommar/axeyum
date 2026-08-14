# ADR-0452: Balanced Nat Bézout certificates

Status: accepted

Date: 2026-08-14

Requirements: [Lean kernel requirements](../../plan/lean-kernel-requirements-2026-08-13.md), R4.8 (Bézout layer).

## Context

ADR-0449 supplied an executable, well-founded Euclidean gcd; ADR-0450 bridged
divisibility across executable remainders; and ADR-0451 proved the gcd common-
divisor characterization. R4.8 next requires Bézout before Gauss's lemma.

The existing integer prelude is intentionally assumption-bearing. Using it for
the coefficients would add unrelated ordered-ring axioms to the zero-axiom Nat
lane. Pinned Lean 4.30 contains a partial `Int.gcdExt` tactic utility, but not a
kernel theorem suitable for this prelude. The Rado reconstruction likewise
used an authored concrete Bézout witness; it did not discover or supply the
missing reusable general theorem.

## Decision

Represent signed coefficients by positive and negative natural parts:

```text
bezout m n g :=
  exists mp mn np nn,
    g + m*mn + n*nn = m*mp + n*np

gcd_bezout : forall m n, bezout m n (gcd m n)
```

This is exactly the integer identity
`g = m*(mp-mn) + n*(np-nn)` without defining signed subtraction or choosing a
normal form for coefficient pairs. It is a certificate relation, not a claim
that the four witnesses are unique or minimal.

Prove `gcd_bezout` with `WellFounded.fix` over gcd's first input. The zero case
uses `(mp,mn,np,nn) = (0,0,1,0)`. In a successor step, let
`n = d*q + r` be the checked equation from `div_mod_exec`. From recursive
coefficients `(rp,rn,dp,dn)` for `(r,d)`, construct coefficients for `(d,n)`:

```text
d-positive = dp + q*rn
d-negative = dn + q*rp
n-positive = rp
n-negative = rn
```

The proof expands both sides with checked distributivity, reassociates and
permutes finite sums with checked commutative-monoid laws, applies the recursive
equation, and transports the result through `gcd_succ`. Add the generally useful
`right_distrib` theorem, derived from `mul_comm` and `left_distrib`, for the
substitution `n*c = (d*q+r)*c`.

No classical choice is used: all four existential witnesses are introduced and
eliminated explicitly. No paper-specific positivity or coprimality hypothesis
is present, and the all-zero case is included.

## Evidence

The focused kernel suite admits the complete prelude with zero axioms and checks
the general theorem at `gcd 10 15` and `gcd 0 0`. An independent explicit
certificate checks `5 + 10*0 + 15*1 = 10*2 + 15*0`, demonstrating the balanced
relation's intended signed meaning. A mutation reuses `gcd_bezout 10 15` after
changing the second generator to 14; the trusted declaration gate rejects it.

The deterministic declaration inventory contains 19 definitions and 117
theorems after this increment. Repository-wide gates and exact-main publication
remain release conditions for the implementation commit, not premises of this
decision.

## Consequences

The zero-axiom Nat prelude now exposes a reusable Bézout existence theorem for
every pair of naturals. Later proofs can eliminate the certificate directly,
while an executable extended-gcd API may refine the witness representation
without changing this semantic contract.

R4.8 remains incomplete: Gauss's lemma and its cancellation consequence are not
claimed. The next number-theory increment should derive Gauss from
`gcd_bezout`, multiplication/distributivity, and divisibility elimination.

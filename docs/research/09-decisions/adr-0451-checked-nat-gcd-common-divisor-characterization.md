# ADR-0451: Checked Nat gcd common-divisor characterization

Status: accepted

Date: 2026-08-14

Requirements: [Lean kernel requirements](../../plan/lean-kernel-requirements-2026-08-13.md), R4.8 (gcd semantic layer).

## Context

ADR-0449 defined executable Euclidean gcd and checked its unfolding equations.
ADR-0450 then supplied the all-Nat divisibility algebra and `dvd_mod_iff` needed
to reason across each recursive remainder. Computation and termination alone do
not establish that the output is a greatest common divisor; the universal
property must be proved in both directions.

The Rado reconstruction reached the same trust boundary in a concrete setting:
authored Bézout witnesses and case decompositions checked, but missing reusable
library steps remained `unknown`. The correct response is a general theorem
over every natural input and common divisor, including zero, rather than a
certificate specialized to the paper's positive coprime parameters.

## Decision

Add the zero-axiom theorems:

```text
gcd_dvd       : forall m n, gcd m n | m and gcd m n | n
gcd_dvd_left  : forall m n, gcd m n | m
gcd_dvd_right : forall m n, gcd m n | n
dvd_gcd       : forall k m n, k | m -> k | n -> k | gcd m n
dvd_gcd_iff   : forall k m n, k | gcd m n <-> k | m and k | n
```

Prove `gcd_dvd` and `dvd_gcd` independently with `WellFounded.fix` over the
first input and checked strict Nat well-foundedness. Their successor cases call
the recursive proof only at `mod n (succ m)`, justified by `mod_lt`.

For `gcd_dvd`, the recursive gcd divides the divisor and remainder;
`dvd_mod_iff` carries remainder divisibility forward to the dividend. For
`dvd_gcd`, divisibility of the dividend and divisor carries backward through
`dvd_mod_iff`, supplying the two recursive hypotheses. Both proofs transport
the recursive result through `gcd_succ`. Their zero cases transport explicitly
through `gcd_zero_left` and use `dvd_zero` / `dvd_refl` as appropriate.

Finally, derive the projections by conjunction elimination. The forward half
of `dvd_gcd_iff` composes an arbitrary divisor of gcd with both projections by
`dvd_trans`; the reverse half applies `dvd_gcd` to the conjunction fields.

## Evidence

At `gcd 10 15`, the kernel checks the exact conjunction saying the computed gcd
divides both inputs. Explicit factors prove `5 | 10` and `5 | 15`; `dvd_gcd`
then checks `5 | gcd 10 15`. `dvd_gcd_iff` infers at the same inputs and at the
all-zero corner.

A mutation reuses the valid `gcd_dvd 10 15` proof while changing its right-hand
input from 15 to 14. The trusted gate rejects the changed statement with
`DeclarationValueMismatch`. All declarations join deterministic rendering,
strict all-feature Clippy, complete kernel tests, real-Lean replay,
warning-denied rustdoc, axiom-ledger, and parity-contract gates.

## Consequences

`Nat.gcd` now has its standard mathematical universal property, not merely an
executable name. This completes the gcd sublayer needed before Bézout and Gauss
and gives later number-theory algorithms a reusable, all-Nat semantic API.

R4.8 remains incomplete: no Bézout coefficients or Gauss lemma are claimed.
The next layer should define a checked extended-Euclidean witness relation and
prove existence without importing signed host arithmetic into the Nat prelude.

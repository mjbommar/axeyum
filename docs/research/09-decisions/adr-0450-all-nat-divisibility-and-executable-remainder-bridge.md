# ADR-0450: All-Nat divisibility and executable remainder bridge

Status: accepted

Date: 2026-08-14

Requirements: [Lean kernel requirements](../../plan/lean-kernel-requirements-2026-08-13.md), R4.3 and R4.8 dependencies.

## Context

ADR-0449 added checked Euclidean gcd computation but intentionally did not call
the result a greatest common divisor. The pinned Lean proof of that semantic
characterization depends on `dvd_mod_iff` in both directions. Axeyum had
divisibility introduction and addition, but lacked reflexivity, zero,
transitivity, multiplication closure, all-Nat additive cancellation, and the
remainder bridge.

The Rado reconstruction experience makes this distinction material. Authored
case data and Bézout witnesses were useful, but the checker correctly returned
`unknown` where the general library was absent. Specializing a divisibility
argument to the paper's positive parameters would repeat that limitation and
would leave gcd incorrect at zero corners.

## Decision

Add zero-axiom checked theorems for:

```text
dvd_refl                 : dvd a a
dvd_zero                 : dvd a 0
dvd_trans                : dvd a b -> dvd b c -> dvd a c
dvd_mul_right_of_dvd     : dvd a b -> dvd a (b*c)
dvd_add_iff_right        : dvd k m -> (dvd k n <-> dvd k (m+n))
dvd_mod_iff              : dvd k (succ d) ->
                           (dvd k (mod n (succ d)) <-> dvd k n)
```

The additive reverse implication must hold for `k = 0`; it therefore cannot
reuse the older positive-divisor cancellation theorem. Add the unconditional
truncated identity

```text
b * (q-a) = b*q - b*a
```

by Nat-order totality. The already checked bounded theorem handles `a <= q`;
when `q <= a`, both differences reduce propositionally to zero using
multiplication monotonicity. Also prove `(m+n)-m = n` by restoration,
commutation, and additive cancellation. Existential factors for `m` and `m+n`
then yield their difference as a factor for `n` without deciding whether `k`
is zero.

For a successor divisor, `div_mod_exec` supplies
`n = divisor*quotient+remainder`. Multiplication closure makes the first summand
divisible by `k`; `dvd_add_iff_right` removes it in both directions. Equality
transport identifies the reconstructed sum with the executable dividend.

## Evidence

The trusted gate admits and renders all eight new theorems. Tests exercise the
reverse-order truncated branch `3*(2-5)`, compose `2 | 6 | 18`, instantiate
additive cancellation at divisor zero, and check the exact executable statement
`2 | (6 mod 4) <-> 2 | 6`. A mutation substitutes `6 / 4` for `6 mod 4`; the
kernel rejects the valid bridge proof against that changed statement with
`DeclarationValueMismatch`.

The declarations remain in the zero-axiom Nat prelude and join deterministic
rendering, strict all-feature Clippy, full kernel tests, real-Lean replay,
warning-denied rustdoc, axiom-ledger, and parity-contract gates.

## Consequences

The exact reusable bridge used by Lean's Euclidean gcd induction is now
available over all possible common divisors, including zero. The next increment
can prove that computed gcd divides both inputs and that every common divisor
divides computed gcd, then package the two directions as `dvd_gcd_iff`.

This ADR does not establish gcd semantics, Bézout, Gauss, or R4.8 completion.

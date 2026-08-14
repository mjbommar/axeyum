# ADR-0449: Checked well-founded Euclidean gcd computation

Status: accepted

Date: 2026-08-14

Requirements: [Lean kernel requirements](../../plan/lean-kernel-requirements-2026-08-13.md), R4.8 (partial).

## Context

ADR-0441--0445 supplied native accessibility, generic well-founded recursion,
its checked unfolding equation, and reducible well-foundedness of strict Nat
order. ADR-0447--0448 supplied executable quotient and remainder projections
and proved their relational Euclidean specification. The next reusable
number-theory layer is an executable gcd whose recursive decrease is visible to
the checker.

The Rado reconstruction work is a warning against replacing this layer with a
host-computed result or a theorem specialized to one witness. Its externally
authored case tree and Bézout data were useful evidence, while the missing
general checked library correctly remained `unknown`. Gcd should therefore be
an ordinary zero-axiom prelude definition with general checked equations,
independent of any one downstream certificate.

## Decision

First add the theorem

```text
Nat.mod_lt : forall k n, Nat.mod n (Nat.succ k) < Nat.succ k
```

by eliminating the conjunction produced by `Nat.div_mod_exec` and retaining
its remainder bound. Then define `Nat.gcd m n` in the same first-argument
orientation as pinned Lean:

```text
gcd 0 n       = n
gcd (succ k) n = gcd (mod n (succ k)) (succ k)
```

The definition is `WellFounded.fix Nat.lt Nat.lt_well_founded`, with family
`fun _ => Nat -> Nat`. Its successor step invokes the recursive function only
at `mod n (succ k)` and supplies `Nat.mod_lt k n` as the required decrease.
There is no host recursion, comparison, or admitted termination fact.

Expose the two equations as checked theorems `Nat.gcd_zero_left` and
`Nat.gcd_succ`. Both are pointwise consequences of
`WellFounded.fix_eq`; equality between the resulting `Nat -> Nat` functions is
applied to the second argument using `Eq.rec`.

## Evidence

The kernel checks the exact type of `mod_lt` at `6 mod 4`. Closed reduction
computes `gcd 0 5 = 5`, `gcd 10 15 = 5`, and `gcd 7 0 = 7`, covering the base
case, multiple Euclidean steps, and a zero second argument. A mutation applies
the valid successor-equation proof to a statement that substitutes quotient
for remainder; admission is rejected with `DeclarationValueMismatch`.

The definition and three theorems join the promised-name,
deterministic-render, zero-axiom, strict all-feature Clippy, full kernel-test,
warning-denied rustdoc, and pinned Lean replay gates.

## Consequences

Axeyum now has a general executable Euclidean algorithm whose termination and
unfolding are checked inside the zero-axiom Nat development. It exercises the
well-founded recursion foundation with a nontrivial algorithm and makes later
division/number-theory reconstruction independent of host gcd computation.

This is only the computational part of R4.8. No greatest-common-divisor
characterization has yet been proved: common-divisor preservation, maximality,
Bézout, and Gauss remain absent. The next increment must establish the reusable
divisibility semantics before any theorem is credited merely because closed
gcd examples compute.

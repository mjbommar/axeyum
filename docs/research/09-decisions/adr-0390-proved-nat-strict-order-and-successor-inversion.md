# ADR-0390: Proved Nat strict order and successor inversion

Status: accepted

Date: 2026-08-13

Requirements:
[`lean-kernel-requirements-2026-08-13.md`](../../plan/lean-kernel-requirements-2026-08-13.md),
R4.1 / R7.1.

## Context

The Rado sharpness witness must establish that several explicit naturals lie in
`[N]`. Its proof uses strict facts such as `N > ab` as well as non-strict
bounds. The Nat prelude already represented `le` by Lean's indexed inductive
shape and proved successor monotonicity, but it could neither state strict
order under a shared name nor invert a bound whose two endpoints are
successors.

The requirements correctly identify successor inversion as a predecessor-style
motive problem. This does not require a public predecessor function: `Nat.rec`
can construct the proposition family that is `False` at zero and `Le n x` at
`succ x`. The existing `Le.rec` can then eliminate the bound derivation into
that family.

## Decision

**Extend the zero-axiom Nat prelude with the reducible definition
`Nat.lt n m := Nat.le (Nat.succ n) m` and the checked theorem
`Nat.le_of_succ_le_succ`.**

The inversion proof uses this family:

```text
P 0        = False
P (succ x) = Le n x
```

The reflexive `Le (succ n) (succ n)` case reduces to `Le n n`. In the step
case, a derivation `Le (succ n) x` combines with the constructor proof
`Le n (succ n)` through the already checked `le_trans`, yielding `Le n x`.
The induction hypothesis is structurally present but unnecessary.

Both names join the exact transactional Nat package. The definition is checked
as a definition, the inversion term as a theorem, and neither is an axiom.

## Evidence contract

- `Nat.lt 2 4` must be definitionally equal to `Nat.le 3 4`.
- Lifting `1 <= 3` with `le_succ_succ` and then applying inversion must produce
  another kernel-checked proof of exactly `1 <= 3`.
- Relabelling that valid inverted proof as `4 <= 2` must be rejected, and the
  rejected declaration must not enter the environment.
- The full package snapshot, repeat-build identity, rollback, and zero-axiom
  checks remain mandatory.

## Alternatives

### Define a public predecessor first

Rejected for this slice. A predecessor-style proposition family is sufficient
for inversion, while a public predecessor would begin R4.2's subtraction API
without yet supplying its cancellation contract.

### Define strict order independently

Rejected. `lt n m := succ n <= m` matches the intended Nat semantics and makes
all existing `le` derivations and the inversion theorem directly reusable.

### Admit inversion as an axiom

Rejected. The indexed recursor already proves it constructively; admitting it
would weaken the Nat prelude's zero-axiom research boundary for no benefit.

## Consequences

The strict-order and successor-inversion slice of R4.1 is available to every
consumer, including the range side of `thm:sharp`. R4.1 remains **WIP**:
antisymmetry, totality, and `min` are still absent. This decision adds no
subtraction, cancellation, interval type, finite sum, colouring definition, or
Rado theorem credit.

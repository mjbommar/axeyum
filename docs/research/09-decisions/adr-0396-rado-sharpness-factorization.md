# ADR-0396: Rado sharpness factorization

Status: accepted

Date: 2026-08-13

Requirements: [Lean kernel requirements](../../plan/lean-kernel-requirements-2026-08-13.md), R4.6 / R7.1.

## Context

The proof of `thm:sharp` in `../axeyum-rado-paper` writes, for `k >= 3`,

`u = a * [1 + 2 * (a + ... + a^(k-3)) + a^(k-2)]`.

Let `n = k-3`, let `S1(n)` sum powers `a^(i+1)` for `i<n`, and let `S2(n)`
sum `a^(i+2)`. The subtraction-free equality needed before defining `u` is

`a * (1 + (2*S1(n) + a^(n+1))) = a + (2*S2(n) + a^(n+2))`.

At `k=3`, `n=0` and both finite sums are empty. Previous test-local
`geo`/`geo1` recurrences demonstrated related arithmetic but were not the
generic `Nat.sumRange` statement used by the paper proof.

## Decision

Admit a Rado-development theorem with the exact subtraction-free equality
above, universally quantified over `a` and `n`. Keep it in a dedicated
integration development rather than naming a paper-specific theorem in the
generic Nat prelude.

Construct the proof from the checked prelude only:

- `mul_sumRange` moves `a` inside `S1`;
- pointwise `mul_comm` and `pow_succ`, lifted by `sumRange_congr`, identify the
  scaled sum with `S2`;
- `left_distrib`, `mul_assoc`, `mul_comm`, `mul_one`, and `pow_succ` normalize
  the surrounding expression.

## Evidence

The integration suite admits the universal theorem, applies its `n=0` empty
corner, and checks the nonempty `a=3,n=2` instance by kernel reduction to 156
on both sides. It walks the environment and finds zero axioms. A mutation
control drops the leading `a` from the right side at `a=2,n=0`, turning `6=6`
into `6=4`; the trusted gate rejects the valid proof against that false goal
without insertion.

## Consequences

The exact finite-sum factorization named as `thm:sharp`'s first real cost is
checked. The paper theorem is not complete: constructing `u=N/b-a`, `X`, and
their range proofs requires truncated subtraction/cancellation and order
lemmas; divisibility connects the shell length to `N/b`; colour obligations
remain explicit. No theorem credit is claimed.

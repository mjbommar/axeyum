# Fibonacci coprimality premise plan

Date: 2026-08-19

## Result

The proof shape is bounded, and the first composition seam is now closed through
the public theorem-only API. Axeyum's axiom-free `Nat.zero_add`, `Nat.succ_add`,
and `Nat.add_comm` proofs compose into the imported Mathlib environment with a
replayable receipt. Translated definitional equality resolves the first
order-wrapper differences, and atomic singleton composition reconstructs the
absent `Exists` package. The next root now stops at definition `Nat.mul`.

The exact `r082` train stream imports 261 declarations and 52 theorems with no
axioms. It contains `Nat.rec`, but none of the seven native lemmas required by
the bounded proof. Calling `build_nat_prelude` wholesale still rejects at the
first overlapping logic declaration, `True`, with `DeclarationExists`; selected
theorem-only composition avoids granting that rejected bulk operation authority.

## Bounded proof shape

Induct on `n`. The base reduces Fibonacci at zero and one and uses
`Nat.gcd_zero_left`. For the step, rewrite `fib (n + 2)` with the admitted
`Nat.fib_add_two` theorem and name the new gcd `d`. Its two projection facts say
that `d` divides `fib (n + 1)` and the sum. Additive divisibility cancellation
then gives `d ∣ fib n`; `Nat.dvd_gcd` gives
`d ∣ gcd (fib n) (fib (n + 1))`; the induction hypothesis transports this to
`d ∣ 1`; and `Nat.eq_one_of_dvd_one` closes the goal.

This deliberately avoids requiring a new general theorem equating two gcds.
The sole admitted theorem premise is `Nat.fib_add_two`; the remaining seven
items are axiom-free native library theorems.

## Actual blocker and sequence

The completed first increment followed this order:

1. Recover typed prelude handles from existing imported logic and Nat
   declarations.
2. Compare every overlap structurally and fail closed on a type, value,
   recursor, or universe mismatch.
3. Add only missing native theorems, transactionally, so a failed composition
   cannot leave a half-extended environment.
4. Reproduce the selected three-theorem slice through a public completed-clone
   API and bind its exact receipt.

The next increment must rebuild the demanded `Nat.mul` definition's type,
value, universe parameters, and reducibility exactly in the private target,
submit it through the ordinary target gate, and bind both source and target
identities. Opaque, conflicting, and unsupported definitions must decline.

This is the holistic point: theorem search cannot use the library until the
library and imported target share one checked environment. Solving this seam
also benefits every later Mathlib target that needs native arithmetic facts.

## Evidence

The current read-only observation is
`/nas3/data/axeyum/autogenesis/probes/fced2b166-singleton-inductive-composition-v9/observation.json`.
It binds the public API, exact source closure, reused declaration identities,
added theorem identities, environment transition, and composition receipt. The
history is recorded in
[the first checked native-library composition](57-first-native-nat-composition.md),
the promoted boundary in
[public checked theorem composition](58-public-checked-theorem-composition.md),
and the next compatibility result in
[translated definitional reuse](59-translated-definitional-reuse.md), followed
by [atomic singleton-inductive composition](60-atomic-singleton-inductive-composition.md).
Verify the tracked plan and its authority boundary with:

```sh
python3 scripts/check-autogenesis-nat-fib-coprime-premise-plan.py
```

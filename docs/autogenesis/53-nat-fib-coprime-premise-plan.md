# Fibonacci coprimality premise plan

Date: 2026-08-19

## Result

The proof shape is now bounded, but execution is blocked before proof search by
an architectural seam: Axeyum's axiom-free Nat theorem library cannot yet be
composed into an imported Mathlib environment.

The exact `r082` train stream imports 261 declarations and 52 theorems with no
axioms. It contains `Nat.rec`, but none of the seven native lemmas required by
the bounded proof. Calling `build_nat_prelude` on that kernel rejects at the
first overlapping logic declaration, `True`, with `DeclarationExists`.

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

The next implementation should proceed in this order:

1. Recover typed prelude handles from existing imported logic and Nat
   declarations.
2. Compare every overlap structurally and fail closed on a type, value,
   recursor, or universe mismatch.
3. Add only missing native theorems, transactionally, so a failed composition
   cannot leave a half-extended environment.
4. Replay the seven-lemma surface in `r082` before authorizing any target proof
   submission.

This is the holistic point: theorem search cannot use the library until the
library and imported target share one checked environment. Solving this seam
also benefits every later Mathlib target that needs native arithmetic facts.

## Evidence

The current read-only observation is
`/nas3/data/axeyum/autogenesis/probes/d1eb38a13-fib-coprime-prelude-compatibility-v2/observation.json`.
It extends the original rejection receipt with a fail-closed overlap census;
the interpretation and next boundary are recorded in
[the alpha-stable compatibility result](54-alpha-stable-prelude-compatibility.md).
Verify the tracked plan and its authority boundary with:

```sh
python3 scripts/check-autogenesis-nat-fib-coprime-premise-plan.py
```

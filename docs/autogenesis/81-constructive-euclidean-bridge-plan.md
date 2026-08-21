# Constructive official Euclidean bridge plan

Date: 2026-08-20

## Decision

The `Nat.gcd_fib_add_self` lane will repair the broad foundation exposed by the
second support rather than import a convenient target theorem or equate two
same-named declarations. The fixed route independently reconstructs an
official-target Euclidean equation, uses it to rebuild balanced Bézout over the
official gcd, and only then replays coprime-factor cancellation.

This is a new support-only increment. It does not enlarge the original target
submission budget: both exact r091 target submissions remain reserved, and
this bridge plan permits zero target submissions.

## Why descend another layer

The statement-only Lean 4.30 inventory contains exactly the public equation we
need:

```text
Nat.div_add_mod : forall m n, n * (m / n) + m % n = m
```

But the earlier kernel audit measured `propext` in the official proof. Importing
that proof would enlarge the trusted footprint. Native Axeyum proves the same
mathematics through `Nat.div_mod_exec`, but official Lean uses that name for an
incompatible computational declaration, so name equality supplies no bridge.

The constructive layer below both is a synchronized quotient/remainder fuel
computation. Official Lean exposes generated equations for `Nat.div.go`,
`Nat.modCore.go`, and the public `Nat.mod` wrapper. The remainder equations are
already retained with empty footprints; the division root must be independently
exported, audited, and declined if its footprint is not empty.

## Fixed stages

1. Audit `Nat.div.go.eq_1`, `Nat.modCore.go.eq_1`, and `Nat.mod.eq_2` without
   inspecting proof bodies.
2. Prove a joint fuel invariant: divisor times quotient plus remainder equals
   the original dividend.
3. Lift it through the official wrappers, including the zero-divisor case, and
   require the resulting theorem type to match `Nat.div_add_mod` exactly.
4. Re-author balanced-natural Bézout over the official target gcd using that
   equation and target `Nat.mod_lt`.
5. Replay the already accepted cancellation algebra against the target-side
   Bézout theorem and require its type to match the native support.

Every authored theorem reconstructs twice, exposes its direct dependencies,
and must have an empty kernel-derived footprint. A failure discards the private
kernel and ends the increment without target credit.

## Ceiling and horizon

The bridge permits one equation-root audit and four support declarations, each
reconstructed twice: at most eight new kernel theorem submissions. It permits
no retries, executor invocation, exact target submission, semantic receipt,
evaluation credit, or ledger write.

If this succeeds, the next bounded increment can compose both support types
into r091 and spend the two already reserved submissions on the original
Fibonacci gcd-shift theorem. Beyond that target lies `Nat.fib_gcd`; the bridge
is deliberately reusable so later number-theory work inherits a constructive
Euclidean/Bézout base rather than another theorem-specific adapter.

## Verification

```sh
python3 scripts/check-autogenesis-nat-gcd-fib-add-self-euclidean-bridge-plan.py
python3 -m unittest \
  scripts.tests.test_check_autogenesis_nat_gcd_fib_add_self_euclidean_bridge_plan
```

The machine-readable route and authority ceiling are in
[`mathlib-nat-gcd-fib-add-self-euclidean-bridge-plan-v1.json`](../../artifacts/autogenesis/mathlib-nat-gcd-fib-add-self-euclidean-bridge-plan-v1.json).

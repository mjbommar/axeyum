# Official-gcd balanced-Bézout reconstruction plan

Date: 2026-08-21

## Decision

Reconstruct the existing four-natural balanced Bézout carrier directly over the
official `Nat.gcd` surface, but keep the two gcd computation equations as
explicit theorem parameters. Checked specialization can then supply Axeyum's
already reconstructed empty-footprint `Nat.gcd_zero_left` and `Nat.gcd_succ`
instead of importing the official assumption-bearing proofs.

The key representation correction is that Bézout does not require the public
quotient function. The accepted private joint invariant can witness

```text
exists q, m * q + n % m = n
```

through the clean public remainder equation `Nat.mod.eq_2`. The quotient stays
private and existential. This bypasses the opaque `/` wrapper and the declined
`Nat.div_add_mod`, `Nat.div_eq`, and `Nat.mod_eq` routes entirely.

## Fixed execution

The authored source and accepted private invariant are copied under the pinned
Mathlib 4.30 package root on `s5`, compiled once each, and exported once. The
raw proof stream remains unreadable to the model. Axeyum's batch auditor reads
it exactly twice in fresh kernels and measures both `modQuotientWitness` and
`officialGcdBalancedBezout`.

The exact three-file pre-existing checkout baseline must match before copying
and after exact cleanup. Those files may not be opened, changed, or removed.

## Acceptance and boundary

Both measured theorems must reconstruct twice with matching identities, empty
kernel-derived footprints, and no dependency on public quotient equations,
official gcd-equation proofs, or official xgcd coefficients. A compile failure
or first-import failure ends the increment without retry.

Even acceptance establishes only the generic theorem. It does not authorize
closed specialization, cancellation, an exact Fibonacci submission, receipt,
evaluation credit, fact mutation, or ledger write. The next increment must
preregister specialization with the already checked target gcd leaves.

## Verification

```sh
python3 scripts/check-autogenesis-official-gcd-balanced-bezout-reconstruction-plan.py
python3 -m unittest \
  scripts.tests.test_check_autogenesis_official_gcd_balanced_bezout_reconstruction_plan
```

# Official-kernel balanced-Bézout composition plan

Date: 2026-08-21

The prior closed attempt mixed an official generic theorem with a native-support
kernel and failed at a real `WellFounded.fix` representation mismatch. Both gcd
computation leaves have now been reconstructed independently inside the official
Mathlib representation, so this increment keeps every component on that side of
the boundary.

A dedicated driver will import five sealed streams: the official r082 base for
`Nat.mod_lt`, the accepted `modLtSucc` adapter, the new zero-left and successor
roots, and the generic balanced-Bézout theorem. It will compose only those named
roots, specialize the modulo bound and successor theorem under fresh names, and
then specialize the generic theorem with the two fresh official-representation
leaves.

Two complete fresh invocations must be byte-identical. Every composition and
specialization must replay, all three new theorem footprints must be empty, and
the final direct dependencies must be exactly the generic theorem, fresh
zero-left theorem, and fresh closed successor theorem. Native `Nat.gcd_*`, fix
equations, and extensionality dependencies are forbidden.

No cancellation, Fibonacci target, fact transition, evaluation, or ledger
authority is granted by this plan.

```sh
python3 scripts/check-autogenesis-official-gcd-balanced-bezout-official-kernel-plan.py
python3 -m unittest \
  scripts.tests.test_check_autogenesis_official_gcd_balanced_bezout_official_kernel_plan
```

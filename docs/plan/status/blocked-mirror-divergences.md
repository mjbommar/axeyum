# Lane: blocked-mirror-divergences — the 4 structurally-blocked `ml430` causes

<!-- plan-section: lane-status -->

**Your lane's block (`IN PROGRESS`, blocked-mirror-divergences, 2026-08-30).**

Initial commit — research phase, no kernel code changed yet. This file will
be updated as work lands. Recording the state of the investigation early per
the standing "commit within first 10 tool calls" rule.

## Starting facts, verified in-tree

- `Nat.multichoose` (3 facts) and `Nat.minFac` (1 fact): **already fully
  resolved by prior lanes** (`docs/plan/status/241-nat-minfac-relprime.md`,
  `250-nat-fastfib-minfac.md`, `239`-era multichoose work). Local Nat-valued
  analogue facts exist and are `proved` (`F:nat-multichoose-one`,
  `F:nat-multichoose-one-right`, `F:nat-multichoose-zero-right`,
  `F:nat-coprime-of-lt-minfac`), and the corresponding `ml430` mirrors
  correctly stay `open`. Verifying the Mathlib-source reading myself before
  writing this up as final.
- `Nat.testBit` (5 facts): 2 of 5 already resolved the same way
  (`lt_of_testbit` -> `F:nat-lt-of-testbit`, `zero_of_testbit_eq_false` ->
  `F:nat-zero-of-testbit-eq-zero`, both `proved`). 3 remain fully open with
  NO local analogue yet: `testbit_land`, `testbit_lor`, `testbit_ldiff`.
  `docs/plan/status/244-nat-testbit-bitwise.md` already worked out the full
  proof route for these three in detail. `testbit_eq_inth` needs `Nat.bits :
  List Bool` -- this kernel has no `List` type at all, on top of the
  Bool/Nat codomain mismatch; deepest-blocked of the five.
- `Nat.fastFib` (1 fact): the codebase's own `Nat.binaryRec` (fuel-based,
  `nat_prelude/binary_rec.rs`) is NON-dependent (`alpha` fixed, not varying
  in `n`), and Mathlib's `fastFibAux : Nat -> Nat x Nat` uses `binaryRec`
  with a motive that is ALSO non-dependent (`fun _ => Nat x Nat`, confirmed
  by reading `Mathlib/Data/Nat/Fib/Basic.lean` at the pinned commit). So the
  "fuel forces non-dependence" obstruction that blocks a GENERAL dependent
  `binaryRec` does not actually block THIS specific mirror -- investigating
  further before committing to this being fully closeable this session.

Work continues below as it lands.

<!-- plan-section: landed-changes -->

| 2026-08-30 | blocked-mirror-divergences | Initial research commit; no kernel code yet |

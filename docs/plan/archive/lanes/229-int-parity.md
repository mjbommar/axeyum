# Lane: int-parity — Int.Odd/Int.Even via natAbs, then Int.fib_of_odd

<!-- plan-section: lane-status -->

**Your lane's block (DONE, int-parity, 2026-08-28).** Landed `Int.Even`/`Int.Odd`
(`int_prelude/parity.rs`, new module), defined as `Nat.Even`/`Nat.Odd (natAbs n)`
rather than a fresh `Int`-level existential — magnitude alone decides parity,
and this composes for FREE with `natAbs`'s pure reduction on both `Int.rec`
constructors (confirms the earlier lane's prediction exactly). Two bridge
theorems (`odd_iff_nat_abs_odd`, `even_iff_nat_abs_even`, both near-tautological
`fun h => h` proofs) and `Int.fib_of_odd` (`int_prelude/fibonacci.rs`) all landed
and are kernel-checked with empty axiom footprints. `Int.fib_of_odd`'s ofNat
branch is free (unused hypothesis, both sides reduce to the same term); the
negSucc branch needed one new induction, `pow_neg_one_add_self` (same technique
as the file's existing `pow_neg_one_two_mul`, over the `k+k` witness shape
`Nat.Even` uses instead of `mul 2 k`, since `add(succ k)(succ k)` does not
reduce purely the way `mul two (succ k)` does — bridges via an explicit
`succ_double_eq_nat` equation lifted to `Int`). No new `Int`-level parity lemma
was needed for the proof itself, exactly as predicted.

Concrete instantiation tests with genuine positive AND negative witnesses at
BOTH signs (`Int.Odd 3`/`-3` inhabited, `Not (Int.Odd 4)`/`-4` proved) —
`int_odd_applies_at_concrete_values_of_both_signs`,
`fib_of_odd_applies_at_a_concrete_odd_index_of_each_sign`
(`int_prelude_tests.rs`). `int_prelude::` test count: 38 -> 40 (all pass).
`derived_laws` 147 -> 150, `definition_names` 25 -> 27 (pinned arrays,
recounted not incremented). `cargo fmt --all --check` and
`cargo clippy -p axeyum-lean-kernel --all-targets -- -D warnings` both clean.
`python3 scripts/validate-facts.py`: 0 errors, 1913 facts.

New facts: `F:int-even`, `F:int-odd` (the two definitions), `F:int-odd-iff-nat-abs-odd`,
`F:int-even-iff-nat-abs-even` (the bridge theorems). `F:ml430-int-fib-of-odd-66560495`
flipped `open` -> `proved` with a real kernel-checked proof (not a mirrored
transcription of Mathlib's tactic proof, which was never consulted).

Next lane: nothing else in this task's scope is open. `Int.Even`'s own bridge
theorem (`even_iff_nat_abs_even`) has no consumer yet — it was built for a
symmetric, discoverable API pair per the brief, not because anything currently
needs it.

<!-- plan-section: landed-changes -->

| 2026-08-28 | int-parity | `Int.Even`/`Int.Odd` via `natAbs`, two bridge theorems, `Int.fib_of_odd`, all axiom-free; `F:ml430-int-fib-of-odd-66560495` proved |

# Lane: countrange-bijection — the `countRange`-invariance primitive under Euler's totient

<!-- plan-section: lane-status -->

**IN PROGRESS.** Initial commit: survey only, no declarations yet.

## Survey so far

`Nat.countRange` (`nat_prelude/totient.rs`) is structural `Nat.rec` on `n`.
Existing companions: `countRange_zero/_succ/_congr/_split/_le/_le_of_le/
_le_of_subset/_compl/_union_add_inter/_succ_of_true/
_eq_pred_of_only_zero_false/_ge_two_of_two_witnesses/_reversal_even`.
**No bijection-invariance in any form** — consistent with `320`'s finding.

Machinery that exists and should compose: `Nat.permInverse` +
`permInverse_left`/`_right` (`permutation.rs`, an EXPLICIT computable
inverse — this is what makes the primitive reachable),
`Nat.transposition`/`_injective`/`_involutive`/`_maps_into`
(`transposition.rs`), `Nat.injective_on_imp_surjective_on` (`finite.rs`),
`Nat.crt_unique` (`nat_prelude/crt.rs`, Nat-native).

## Next

Settle the exact statement and the induction route; numeric-check in Python
before any Rust.

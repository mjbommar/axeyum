# Lane: nat-parity-lowbit — the parity <-> low-bit bridge, then `Nat.even_xor`

<!-- plan-section: lane-status -->

**Your lane's block (`DONE (bridge landed; Nat.even_xor landed and closes
F:ml430-nat-even-xor-78a39432; Nat.lt_xor_cases stays open)`,
nat-parity-lowbit, 2026-08-29).**

## What landed

### 1. The bridge: `Nat.even_iff_mod_two_eq_zero` / `Nat.odd_iff_mod_two_eq_one`

`nat_prelude/parity.rs`:

```
Nat.even_iff_mod_two_eq_zero : ∀ n, Iff (Even n) (Eq (mod n 2) 0)
Nat.odd_iff_mod_two_eq_one   : ∀ n, Iff (Odd n)  (Eq (mod n 2) 1)
```

Neither half of this existed anywhere in the prelude, inline or otherwise
(checked: `parity.rs`'s own module doc said so, and `binary.rs`'s seven
`mod _ 2` sites use `Lt r 2` only as a bound, never split). Built fresh,
not extracted:

- `mp` (`Even n -> Eq (mod n 2) 0`): eliminate the existential
  (`Exists.rec`, the same shape `declare_even_not_odd` already uses) to
  `k, hk : Eq n (add k k)`, then a `d.chain` rewriting `mod n 2` through
  `hk`, a new `mul_two_eq_add_self` conversion (`k+k` <-> `mul two k`, via
  `succ_mul`/`one_mul` — the exact inline technique `binary.rs`'s
  `n_lt_mul_two` already uses for a `Lt` conclusion, extracted here as a
  standalone equality), an `add_zero` insertion, and a new
  `mod_two_mul_add_of_lt` helper closing the last step.
- `mpr` (`Eq (mod n 2) 0 -> Even n`): `div_mod_exec` gives
  `n = add (mul two (div n 2)) (mod n 2)`; substitute the hypothesis,
  simplify, convert to `add`-form via `mul_two_eq_add_self`, hand the
  result to `Exists.intro` at witness `div n 2`.
- The `Odd` twin needs one more piece, `succ_eq_add_one`
  (`Eq (succ a) (add a one)`, via `add_succ`/`add_zero` reversed) to
  bridge `succ(k+k)` and `add (mul two k) 1`.

Detail moved to [`../notes/254-nat-parity-lowbit.md`](../notes/254-nat-parity-lowbit.md).

<!-- plan-section: landed-changes -->

| 2026-08-29 | nat-parity-lowbit | Landed the parity <-> low-bit bridge (`Nat.even_iff_mod_two_eq_zero`/`Nat.odd_iff_mod_two_eq_one`, new `mod_two_mul_add_of_lt` helper, `nat_prelude/parity.rs`) and `Nat.even_xor` (new `nat_prelude/xor_parity.rs`), closing `F:ml430-nat-even-xor-78a39432` via a new native `F:nat-even-xor`; `F:ml430-nat-lt-xor-cases-c43a1e85` stays open (needs a highest-differing-bit `testBit` induction this technique gives no foothold for) |

# Notes: 371-pow-add-prime

Detail moved out of [`../status/371-pow-add-prime.md`](../status/371-pow-add-prime.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

Registered in `nat_prelude_tests.rs`'s environment-derived coverage list
(`theorem_names`) and confirmed via
`every_nat_declaration_is_checked_and_axiom_free`. Full `nat_prelude::` sweep:
**208 passed, 0 failed** (was 204 before this lane; +3 theorems +1 new test).
`cargo fmt --all --check` and `clippy -p axeyum-lean-kernel --all-targets -D
warnings` both clean.

**What did NOT land, and why**: the fact itself. Two pieces are still needed
and neither is attempted here:

1. "`n` is not a power of two ⟹ `n` has an odd factor `d > 1`" — a 2-adic
   valuation argument (extract the odd part of `n` via strong/well-founded
   recursion). Nothing in this session builds it; `Nat.even_or_odd`
   (`powsq.rs`) is the closest existing primitive but stops at one bit, not
   an iterated valuation.
2. The final contradiction: given `d*e = n`, `d` odd `> 1`, show
   `dvd_pow_add_one_of_odd_mul_exp` exhibits a divisor `a^e+1` that is
   neither `1` nor `a^n+1` (needs `e < n` from `d > 1`, and `a^e+1 > 1` from
   `a > 1`, both easy order facts — not done here), then plug into
   `prime_condition`'s `∀ c, c ∣ x → c = 1 ∨ c = x` to derive `False`.

Bridging `dvd_pow_add_one_of_odd_exp`'s `succ (mul 2 t)` exponent shape to
`Nat.Odd`'s own witness shape (`succ (add t t)`) needs only
`two_mul_eq_add_self` (`powsq.rs`, module-private today) — cheap, not done
here since nothing downstream needs it yet.

**For the next lane**: piece 1 above is the harder of the two remaining
pieces and is a genuine well-founded-recursion undertaking (`Nat.gcd`,
`Nat.bezout_witnesses`, `Nat.modeq`, `Nat.wilson` all already use
`WellFounded.fix` in this kernel — see CLAUDE.md's "NO FUEL ENCODING CAN BE A
DEPENDENT RECURSOR" entry for why a fuel encoding here is the wrong tool).
Piece 2 is comparatively short standard order-theory bookkeeping once piece 1
exists.

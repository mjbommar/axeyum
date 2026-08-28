# Lane: nat-cascade — the choose/coprime cascade six facts unblocked by choose.rs/primes.rs

<!-- plan-section: lane-status -->

**Your lane's block (`DONE`, nat-cascade, 2026-08-28).** All six targeted
facts landed, all kernel-checked and axiom-free (`nat` trusted surface = 0
throughout). `nat_prelude::` went 95 -> 96 passed, 0 failed.

Two of the six turned out to be thin corollaries once mirrored against the
just-landed prerequisites, exactly as the brief predicted: `choose_symm_add`
(one call to `choose_symm_of_eq_add` with `n := a+b` and `refl` for the
hypothesis) and `coprime_of_dvd` (two-step composition of
`coprime_of_dvd_right` then `coprime_of_dvd_left`, no new algebra). The other
four needed real construction:
- `choose_le_add` — induction on `b`, chaining `choose_le_succ` through
  `le_trans` (both cases defeq via `add`'s definitional zero/succ equations).
- `coprime_self_add_right` — `coprime_add_self_right` transported along
  `add_comm` to swap which side of the sum carries `m`.
- `coprime_symmetric` — **no `gcd_comm` lemma existed in the prelude** (the
  brief's "check whether a `gcd_comm` already closes this" came back
  negative); built directly via mutual `gcd_dvd_left`/`gcd_dvd_right` +
  `dvd_gcd` + `dvd_antisymm`.
- `coprime_or_dvd_of_prime` — decided constructively via a local `Bool.rec`
  case split on `beq (gcd p i) one` (mirrored from `totient.rs`'s private
  `bool_true_or_false` helper, duplicated since it is module-private) plus
  `prime_dvd_iff_not_coprime`'s reverse direction. **Not Bezout**, matching
  the brief's warning about the earlier coprime lane.

Kernel rejected nothing on the first accepted attempt for any of the six —
every proof term type-checked once written, so no bisection was needed.

Newly unblocked but out of scope for this lane: `F:ml430-nat-choose-le-choose-907b5042`
(needs `choose_le_add`, now available) and `F:ml430-nat-coprime-of-lt-prime-1978a919`
(needs `coprime_or_dvd_of_prime`, now available).

<!-- plan-section: landed-changes -->

| 2026-08-28 | nat-cascade | `Nat.choose_le_add`, `Nat.choose_symm_add` proved (`nat_prelude/choose.rs`); pinned `65+331`->`65+333` in `the_build_is_deterministic` |
| 2026-08-28 | nat-cascade | `Nat.coprime_of_dvd`, `Nat.coprime_self_add_right`, `Nat.coprime_symmetric`, `Nat.coprime_or_dvd_of_prime` proved (`nat_prelude/primes.rs`); pinned `65+333`->`65+337` |

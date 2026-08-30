# Lane: parity-coprime — `Coprime 2 n ↔ Odd n` and the two facts the last cascade left

<!-- plan-section: lane-status -->

**Your lane's block (`DONE`, parity-coprime, 2026-08-28).** All six targeted
facts landed, all kernel-checked and axiom-free (`nat` trusted surface = 0
throughout). `nat_prelude::` went 96 -> 98 passed, 0 failed.

Two facts were cheap: `F:ml430-nat-choose-le-choose-907b5042` needed one new
declaration (`choose_le_choose`, monotone-in-the-row-index, via `choose_le_add`
transported along an additive witness extracted from `Le a b` by
`sub_add_cancel`). `F:ml430-nat-coprime-of-lt-prime-1978a919` needed no new
Rust at all — `declare_coprime_of_lt_prime` (`nat_prelude/primes.rs`) had
already been admitted to the kernel in an earlier commit (`de2e39eee`), via a
direct route that does not actually go through `coprime_or_dvd_of_prime`
despite the fact's recorded `depends_on` edge naming it (that edge predates
the direct proof and was never revisited). Found already-proved, status
flipped, no re-derivation.

The substantive piece, `F:ml430-nat-coprime-two-left-1b47e7c4` (`Coprime 2 n
↔ Odd n`), needed real construction: `2` is prime (a private `prime_two`
helper rebuilding `prime_condition(2)`), `coprime_or_dvd_of_prime` splits
`gcd 2 n = 1 ∨ dvd 2 n`, `prime_dvd_iff_not_coprime` relates `dvd 2 n` to
`Not (gcd 2 n = 1)`, and a private bridge (`even_of_dvd_two`/
`dvd_two_of_even`, via a rebuilt `2*k = k+k` identity) connects `dvd 2 n` and
`Even n` so `even_or_odd_exists`/`even_not_odd` can rule out the even case in
each `Iff` direction. `coprime_two_right`, `coprime_odd_of_left`,
`coprime_odd_of_right` were thin corollaries once `coprime_two_left` existed,
exactly as the brief predicted.

**Did NOT need `add_self_ne_succ_add_self`** (the brief flagged it as a
likely dependency) — the whole construction routes through `dvd`/`gcd`
machinery instead of directly comparing two existential witnesses, so that
theorem never came up.

Detail moved to [`../notes/191-parity-coprime.md`](../notes/191-parity-coprime.md).

<!-- plan-section: landed-changes -->

| 2026-08-28 | parity-coprime | `Nat.choose_le_choose` proved (`nat_prelude/choose.rs`); pinned `67+342`->`67+343` in `the_build_is_deterministic` |
| 2026-08-28 | parity-coprime | `Nat.coprime_of_lt_prime` fact flipped to proved (already admitted pre-existing kernel declaration, no new Rust) |
| 2026-08-28 | parity-coprime | `Nat.coprime_two_left`, `Nat.coprime_two_right`, `Nat.Coprime.odd_of_left`, `Nat.Coprime.odd_of_right` proved (`nat_prelude/primes.rs`); pinned `67+343`->`67+347` |

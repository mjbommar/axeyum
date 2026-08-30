# Notes: 184-coprime-backlog

Detail moved out of [`../status/184-coprime-backlog.md`](../status/184-coprime-backlog.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

Bézout was **not** the engine here (contrary to the brief's guess) --
`Coprime.of_dvd_{left,right}` and `prime_dvd_iff_not_coprime` all went
through plain divisibility algebra (`gcd_dvd_left/right`, `dvd_trans`,
`dvd_gcd`, `eq_one_of_dvd_one`, and for the prime fact the same
`le_of_dvd`/`le_of_succ_le_succ`/`not_succ_le_zero` numeral-contradiction
shape `coprime_of_lt_prime` already uses); `coprime_add_self_right` went
through `dvd_antisymm` (`dvd_add`, `dvd_add_iff_right`, `add_comm`). Bézout
machinery (`bezout.rs`) was read but not needed for any of the four.

Nothing was already built for these four -- checked `bezout.rs`, `crt.rs`,
`primes.rs`, `lcm.rs`, `irrational.rs`, `perfect.rs` first (per the brief);
none had `dvd_trans`-based coprimality descent or the `gcd`-`Iff`-`add_comm`
shape `coprime_add_self_right` needed, though all the LEMMAS consumed
(`dvd_trans`, `dvd_gcd`, `eq_one_of_dvd_one`, `dvd_add_iff_right`, `dvd_add`,
`dvd_antisymm`) already existed and were simply composed.

`cargo test -p axeyum-lean-kernel --lib nat_prelude::`: **94 -> 96** passed,
0 failed (added one concrete-numeral application test covering all four
theorems, plus fixed the two environment-derived coverage/determinism tests
that failed once the new theorems went live). `cargo clippy -p
axeyum-lean-kernel --lib -- -D warnings`: clean. `python3
scripts/validate-facts.py`: 1867 facts, 0 errors.

# draw11-theorems-b

## Status: in progress (2026-08-31)

Frontier measured at start (python3 scripts/check-dispatchable-frontier.py):
23 DISPATCHABLE, including the two (`and_or_distrib_left/right`) a sibling
lane already closed -- skipped per brief.

Working set selected (7 of the remaining 21):
- F:ml430-nat-coprime-lcm-eq-mul-edf52888 -- already proved under
  `Nat.coprime_lcm_eq_mul` (lcm.rs). Fact-ledger only, no new Rust.
- F:ml430-nat-dvd-dvd-nat-lcm-left-6143311e -- already proved under
  `Nat.dvd_lcm_of_dvd_right` (primes.rs). Fact-ledger only.
- F:ml430-nat-dvd-dvd-nat-lcm-right-d05db50b -- already proved under
  `Nat.dvd_lcm_of_dvd_left` (primes.rs). Fact-ledger only.
- F:ml430-nat-add-one-mul-choose-eq-d364de16 -- new: `succ_mul_choose_eq`
  read backwards + `mul_comm`. New file `nat_prelude/draw11_mirrors.rs`.
- F:ml430-nat-coprime-eq-of-mul-eq-zero-a2026bd5 -- new: `mul_eq_zero` case
  split + `gcd_zero_left`/`gcd_comm` substitution.
- F:ml430-nat-coprime-dvd-mul-left-e799d04c -- new: `gauss_lemma` (mp) +
  `dvd_mul`/`mul_comm`/`dvd_trans` (mpr), packaged as an `Iff`.
- F:ml430-nat-coprime-dvd-mul-right-7cd1c3c8 -- new: symmetric route.

New Rust: `crates/axeyum-lean-kernel/src/nat_prelude/draw11_mirrors.rs`,
wired into `build_nat_prelude_uncached` after `declare_squarefree_all`
(last, needs only long-established lemmas).

In progress: `cargo check -p axeyum-lean-kernel` is green. Next: run the
`nat_prelude::` test sweep, write/update the fact JSON files, run holdout
isolation before/after, settled-fact-statement check, depends_on fixup.

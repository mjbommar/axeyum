# Lane: draw11-theorems-b — Nat theorem proofs from the ml430 mirror dispatch queue

<!-- plan-section: lane-status -->

**7 ml430 mirror facts closed, session complete** (`WIP`, draw11-theorems-b,
2026-08-31). Frontier measured at start
(`python3 scripts/check-dispatchable-frontier.py`): 23 DISPATCHABLE (two,
`and_or_distrib_left/right`, already closed by a sibling lane and skipped
per brief). Frontier at end: 16 DISPATCHABLE — 23 minus the 7 closed here.

Three already proved under a different name (fact-ledger evidence only, no
new Rust): `F:ml430-nat-coprime-lcm-eq-mul-edf52888` ==
`Nat.coprime_lcm_eq_mul`; `F:ml430-nat-dvd-dvd-nat-lcm-left-6143311e` ==
`Nat.dvd_lcm_of_dvd_right`; `F:ml430-nat-dvd-dvd-nat-lcm-right-d05db50b` ==
`Nat.dvd_lcm_of_dvd_left` (all in `nat_prelude/lcm.rs` / `primes.rs`; this
codebase spells `Coprime m n` as `gcd m n = 1` directly).

Four new theorems in the new
`crates/axeyum-lean-kernel/src/nat_prelude/draw11_mirrors.rs`, wired into
`build_nat_prelude_uncached` last (needs only long-established lemmas):
`F:ml430-nat-coprime-dvd-mul-left-e799d04c`,
`F:ml430-nat-coprime-dvd-mul-right-7cd1c3c8` (both `Iff`s: `mp` from
`gauss_lemma`, `mpr` from `dvd_mul` + `mul_comm` + `dvd_trans`),
`F:ml430-nat-coprime-eq-of-mul-eq-zero-a2026bd5` (`mul_eq_zero` case split
+ `gcd_zero_left`/`gcd_comm` substitution),
`F:ml430-nat-add-one-mul-choose-eq-d364de16` (`succ_mul_choose_eq` read
backwards + one `mul_comm`). All axiom-free (`nat` prelude trusted surface
measures 0), registered in `nat_prelude_tests.rs`'s environment-derived
`theorem_names` coverage check, each with a discriminating unit test that
applies a real witness to an inferred proof term (not just a type-shape
check).

`cargo test -p axeyum-lean-kernel --lib nat_prelude::`: 242 passed, 0
failed. `cargo clippy -p axeyum-lean-kernel --lib --all-features -- -D
warnings`: clean (the crate's `--all-targets` clippy has pre-existing
failures in unrelated `tests/*.rs`/`examples/*.rs` files this lane never
touched, confirmed pre-dating this session via `git log`).
`python3 scripts/validate-facts.py`: 2364 facts, 0 errors (proved
2152 -> 2156). `python3 scripts/check-autogenesis-holdout-isolation.py`:
PASS before and after, `settled=0 references=0`.

**Declined, not attempted:** `Nat.Coprime.mul_add_mul_ne_mul` (needs a
Nat-subtraction case split I didn't have budget to verify — difficulty,
not divergence); `Nat.fermat_primeFactors_one_lt`,
`Nat.Squarefree.ext_iff` (need more supporting infrastructure than fit the
remaining budget — unsized, not divergence); the `add_choose`/
`descFactorial`/`ascFactorial`/factorial-growth family, 8 facts
(`nat_prelude/choose.rs` has a close relative,
`desc_factorial_eq_factorial_mul_choose`, but none of the eight are a
direct corollary — each needs a genuine new induction, not attempted for
time); `Int.exists_gcd_one` (x2), `Int.gcd_dvd_iff` (Int-side gcd/Bezout
infrastructure exists in `int_prelude/gcd.rs`/`bezout.rs` but I did not
check how close these three are — unsized).

**Next step for a future lane:** re-run the frontier script before
dispatching — this file is a snapshot, not authority. By my reading
`Nat.Coprime.mul_add_mul_ne_mul` is the most promising unattempted target
(bounded casework, one `b ≤ m` split), though I didn't finish sizing it.

<!-- plan-section: landed-changes -->

| 2026-08-31 | `757afb706` | New `nat_prelude/draw11_mirrors.rs`: 4 theorems (coprime_dvd_mul_left/right, coprime_eq_of_mul_eq_zero, add_one_mul_choose_eq), each with a discriminating concrete-instance test. |
| 2026-08-31 | `e00c2500e` | Close 3 ml430 lcm/coprime mirrors already proved under another name (fact-ledger evidence only). |
| 2026-08-31 | `5410c49f9` | Close 4 ml430 mirrors with the new draw11_mirrors.rs proofs (fact-ledger evidence). |

# Lane: nat-gcd — closing the `natural-gcd` import-backlog family via the divisibility characterization of `Nat.gcd`

<!-- plan-section: lane-status -->

**Your lane's block (`DONE`, nat-gcd, 2026-08-28).** Closed 9 of the 12 open
`natural-gcd` facts (all `development`, none `held-out` — verified against
`nursery-v1.json` before starting). All 9 proofs go through the
divisibility characterization (`gcd_dvd_left`/`gcd_dvd_right`/`dvd_gcd`/
`dvd_antisymm`/`eq_one_of_dvd_one`, plus `dvd_lcm_left`/`dvd_lcm_right`/
`dvd_trans` for the lcm ones) — **none needed to unfold `Nat.gcd`'s
well-founded recursion**, so none hit the `Quot.sound` wall the brief warned
about.

Landed, each independently kernel-verified and axiom-free (`nat` trusted
surface stays 0):

- `Nat.not_coprime_zero_zero : ¬ gcd 0 0 = 1` — `gcd_zero_left` gives
  `gcd 0 0 = 0`; `succ_ne_zero` refutes `0 = 1`.
- `Nat.coprime_one_left_iff : gcd 1 n = 1 ↔ True` and
  `Nat.coprime_one_right_iff : gcd n 1 = 1 ↔ True` — `gcd_dvd_left`/
  `gcd_dvd_right` plus `eq_one_of_dvd_one` give the equation
  unconditionally.
- `Nat.coprime_add_self_left : gcd (m+n) n = 1 ↔ gcd m n = 1` — swap both
  sides of `coprime_add_self_right(n, m)` through `coprime_symmetric`.
- `Nat.coprime_self_add_left : gcd (m+n) m = 1 ↔ gcd n m = 1` —
  `coprime_add_self_left(n, m)` transported along `add_comm`, the same
  congruence-transport shape `coprime_self_add_right` uses.
- `Nat.dvd_lcm_of_dvd_left` / `Nat.dvd_lcm_of_dvd_right` — `dvd_trans`
  through `dvd_lcm_left`/`dvd_lcm_right`.
- `Nat.dvd_of_lcm_left_dvd` / `Nat.dvd_of_lcm_right_dvd` — `dvd_trans`
  through `dvd_lcm_right`/`dvd_lcm_left` composed with the hypothesis.

All 9 declared in `nat_prelude/primes.rs` (kept there rather than in
`gcd.rs`, matching the file's own existing convention: every other
`Coprime`-shaped lemma — `coprime_of_dvd_left/right`, `coprime_symmetric`,
`coprime_add_self_right`, `coprime_self_add_right` — already lives in
`primes.rs`, not `gcd.rs`; `gcd.rs` owns only `Nat.gcd`'s definition and its
raw `gcd_dvd_*`/`dvd_gcd`/`dvd_gcd_iff` characterization). The 4
lcm-transitivity lemmas also went into `primes.rs` rather than `lcm.rs`,
since `lcm.rs` was explicitly out of scope (read-only) for this lane — they
only *consume* `p.lcm`/`p.dvd_lcm_left`/`p.dvd_lcm_right`/`p.dvd_trans`
through the shared `NatPrelude` fields, `lcm.rs` itself is untouched.

`nat_prelude` count: **73 + 369 = 442 before, 73 + 378 = 451 after** (9 new
theorems, 0 new definitions), read off `the_build_is_deterministic`'s own
panic message, not hand-counted.

**Not attempted, and why:**
- `F:ml430-mutation-c20db9b4c60b816ce738bdf2` (`Nat.Coprime 0 0`, an
  "outcome-blind mutation" of `not_coprime_zero_zero`) is **false**
  (`gcd 0 0 = 0 ≠ 1`). Proving it would be a soundness violation, so it was
  left untouched — closing it is not this lane's job (if the mutation
  harness expects a refutation route instead of a proof, that is a separate
  mechanism this lane did not investigate).
- `F:ml430-nat-coprime-iff-isRelPrime-0c08eb25` needs an `IsRelPrime`
  predicate; grepped the whole crate (`grep -rn "IsRelPrime"
  crates/axeyum-lean-kernel/src/`) and confirmed it does not exist anywhere
  in this kernel. Out of scope to introduce a new predicate for one fact.
- `F:ml430-nat-div-dvd-div-left-b56f6f7c` (`m∣k → n∣m → k/m ∣ k/n`) needs
  real `Nat.div` reasoning (write `k = m·p`, `m = n·q`, cancel through
  `div_mul_cancel_of_dvd`) — feasible but genuinely more involved than the
  divisibility-characterization route above, and budget went to the 9
  landed instead. Not attempted; no partial work left behind.

Verified: `cargo test -p axeyum-lean-kernel --lib nat_prelude` — 107
passed, 0 failed (confirmed nonzero, not a filtered subset).
`cargo clippy -p axeyum-lean-kernel --all-targets -- -D warnings` clean.
`rustfmt --edition 2024` on all three touched files: no changes (already
formatted). `python3 scripts/validate-facts.py`: 0 errors. Each of the 9
new `checker_command`s independently re-run and confirmed to depend on the
finding (exits nonzero against a bogus name, per
`nat_theorem_inventory`'s own fail-on-absence design).

<!-- plan-section: landed-changes -->

| 2026-08-28 | nat-gcd | 9 `natural-gcd` facts closed via the divisibility characterization of `Nat.gcd`/`Nat.lcm` (0 axioms) |

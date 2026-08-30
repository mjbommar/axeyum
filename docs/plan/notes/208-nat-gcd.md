# Notes: 208-nat-gcd

Detail moved out of [`../status/208-nat-gcd.md`](../status/208-nat-gcd.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

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

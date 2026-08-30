# Lane: nat-parity-div — the parity / division-by-two mirror cluster

<!-- plan-section: lane-status -->

**Your lane's block (`DONE for this dispatch`, nat-parity-div, 2026-08-30).**
Closed 7 of 10 dispatched mirrors plus flipped 1 pre-existing (see landed-changes).
3 remain open with named blockers below. All work is direct Nat-level kernel
construction (not Int carrier transports — see
`crates/axeyum-lean-kernel/src/nat_prelude/parity_div.rs`'s module doc for why
the `ofNat`/`natAbs` bridge from the `Int` siblings turned out costlier).

Verification run: `cargo test -p axeyum-lean-kernel --lib nat_prelude::` — 211
passed, 0 failed (was 204 before this lane). `clippy -D warnings` clean on
`-p axeyum-lean-kernel --all-targets --all-features`. `rustfmt --edition 2024
--check` clean. `python3 scripts/validate-facts.py` — 2265 facts, 0 errors.
`python3 scripts/check-mirror-statement-fidelity.py` — verdict=PASS.

**Closed (new kernel theorems, `nat_prelude/parity_div.rs`):**
- `Nat.div_two_mul_two_of_even : Even n -> n/2*2 = n`
  (`F:ml430-nat-div-two-mul-two-of-even-9ccc5340`)
- `Nat.div_two_mul_two_add_one_of_odd : Odd n -> n/2*2+1 = n`
  (`F:ml430-nat-div-two-mul-two-add-one-of-odd-9e3e8b82`)
- `Nat.add_one_lt_of_even : Even n -> Even m -> n<m -> n+1<m`
  (`F:ml430-nat-add-one-lt-of-even-3464b374`)
- `Nat.odd_of_mul_left : Odd (m*n) -> Odd m` (`F:ml430-nat-odd-of-mul-left-2c6c2553`)
- `Nat.odd_of_mul_right : Odd (m*n) -> Odd n` (`F:ml430-nat-odd-of-mul-right-fe6d20ff`)
- `Nat.even_add_one : Even (n+1) <-> !Even n` (`F:ml430-nat-even-add-one-15b5cb18`)
- (private helper) `Nat.even_mul_of_even_left : Even m -> Even (m*n)`, under the
  two `odd_of_mul_*` above.

**Flipped onto a pre-existing theorem, no new proof:**
- `F:ml430-nat-even-iff-024826e9` (`Even n <-> n%2=0`) — matches
  `Nat.even_iff_mod_two_eq_zero`, already in `nat_prelude/parity.rs` before this
  lane started. Flipping it exposed 8 sibling facts (6 `Int` mirrors that already
  used this Nat theorem in their proof terms, `F:ml430-nat-prime-mod-two-eq-one-iff-ne-two-25c35e73`,
  `F:nat-even-xor`) to `check-fact-depends-derived.py`'s dependency graph; fixed
  with `--fix` (their proof terms did not change, only their recorded
  `depends_on`).

**Blocked, named, sized — next lane can pick these up directly:**

Detail moved to [`../notes/369-nat-parity-div.md`](../notes/369-nat-parity-div.md).

<!-- plan-section: landed-changes -->

| 2026-08-30 | nat-parity-div | 6 new axiom-free Nat kernel theorems (parity/div-two cluster) + 1 mirror flipped onto a pre-existing theorem; 7 of 10 dispatched facts proved, 3 blocked with named reasons |

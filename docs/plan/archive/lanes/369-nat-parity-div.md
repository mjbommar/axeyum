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

- `F:ml430-nat-even-add-31386639` (`Even(m+n) <-> (Even m <-> Even n)`) and
  `F:ml430-nat-even-add-39e3bc07` (`Even(m+n) <-> (Odd m <-> Odd n)`): NOT
  missing any single lemma. These need a 4-branch case split on `(m%2, n%2)`
  (nested `Nat.mod_two_eq_zero_or_one` on `m` then `n`), computing `(m+n)%2` in
  each of the 4 leaves (the arithmetic is the same `succ_add`/defeq-reduction
  technique `even_add_one` already uses, just doubled), then combining into the
  OUTER `Iff` — which itself has an `Iff` on one side, so each leaf's
  construction must produce a full `Iff (Even m <-> Even n) ...`-shaped term
  directly (no generic `iff_congr` combinator exists in this kernel to build it
  generically; `int_prelude/parity.rs`'s `even_add`/`even_add'` do exactly this
  shape already, over `Int` — read `even_add_family_stmt_and_proof` there for
  the case-tree structure to mirror, NOT to transport). Sizing: roughly 2-3x
  `even_add_one`'s proof volume (4 leaves vs. 2, each producing a compound
  `Iff`), no new arithmetic lemma needed.
- `F:ml430-nat-even-div-395c6b5e` (`Even (m/n) <-> m % (2*n) / n = 0`): genuinely
  Nat-specific, no `Int` analog exists for this one (division doesn't carry
  over the same way). Needs relating `Nat.div`/`Nat.mod` under SCALING the
  divisor by 2 (`m/n` vs `m % (2n) / n`) — I did not find an existing lemma of
  this shape in `division.rs`/`div_mod_lemmas.rs`/`mod_mul_lemmas.rs` (checked
  all three). This is more substantial than the other two blockers: it likely
  needs a new `Nat.div_mod_scale`-shaped identity built from `div_mod_exec`/
  `div_mod_unique` at divisor `2*n` compared against divisor `n`, not just a
  case split on existing facts.

**Skipped per brief:** `fermat`/`prime`-family facts in the same
`check-dispatchable-frontier.py --json` dispatchable set (`F:ml430-nat-coprime-fermatnumber-*`,
`F:ml430-nat-fermatnumber-*`, `F:ml430-nat-odd-fermatnumber-*`,
`F:ml430-nat-fermat-primefactors-one-lt-*`, `F:ml430-nat-pow-of-pow-add-prime-*`,
`F:ml430-nat-totient-gcd-mul-totient-mul-*`) — sibling lanes own those.

Held-out check: all 10 originally-dispatched facts (and the 3 remaining open
ones) verified against `check-dispatchable-frontier.py --json`'s `held_out`
list before starting — none are held-out.

<!-- plan-section: landed-changes -->

| 2026-08-30 | nat-parity-div | 6 new axiom-free Nat kernel theorems (parity/div-two cluster) + 1 mirror flipped onto a pre-existing theorem; 7 of 10 dispatched facts proved, 3 blocked with named reasons |

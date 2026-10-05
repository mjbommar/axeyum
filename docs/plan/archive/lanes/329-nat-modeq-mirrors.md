# Lane: nat-modeq-mirrors — close `ml430-nat-modeq` additive/multiplicative mirrors

<!-- plan-section: lane-status -->

**Your lane's block (`DONE for this pass`, nat-modeq-mirrors, 2026-08-30).**
6 of the 10 dispatchable `ml430-nat-modeq` mirrors closed; 4 left open with a
precise blocker each (below). `nat_prelude/modular.rs` already carries a full
`Nat.modEq d a b := ∃ u v, a + d*u = b + d*v` congruence family (refl, symm,
trans, add_left/right/both, mul_left/right/both, and `euler.rs`'s coprime
multiplicative cancel `mod_eq_cancel`) — none of it was wired to any fact
before this lane, and `F:ml430-nat-modeq-add-1561afa8` turned out to already be
exactly `Nat.mod_eq_add`, no new proof needed.

Closed (new file `crates/axeyum-lean-kernel/src/nat_prelude/modeq_add_cancel.rs`,
wired in right after `declare_gcd_comm`, since `mod_eq_cancel_left` needs
`gcd_comm`):

- `F:ml430-nat-modeq-add-1561afa8` — `Nat.mod_eq_add` (pre-existing, flip only)
- `F:ml430-nat-modeq-add-iff-left-b719aac5` — `Nat.mod_eq_add_iff_left`
- `F:ml430-nat-modeq-add-iff-right-84daa45f` — `Nat.mod_eq_add_iff_right`
- `F:ml430-nat-modeq-add-left-cancel-fb96581c` — `Nat.mod_eq_add_left_cancel`
- `F:ml430-nat-modeq-add-right-cancel-f0ab48e4` — `Nat.mod_eq_add_right_cancel`
- `F:ml430-nat-modeq-cancel-left-of-coprime-f89af373` — `Nat.mod_eq_cancel_left`
  (same content as `mod_eq_cancel`, coprimality's `gcd` argument order flipped
  via `gcd_comm` to match this mirror's `m.gcd c = 1` vs. `mod_eq_cancel`'s
  `gcd c n = 1`)

All five new theorems compose only already-checked lemmas
(`mod_eq_add_left`/`_right`/`_symm`/`_trans`/`mod_eq_add`/`gcd_comm`/
`mod_eq_cancel`) plus two `euler.rs` helpers exported `pub(super)` for this
purpose: `cancel_common_right_addend` (`modEq n (a+k) (b+k) → modEq n a b`,
needs no side condition — additive cancellation is easier than the
multiplicative case `mod_eq_cancel` needs Bezout for) and `rewrite_mod_eq`
(transport a `modEq` across an `Eq` on each endpoint). No new
existential-elimination term was written in this pass.

Every rendered type checked character-for-character against `nat_theorem_inventory`
output before flipping a fact (all 5 new + the 1 pre-existing match their
`formal.statement` exactly, up to alpha-renaming). Each `checker_command`
verified BOTH directions by hand: exit 0 against the real declaration name,
exit 1 with `_FABRICATED_NONEXISTENT` appended to that name.
`python3 scripts/validate-facts.py` → 2219 facts, 0 errors (after
`scripts/check-fact-depends-derived.py --fix`, which added 20 `depends_on`
edges the proof terms actually use).

**Left open, 4 facts, in decreasing tractability:**

- `F:ml430-nat-modeq-add-le-of-lt-c774015b` — `a≡b [MOD m] → a<b → a+m≤b`.
  Mathematically straightforward (witnesses `a+m*u=b+m*v` plus `a<b` force
  `u>v`, hence `m*u ≥ m*v+m`, hence `b ≥ a+m`) but every supporting piece is
  missing from this prelude: no `Le`/`Lt`-to-existence bridge
  (`Lt a b → ∃k, b=a+k+1`-shaped lemma — grepped `order*.rs`/`add_basics.rs`/
  `add_pos.rs` for `exists_add`/`le_iff_exists`/`lt_iff_exists`/
  `succ_le_of_lt`, nothing), no `m>0 ∧ m*u>m*v → u>v` cancellation-under-order
  lemma, no `u>v → m*u≥m*v+m` step. Needs 2-3 new order/monotonicity lemmas
  before the modEq-specific argument even starts. Real work, not a quick
  wrapper — sizeable enough that I judged it out of scope for this pass rather
  than risk a rushed, wrong order argument.
- `F:ml430-nat-modeq-cancel-left-div-gcd-57ef8287` — `0<m → c*a≡c*b[MOD m] →
  a≡b[MOD m/gcd(m,c)]`.
- `F:ml430-nat-modeq-cancel-left-div-gcd-cfca1225` — same with an extra
  `c≡d[MOD m]` hypothesis, concluding `a≡b[MOD m/gcd(m,c)]`.
- `F:ml430-nat-modeq-cancel-right-div-gcd-22a4f40d` — right-multiplication
  mirror of the first.

  All three div-gcd facts need genuinely new infrastructure beyond
  `mod_eq_cancel_left`: rewriting `m` as `g*(m/g)` and `c` as `g*(c/g)` where
  `g=gcd(m,c)` (needs `Nat.div_gcd_dvd`-style divisibility + the exact
  factorization identities), then `coprime (m/g) (c/g)`, then transporting the
  hypothesis `c*a≡c*b[MOD m]` down to `(c/g)*a≡(c/g)*b[MOD m/g]` before
  `mod_eq_cancel_left` applies. That's a genuinely bigger slice (division
  algebra + a fresh coprimality lemma), not a wrapper — did not attempt this
  pass.

Next lane: the div-gcd family is probably worth its own dedicated pass (the
division/gcd factorization lemmas would likely also feed other open facts in
this ledger); `add-le-of-lt` mostly needs 2-3 general order lemmas that belong
in `order.rs`/`order_extra.rs` rather than in a modEq-specific file.

<!-- plan-section: landed-changes -->

| 2026-08-30 | nat-modeq-mirrors | `nat_prelude/modeq_add_cancel.rs`: 5 new theorems + 1 pre-existing flip close 6 `ml430-nat-modeq` mirrors (add, add_iff_left/right, add_left/right_cancel, cancel_left_of_coprime); 4 left open (add_le_of_lt, 3x cancel-div-gcd) with precise blockers recorded above |

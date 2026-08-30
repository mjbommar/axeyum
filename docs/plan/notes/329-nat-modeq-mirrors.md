# Notes: 329-nat-modeq-mirrors

Detail moved out of [`../status/329-nat-modeq-mirrors.md`](../status/329-nat-modeq-mirrors.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

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

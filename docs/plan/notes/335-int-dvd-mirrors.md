# Notes: 335-int-dvd-mirrors

Detail moved out of [`../status/335-int-dvd-mirrors.md`](../status/335-int-dvd-mirrors.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

None of the twelve needed a new case split over `Int.rec`/`Nat.rec` or a
new base algebraic identity beyond `Int.mul_sub`. The unconditional-`n`
`ModEq` facts all reuse `modeq.rs`'s `modeq_to_dvd`/`dvd_to_modeq` bridge
(itself already unconditional, but never exposed as its own declared
theorem before `mod_eq_dvd`) exactly the way `modeq.rs`'s own
`declare_modeq_add_right`/`_left` already do for addition; `mod_eq_mul_general`
applies the identical trick to multiplication, which needed one extra
step (`Int.mul_sub`) the additive case does not.

All fourteen declarations are axiom-free (`prelude_axiom_inventory
--require-axiom-free integer`: `integer: axiom=0`), registered in
`int_prelude_tests.rs`'s `derived_laws` pin (recomputed by
`scripts/recount-pinned-inventory.py`, 196 -> 207 -> 208, never
hand-incremented), and covered by the environment-derived
`every_int_declaration_is_checked_and_axiom_free` assertion. Full
`int_prelude::` sweep: 49 passed, 0 failed, both after the twelve-theorem
commit and again after the thirteenth (`mod_eq_mul_general`).

Every fact's `checker_command` was run directly (not just written): each
greps `int_theorem_inventory`'s output anchored
`^theorem[[:space:]]+Int\.<name>[[:space:]]`, verified against the
substring-overlapping sibling where one exists (`dvd_gcd_nat` vs
`dvd_gcd_nat_iff`, `mod_eq_add` vs `mod_eq_add_left_cancel_general`,
`mod_eq_add_right_cancel` vs `_general`), and confirmed to fail closed
(`int_theorem_inventory` exits 1, "no Int declaration matches") on a
fabricated name.

Partition check before touching any fact: all fourteen are `development`
in `artifacts/autogenesis/nursery-v2-extension.json` — none held-out.

`python3 scripts/check-fact-depends-derived.py --fix` was run after each
flip batch (the dependency is always in the proof term; only the ledger
edge was missing). `validate-facts.py`: 2220 facts checked, 0 errors,
`missing_edges=0`, `proved=2046`.

**Six targets remain open, genuinely harder — not mis-sized:**

- `F:ml430-int-dvd-gcd-mul-iff-dvd-mul-12f61b99`
  (`k ∣ ↑(k.gcd n) * m ↔ k ∣ n * m`),
  `F:ml430-int-dvd-gcd-mul-gcd-iff-dvd-mul-8ea752a5`
  (`k ∣ ↑(k.gcd n) * ↑(k.gcd m) ↔ k ∣ n * m`), and
  `F:ml430-int-dvd-mul-gcd-iff-dvd-mul-22d6488e`
  (`k ∣ n * ↑(k.gcd m) ↔ k ∣ n * m`) all transport to the SAME blocker the
  sibling `nat-gcd-dvd-mirrors` lane already identified and left open
  (`docs/plan/status/331-nat-gcd-dvd-mirrors.md`): all three reduce
  cleanly to the distributive law `Nat.gcd (a*c) (b*c) = Nat.gcd a b * c`
  (Mathlib's `Nat.gcd_mul_right`), which the `Nat` prelude does not have
  (`nat_prelude/lcm_gcd_lemmas.rs` and `nat_prelude/gcd.rs` both checked in
  full, not just grep). Since `Int.gcd` is defined as `Nat.gcd` on
  `natAbs`, an `Int`-level proof needs the `Nat` lemma first regardless of
  which layer it is stated at. Do not re-derive this independently at the
  `Int` layer — build it once at the `Nat` layer and both lanes' remaining
  facts unlock together.
- `F:ml430-int-dvd-mul-3a7b94cd` (`c ∣ a*b ↔ ∃ c₁ c₂, c₁∣a ∧ c₂∣b ∧
  c₁*c₂ = c`) is the `Int` mirror of the sibling lane's
  `F:ml430-nat-dvd-mul-ebd102e2`, and is the same kind of statement they
  flagged: an existence claim over a compatible factorization, closer to
  unique factorization than to gcd algebra. No short route through
  existing prelude lemmas found; did not attempt a from-scratch
  construction.
- `F:ml430-int-modeq-cancel-left-div-gcd-b2d407e8` (`0 < m → c*a ≡ c*b
  [ZMOD m] → a ≡ b [ZMOD m / ↑(m.gcd c)]`) and
  `F:ml430-int-modeq-cancel-right-div-gcd-00cd73fa` (mirrored) are a
  DIFFERENT family from the existing `p.mod_eq_cancel`, which requires
  `Coprime c n` outright — these generalize past that by dividing the
  modulus by `gcd(m,c)` first, which handles the non-coprime case. This
  needs new machinery relating `c*(b-a)` divisibility by `m` to `(b-a)`
  divisibility by `m/gcd(m,c)`, built from the existing
  `gcd_div_gcd_div_gcd` (coprimality of the quotients) rather than
  `gauss_lemma` directly. Sized but not attempted — real algebra, not a
  composition of what already exists.

**Next step for whoever picks this up:** build `Nat.gcd_mul_right` first
(shared blocker, unlocks three facts here and three in the `Nat` lane's
own remainder); the two `modeq_cancel_*_div_gcd` facts and `dvd_mul` are
independent of that and of each other.

`bash scripts/check-merge-hygiene.sh`: see commit history for the exact
line; ran clean.

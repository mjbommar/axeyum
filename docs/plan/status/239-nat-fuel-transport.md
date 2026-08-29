# Lane: nat-fuel-transport — transport landAux fuel-irrelevance to lorAux/ldiffAux, then close one of the 7 blocked facts

<!-- plan-section: lane-status -->

**Your lane's block (`DONE`, nat-fuel-transport, 2026-08-29).** Both
transports landed (`lorAux`, `ldiffAux`), and `F:ml430-nat-land-comm-7e6ad72e`
(one of the 7 `natural-bitwise` facts fuel-irrelevance was blocking) is
closed. The other 6 (`land_assoc`, `land_bit`, `lor_comm`, `lor_assoc`,
`lor_bit`, `ldiff_bit`) remain open — see "What is still needed" below for
what each still needs beyond this lane's work.

**Whether the ~20-lines-each sizing held.** No — it undercounted both, and
in different ways.

- **`lorAux`'s transport needed a piece the handoff did not name.**
  `Nat.lor_aux_zero_left_any_fuel`'s `succ`-branch proof cannot use
  `bool_select_nat_same` the way `land`'s analogue does: at `m = 0` fixed,
  `fuel = succ f`, the outer `n = 0` guard's two branches are `m` (`= 0`,
  literal) and the reduced inner term (`= n`) — two DIFFERENT terms, not one
  term repeated. The fix is a nested `cases_zero_succ` on `n` itself inside
  the `fuel = succ f` branch; once `n`'s shape is exposed, both leaves close
  by `refl`. This is `lorAux`'s fuel-exhaustion row (returns `n`, not `0`)
  biting, not its guard order. `declare_lor_aux_agree_of_fuel` itself,
  once `lor_aux_zero_left_any_fuel` existed, WAS close to the sizing — a
  guard/bit-combine swap, no new proof technique.
- **`ldiffAux`'s transport matched the sizing exactly.** Its
  `zero_left_any_fuel` is byte-for-byte `land`'s proof (same absorbing-zero
  base case, confirmed by tracing the reduction: at `m = 0` fixed, both the
  outer and inner guards ultimately collapse to the constant `0` via
  `bool_select_nat_same`, exactly as `land`'s does). Its `agree_of_fuel`
  step needed only the hybrid guard swap (`on_n_zero = m` pass-through like
  `lor`, `on_m_zero = 0` absorbing like `land`) and the `beq`-based per-bit
  combine — no new case split.

**Negative control per transport** (mandatory, insufficient-fuel, checked by
evaluation alone since no `Le m fuel` proof exists at the chosen witness):

- `lor`: `(fuel, m, n) = (1, 3, 4)` — `lorAux 1 3 4 = 5` against
  `lor 3 4 = 7` (`011 | 100 = 111`). **`land`'s own witness `(1, 7, 7)` does
  NOT discriminate `lor`**: `lorAux 1 7 7 = 7 = lor 7 7`, no disagreement at
  all, because `lorAux`'s base row returns `n` rather than `0`. Each
  transport needed its own witness, verified by simulating both recursions
  in Python before committing to the Rust proof.
- `ldiff`: `(fuel, m, n) = (0, 7, 0)` — `ldiffAux 0 7 0 = 0` (the outer
  `Nat.rec` never runs at all) against `ldiff 7 0 = 7` (`ldiff m 0 = m`, and
  canonical fuel `m = 7` IS `succ`-shaped, so the `n = 0` guard is reached).

**Which of the 7 facts closed, and what the second piece turned out to be.**
`F:ml430-nat-land-comm-7e6ad72e` (`Nat.land_comm`) — the second piece was
**same-fuel commutativity**, not the `Nat.bit` decode bridge. Fuel-irrelevance
alone is not enough: `land m n = landAux m m n` and `land n m = landAux n n m`
put DIFFERENT values (`m` vs `n`) in the fuel slot, so a genuinely separate
theorem was needed — `Nat.land_aux_comm_of_fuel : ∀ fuel m n, landAux fuel m n
= landAux fuel n m` (a new `agree_by_fuel_induction` instance, 4-way
`(m = 0?, n = 0?)` case split via nested `cases_zero_succ`). Three of the four
cases close via `land_aux_zero_left_any_fuel` or `refl` alone (a guard
checking a LITERAL `0` never needs the other argument's shape); the fourth
(both nonzero) needs only the induction hypothesis plus `Nat.mul_comm` for the
per-bit product — `land`'s guard is symmetric (`on_n_zero = on_m_zero = 0`),
so `guarded(succ_a, succ_b, 0, 0, _, _)` is defeq to BOTH sides' own reduced
row regardless of argument order, and no guard-reordering lemma was needed.
`Nat.land_comm` itself chains `land m n = landAux m m n = landAux (m+n) m n =
landAux (m+n) n m = landAux n n m = land n m`, the outer two steps via
`land_aux_agree_of_fuel` at the shared fuel `m + n` (`Nat.le_add_right` for
`Le m (m+n)`; `Le n (m+n)` needs an extra `Nat.add_comm` transport since only
`le_add_right`, not a `le_add_left`, exists), the middle step via
`land_aux_comm_of_fuel`. Kernel-admitted on the FIRST attempt — no rejection
to diagnose.

**What the kernel rejected, and why: nothing, on both new transports and the
comm lemma.** Every declaration in this lane (`lor_aux_zero_left_any_fuel`,
`lor_aux_agree_of_fuel`, `lor_aux_eq_lor_of_le`, `ldiff_aux_zero_left_any_fuel`,
`ldiff_aux_agree_of_fuel`, `ldiff_aux_eq_ldiff_of_le`,
`land_aux_comm_of_fuel`, `land_comm`) was admitted on its first `cargo test`
run. The only compile-time friction was one clippy `used_underscore_binding`
(an unused-looking closure parameter that was in fact used two lines later);
fixed by renaming, not by silencing the lint.

**What is still needed to close the other 6** (unchanged from
`docs/plan/status/237-nat-fuel-irrelevance.md`'s diagnosis, now confirmed by
actually building the `land_comm` route): `lor_comm` needs the SAME
same-fuel-commutativity treatment as `land_comm`, transported to `lorAux`
(its guard is symmetric too — both `on_n_zero`/`on_m_zero` are pass-through,
`m`/`n` respectively — so the 4-way case split should carry over with the
`max`-via-`ble` per-bit combine in place of `mul`). `land_assoc`/`lor_assoc`
need an analogous same-fuel ASSOCIATIVITY lemma (not built here — a 3-operand
case split is a different, larger piece, not a corollary of commutativity).
`land_bit`/`lor_bit`/`ldiff_bit` still need the `Nat.bit` decode bridge this
lane did not attempt — relating `landAux`/`lorAux`/`ldiffAux` at a
`Nat.bit`-constructed argument (`fuel = bit a m`, non-canonical) to the
recursive step; fuel-irrelevance and the comm lemmas built here do not touch
`Nat.bit` at all.

**Counts.** `nat_prelude` before this lane: 122 passed (post
`nat-fuel-irrelevance`). After: 125 passed (3 new instantiation tests: `lor`'s
and `ldiff`'s fuel-irrelevance negative controls, `land_comm`'s concrete
application). 8 new declarations, all theorems
(`lor_aux_zero_left_any_fuel`, `lor_aux_agree_of_fuel`, `lor_aux_eq_lor_of_le`,
`ldiff_aux_zero_left_any_fuel`, `ldiff_aux_agree_of_fuel`,
`ldiff_aux_eq_ldiff_of_le`, `land_aux_comm_of_fuel`, `land_comm`) —
`the_build_is_deterministic`'s pin moved `85 + 441` → `85 + 449` (counted
from the panic message's own mismatch both times, not hand-incremented).
`nat` trusted surface still `axiom=0 opaque=0 quotient=0`
(`nat_axiom_inventory --require-axiom-free nat`). New fact `F:nat-land-comm`;
`F:ml430-nat-land-comm-7e6ad72e` flipped open → proved via a reconciliation
evidence row (Mathlib's `Nat.land` is `Nat.bitwise and`, and ours is proved
equal to that specialization by `Nat.bitwise_and_eq_land`, so this closes the
SAME function's commutativity — the honest-flip criterion in CLAUDE.md's
gotchas). `python3 scripts/validate-facts.py`: 1923 facts, 0 errors.
`cargo fmt --all --check` and
`cargo clippy -p axeyum-lean-kernel --all-targets -- -D warnings` both clean
on the touched files. NOT run: the aggregate `just check` / `./scripts/check.sh`.

Three `testbit` facts remain pinned OPEN by the live
`gen-autogenesis-bitwise-family-projection.py` gate and were not touched.

<!-- plan-section: landed-changes -->

| 2026-08-29 | nat-fuel-transport | Transport fuel-irrelevance to `lorAux`/`ldiffAux` (6 new theorems); close `F:ml430-nat-land-comm-7e6ad72e` via a new same-fuel commutativity lemma (`land_aux_comm_of_fuel`) plus the shared-fuel routing (`land_comm`); 6 of 7 blocked facts remain open |

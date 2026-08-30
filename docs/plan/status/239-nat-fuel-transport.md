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

Detail moved to [`../notes/239-nat-fuel-transport.md`](../notes/239-nat-fuel-transport.md).

<!-- plan-section: landed-changes -->

| 2026-08-29 | nat-fuel-transport | Transport fuel-irrelevance to `lorAux`/`ldiffAux` (6 new theorems); close `F:ml430-nat-land-comm-7e6ad72e` via a new same-fuel commutativity lemma (`land_aux_comm_of_fuel`) plus the shared-fuel routing (`land_comm`); 6 of 7 blocked facts remain open |

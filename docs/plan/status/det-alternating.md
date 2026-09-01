# Lane: det-alternating

<!-- plan-section: lane-status -->

**Landed.** `Rat.det_alternating` — the ALTERNATING property of the general-n
determinant (`det A n = 0` whenever two distinct rows of `A` agree pointwise)
— is admitted by the trusted kernel gate, axiom-free, accepted on the first
attempt. This is step 2 of ADR-1310's three-theorem dependency chain toward
determinant multiplicativity (step 1, `Rat.det_row_expansion`, was already
landed on `main`; step 3, sign under a row swap, was not attempted).

## What landed

`Rat.det_alternating`, rendered type:

```
∀ (m : Nat) (A : Nat → Nat → Rat) (i j : Nat),
  Nat.beq i j = false →
  Nat.ble i m = true →
  Nat.ble j m = true →
  (∀ c, A i c = A j c) →
  Rat.det A (succ m) = Rat.zero
```

Proved by a single induction on `m`. Base case (`m=0`) is vacuous: the two
bound hypotheses force `i=j=0`, contradicting distinctness. The step
case-splits `i` and `j` against `0` (not against each other), giving four
shapes, all sharing one helper (`zero_sum_via_expansion`: expand along a row,
collapse the sum via `Rat.sumRange_eq_zero_of_lt` once every cofactor
determinant is shown `0`):

1. **Both rows nonzero** — expand along row `0`. `Rat.matSkip_zero`
   (`matSkip 0 x = succ x`, unconditional, already landed) means the minor's
   shifted rows are the original `i`,`j` by pure computation, and because
   `Nat.beq`/`Nat.ble` at two `succ`s iota-reduce by peeling one layer, the
   OUTER hypotheses are already, up to defeq, exactly what the induction
   hypothesis wants — passed through verbatim, nothing rebuilt.
2. **One row `0`, the other `≥ 2`** — expand along row `1`, unconditionally
   valid (`ble 1 (succ mp) = true` for any `mp`, pure iota).
3. **Rows are `{0,1}`, no third row** (`mp=0`, dimension 2) — closes directly
   from `Rat.det_eq_det2` and ordinary `Rat` algebra (`A00=A10`, `A01=A11`
   give `A00*A11=A01*A10` by `Rat.mul_comm`), reusing the (now `pub(super)`)
   `det2_zero_of_ad_eq_bc` from `matrix.rs`.
4. **Rows are `{0,1}`, a third row exists** (`mp = succ mp'`) — expand along
   row `2`; validity (`ble 2 (succ mp) = true`) is derived from
   `Nat.beq mp 0 = false` via a small helper producing `mp = succ (pred mp)`.
5. **The symmetric case** (nonzero row first, `j=0`) reuses the SAME core
   builders for shapes 2–4 (`alt_core_ge2`, `alt_core_eq1`) with the
   row-equality hypothesis flipped by `rsymm`, rather than duplicating the
   construction.

**Contrary to ADR-1310's expectation, no branch uses `Rat.det_congr`.** Every
branch applies the induction hypothesis directly to the literal minor term;
every index shift needed resolves by pure iota reduction once the case split
fixes the relevant index's shape (`0`, `1`, or a `succ` of a bound variable).
No new supporting lemma (e.g. no `matSkip_of_ble`) was needed beyond what was
already declared — the "OTHER branch of `matSkip`'s `bool_select_nat`" that
looked necessary during planning turned out to always apply at an index whose
shape the case split had already pinned down, so it reduces by refl rather
than needing a general hypothesis-driven lemma.

## Landed changes

| what | where |
| --- | --- |
| `Rat.det_alternating` — one checked theorem, empty axiom footprint, admitted first attempt; 14 supporting Rust helper functions (`zero_sum_via_expansion`, `alt_core_ge2`, `alt_core_eq1`, `congr_nat_to_bool`, `bool_true_via_eq`, `contradiction_of_eq_via_beq`, three `nat_eq_zero_of_.../nat_succ_pred_of_...` bound-derivation helpers, and the case-split tree `alt_base`/`alt_step`/`alt_branch_i_zero`/`alt_branch_i_succ`/`alt_zero_*`/`alt_succ_*`) | `crates/axeyum-lean-kernel/src/rat_prelude/matrix_det.rs` |
| `det2_zero_of_ad_eq_bc` made `pub(super)` for reuse | `crates/axeyum-lean-kernel/src/rat_prelude/matrix.rs` |
| Field + doc, registered in `named`/theorem-kind-and-axiom-footprint inventory | `crates/axeyum-lean-kernel/src/rat_prelude.rs`, `crates/axeyum-lean-kernel/src/rat_prelude/rat_prelude_tests.rs` |
| `F:rat-det-alternating` | `artifacts/facts/` |

## Checks run

- `cargo check -p axeyum-lean-kernel` — clean, twice (before and after the
  test-suite fix below).
- `cargo test -p axeyum-lean-kernel --lib rat_prelude::` — first run: **155
  passed, 1 failed** (`every_rat_declaration_is_checked_and_axiom_free`, an
  environment-derived coverage assertion — `Rat.det_alternating` was live in
  the prelude but absent from the test file's own `named`/`ring_laws`/
  `unnamed_but_live_declarations` inventory). Fixed by registering it in both
  lists. Second run: **156 passed, 0 failed** (501 s).
- `python3 scripts/validate-facts.py` — 2,524 facts, 0 errors.
- `Rat.det_alternating`'s `checker_command` verified in BOTH directions:
  present name prints `1` and exits `0`; a misspelled name prints `0` and
  exits `1`.
- `cargo run --release -p axeyum-lean-kernel --example nat_axiom_inventory --
  --require-axiom-free rat` — exits `0`.

## What is NOT established

- Step 3 of ADR-1310's chain (sign under a row swap) was **not attempted** —
  it was an explicit stretch goal only if step 2 landed with room to spare,
  and the case-split volume for step 2 (14 helper functions, ~950 lines)
  used the available effort.
- Multiplicativity itself remains three steps away no longer — it is now ONE
  step away (sign under a row swap, then the multiplicativity argument
  itself, which ADR-1310 already argued is unblocked by `sumMaps`/
  `prodRange_sumRange_expand`).
- The proof's helper functions are not independently evidenced beyond the
  kernel accepting the whole declaration and the full-suite pass — there is
  no separate mutation/negative-control suite for `Rat.det_alternating`
  itself (unlike `Rat.det_row_expansion`'s ADR-1185 numeric-sweep and
  mutation controls). The kernel gate is real (a wrong statement or a wrong
  proof term is rejected), but no adversarial fixture was built to confirm
  the STATEMENT itself couldn't be satisfied by a weaker/wrong claim.

## Next

Sign under a row swap (ADR-1310 step 3): `det` of a row-permuted matrix is
`sgn * det`, following from the alternating property by the standard
`det(A + swap) = 0` expansion. Then multiplicativity itself.

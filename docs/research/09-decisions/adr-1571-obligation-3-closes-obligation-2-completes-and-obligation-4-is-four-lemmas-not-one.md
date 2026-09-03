# ADR-1571: obligation 3 closes, obligation 2 completes, and obligation 4 turns out to be four more lemmas plus one invariant — three of the four are landed and the invariant is NOT

Status: accepted
Date: 2026-09-02
Index-summary: Thirteen axiom-free `Rat` declarations and one `Nat` one close
ADR-1554's **obligation 3** (`Rat.clearBelow_off` / `clearBelow_zero`, with
`Rat.add_neg_div_mul_cancel` as the arithmetic core), complete its
**obligation 2** (`Rat.pivotSearch_column_zero`, the exhaustion disjunct
ADR-1562 left open), and land three of obligation 4's four prerequisites
(`Rat.leadingIndex_eq_of_first_nonzero`, `Rat.leadingIndex_eq_cols_of_zero_row`,
`Rat.clearBelow_preserves_zero`). `Nat.lt_of_ble_eq_false` — the STRICT
false-side `ble` bridge three consumers were owed (ADR-1558 §4, ADR-1562 §4) —
is promoted into `nat_prelude` and spent exactly once. **`rowEchelon_isEchelon`
is NOT proved and neither is the pivot section, so the ADR-1562 bridge is still
conditional and `rank_eq_rankCols` is still not unconditional.** Four things are
decided or measured. (1) **A fuel lemma needs a fuel bound exactly when its
conclusion is about a value the sweep CREATES, and needs none when the value is
one it PRESERVES** — `clearBelow_zero` and `clearBelow_preserves_zero` are the
same function, one hypothesis apart, and the direction of the conclusion decides
it. (2) **Where the pivot row sits relative to the cursor is a hypothesis, not a
detail, and the two lemmas want OPPOSITE strictness**: `clearBelow_zero` needs
`Lt pr r`, because the nonzero-pivot hypothesis travels inside the motive and is
re-established by `Rat.rowAddMul_off`, which needs the pivot row to be a row the
step did not touch; `clearBelow_preserves_zero` needs `Le pr r`, because its
hypothesis has to COVER row `pr` — the sweep adds a multiple of the pivot row
into each row it rewrites, so the pivot row's own entry in that column must be
zero too. (3) **ADR-1554 §3's choice of `cols` as a zero row's leading index pays a
second time**: in `leadingIndexAux_eq_cols_of_zero` both exhaustion leaves close
by `Eq.refl`, because the scan's give-up answer IS the conclusion. (4)
**Obligation 4 is re-sized from measurement rather than estimate**: what remains
is one invariant `Prop` and two inductions, and the four prerequisites it was
resting on are now three-quarters landed, with `rowSwap`'s range preservation
the only missing one.
Index-status: accepted

Related: ADR-1554 (the row-echelon form and its four obligations), ADR-1555
(`Rat.rank`), ADR-1558 (rank-nullity in column form), ADR-1562 (the bridge
orientation and the section equation), ADR-0603 (graded statement families),
ADR-0601 (one trust anchor).

## Context

ADR-1554 sized `rowEchelon_isEchelon` as four obligations and said obligation 4
was "at least a lane on its own and probably two". ADR-1562 discharged the
`rank = rankCols` bridge modulo ONE hypothesis, the pivot section, and recorded
obligations 2 (exhaustion disjunct) and 3 (whole) as open. This lane took
obligation 3 and then kept going down the prerequisite chain.

The honest summary of what happened is that **obligation 3 was the size ADR-1554
said it was, and obligation 4 is bigger than its sizing because the sizing
counted the invariant and not the lemmas the invariant consumes.** Those lemmas
are what this ADR mostly records.

## Decision

### 1. Obligation 3, in two halves, and the OFF half is the one the ZERO half needs

```text
Rat.clearBelow_off  : ∀ M pr pc rows q c, Le q pr → clearBelow M pr pc rows q c = M q c
Rat.clearBelow_zero : ∀ M pr pc rows q, Lt pr q → Lt q rows → M pr pc ≠ 0 →
                        clearBelow M pr pc rows q pc = 0
```

with `Rat.add_neg_div_mul_cancel : ∀ a b, b ≠ 0 → a + (-(a/b)) * b = 0` as the
arithmetic core ADR-1554 named, and the fuelled `…Aux` form of each.

The OFF half is not a convenience half. When the sweep reaches the target row it
rewrites that row ONCE and then keeps recursing strictly below, so the value the
caller asked about is fixed by rows the loop has not visited yet — which is
`clearBelowAux_off` instantiated at the row just cleared. Proving the zero half
without it means re-deriving it inline.

**The fuel bound in the `…Aux` form is a real hypothesis.** `clearBelowAux`
answers `M` when its fuel runs out, exactly as it does when the row cursor
passes `rows`; the two exhaustion routes are indistinguishable in the answer, so
at `fuel = 0` the zero half is simply false. `Lt q (r + fuel)` — *the target row
is within the `fuel` rows this call will visit* — is the weakest thing that
rules it out, and the wrapper discharges it from `Lt q rows` because
`clearBelow` hands the loop `rows` units.

### 2. A fuel lemma's need for a bound is decided by which way its conclusion points

This is the generalisable finding, and it is not about matrices.

`Rat.clearBelow_preserves_zero` (§3 below) is a statement about the SAME
function with the SAME recursion, and it needs **no fuel bound at all**. The
difference is that `clearBelow_zero`'s conclusion is about a value the sweep has
to CREATE — an exhausted sweep returns `M` untouched and the entry is whatever
it was — while `clearBelow_preserves_zero`'s conclusion is about a value the
sweep PRESERVES, so the exhausted answer satisfies it directly. In the first
lemma the base case and the out-of-range branch are REFUTED; in the second they
CLOSE from the hypothesis.

Stated as a rule: **a fuelled recursion's postcondition needs a fuel bound iff
its conclusion is false of the recursion's exhaustion answer.** Both of this
lane's other fuel bounds (`pivotSearchAux_column_zero`,
`leadingIndexAux_eq_of_first_nonzero`) are the create-shaped kind and need one;
`leadingIndexAux_eq_cols_of_zero` is the preserve-shaped kind in disguise —
its exhaustion answer IS its conclusion — and its bound is only there to reach
the in-range branch.

### 3. What obligation 4 actually needs, measured

The loop invariant `echelonAux` maintains has three clauses: rows `[0, pr)` have
strictly increasing leading indices all below `pc`; rows `[pr, rows)` are zero
throughout `[0, pc)`; and the fuel is enough (`cols ≤ pc + fuel`). Preserving it
through ONE pivot step needs, and cannot be done without:

| prerequisite | what the step needs it for | status |
|---|---|---|
| `Rat.pivotSearch_column_zero` | the NO-PIVOT branch, which advances `pc` alone: it is the only thing that can extend clause 2 by a column | **landed here** |
| `Rat.leadingIndex_eq_of_first_nonzero` | the new pivot row's leading index is exactly `pc` — clause 1's extension | **landed here** |
| `Rat.leadingIndex_eq_cols_of_zero_row` | at exit, every row below the last pivot reads `cols`, which is what `echelonStepOk` accepts | **landed here** |
| `Rat.clearBelow_preserves_zero` | clause 2 survives the sweep at every column left of `pc` | **landed here** |
| `Rat.rowSwap` preserving a zero range | the swap happens BEFORE the sweep, between two rows both in `[pr, rows)` | **NOT landed** |
| the invariant as an explicit `Prop`, and its fuel induction | obligation 4 proper | **NOT landed** |
| the exit derivation, an induction over `isEchelonAux`'s own fuel | obligation 4 proper | **NOT landed** |

So the sizing correction is: ADR-1554 called obligation 4 "the loop invariant",
and the loop invariant is the last two rows of that table. The four rows above
them are separate lemmas about three different functions, and none of them was
visible in the original sizing. Three are now landed and one is not.

**`rowEchelon_isEchelon` is not proved, the pivot section is not derived, and
therefore `Rat.rank_eq_rankCols`, `Rat.rank_le_cols` and the row-form
rank-nullity remain conditional exactly as ADR-1562 left them.** Nothing in this
ADR weakens that; a reader who wants the unconditional forms should read
ADR-1562 §2 for the one equation still owed.

### 4. `Nat.lt_of_ble_eq_false` is promoted, and spent once

ADR-1558 §4 and ADR-1562 §4 recorded the same gap twice: `Nat` had
`le_of_ble_eq_true` and no false-side twin, `ipc` declared the non-strict
statement under a non-`Nat` name, and `pivot_bound.rs` inlined the non-strict
form through `le_total`. The statement `nat_prelude` is now owed is landed:

```text
Nat.lt_of_ble_eq_false : ∀ n m, Nat.ble n m = false → Lt m n
```

The proof splits on `Nat.lt_or_ge` rather than `Nat.le_total` — its left
disjunct IS the conclusion, and its right disjunct `Le n m` contradicts the
hypothesis through `ble_eq_true_of_le`. `le_total` structurally cannot supply
the strict form, which is the whole reason `pivot_bound.rs`'s route stopped at
`Le`.

It is spent exactly once, in `leadingIndexAux_eq_cols_of_zero`, and that use is
the archetype: the scan's `false` branch is the ONLY place an index is known to
be in range, and a bounded-`∀` hypothesis will not answer without a strict
bound. The two earlier consumers are left as they are; retrofitting them is a
separate, purely cosmetic change and this lane did not make it.

## Consequences

- **Obligation 2 is complete.** Range half (ADR-1558), value half (ADR-1562),
  exhaustion disjunct (here). It is the first of ADR-1554's four to close
  outright.
- **The dominance document's "no `rank` function at all" row is false and is
  corrected in place** (`docs/formalized-math-2026-08/09-*.md` §4.3), following
  the precedent ADR-1543 set for the determinant row. Measured on a fresh index
  (2,201 declarations): `shape_search --ns Rat --name-contains rank` returns
  **14** — `Rat.rank` and `Rat.rankCols` as definitions, plus `rank_nullity`,
  `rank_le_rows`, `rankCols_le_cols`, the two `countRange` bridges, the four
  degenerate-dimension equations and the three `_of_pivotSection` results. What
  the row should say is that rank EXISTS at symbolic dimension and that its
  bridge to the column form is conditional on one open equation, which is a
  different and much smaller gap than "not built".
- **ADR-0603 grading for everything landed here**: row 1 is the general
  constructive form (the eight facts); row 2 is **empty by proof**, as for the
  whole family — the order on ℚ is decidable, every predicate is total and
  `Bool`-valued, and there is no Markov-style boundary to refute; row 3 is
  `rat_prelude/clear_below_tests.rs`, `leading_index_tests.rs` and the two new
  tests in `pivot_content_tests.rs`, which reduce every definition at concrete
  matrices against hand-computed values with controls that must NOT be
  `def_eq`; row 4 is empty — no import.
- **Cost.** The `rat` prelude builds in **1.683–1.705 s** (`prelude_build_timing`,
  four consecutive runs) against **1.653–1.660 s** measured on the same host
  immediately after the obligation-3 commit and ADR-1562's 1.63–1.64 s. So the
  fourteen declarations cost roughly 30–45 ms in total, and the family is now
  marginally above the ~1.65 s it was told to watch and inside the ~1.7 s band.
  This IS a delta and not merely a level: the intermediate measurement was taken
  on this host, in this worktree, three commits earlier.
- One rejection is worth carrying forward because the diagnostic names nothing:
  **the lambda that BUILDS a `Not (…)` must bind its argument at the equation,
  not at the negation.** Binding at `Not (…)` produces `Not (Not (…))` and the
  kernel answers with a bare `TypeMismatch` between two consecutive `ExprId`s.
  Bisecting the five declarations with one `eprintln` per `declare_*` call found
  it in a single rebuild; `git bisect`-style reasoning about the term would not
  have, because the two types differ by one constructor deep inside.

## Alternatives rejected

- **Attempting the invariant in this lane after the prerequisites landed.**
  Rejected on measurement, not on preference: §3's table shows one prerequisite
  still missing and two large inductions after it, and a partial invariant is
  not a landable increment — it is either admitted or it is nothing. Sizing it
  honestly and landing four separate checkable lemmas is worth more than a
  half-written motive.
- **Stating `clearBelow_zero` with `Le pr q` instead of `Lt pr q`.** It is
  false at `pr = q`: the pivot row is not cleared against itself, and its entry
  in the pivot column is the nonzero pivot. The statement pin in
  `clear_below_tests.rs` asserts `Le pr q` does NOT occur in the rendered type.
- **Bundling the OFF and ZERO halves into one conjunction carried through one
  induction.** Rejected in §1/§2: they need different hypotheses (the OFF half
  is unconditional in the fuel) and the ZERO half consumes the OFF half, so a
  conjunction would have to carry a bound it does not need and would still have
  to instantiate itself at a different cursor.
- **Retrofitting `ipc_le_of_ble_eq_false` and `pivot_bound.rs` onto the new
  strict lemma.** Deferred deliberately and named as such: both are correct as
  they stand, the change is cosmetic, and doing it here would put a diff in two
  files this lane has no other reason to touch.

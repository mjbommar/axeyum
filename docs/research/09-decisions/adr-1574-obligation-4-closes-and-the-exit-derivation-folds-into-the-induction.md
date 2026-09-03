# ADR-1574: obligation 4 closes — Gaussian elimination lands in row-echelon form, and the exit derivation folds into the induction

Status: accepted
Date: 2026-09-02
Index-summary: **`Rat.rowEchelon_isEchelon` is proved, axiom-free**, closing
ADR-1554's **obligation 4** — the last of its four and the one ADR-1554 sized
as *"at least a lane on its own and probably two"*. Twelve axiom-free `Rat`
declarations in `rat_prelude/echelon_invariant.rs`, seven facts. Four things
are decided or measured. (1) **The exit derivation is not a second induction.**
ADR-1571 §3 listed the invariant's preservation and the exit as two; carrying
`isEchelon … = true` itself as the conclusion at every fuel level makes it
**one**, because each of the three leaves that stop the loop discharges the
conclusion from the invariant and nothing ever names the final cursors. (2)
**The invariant has FIVE clauses, not three, and the fifth is not implied by
the fuel clause** — `Le pc cols` bounds the column cursor from ABOVE, which the
fuel clause cannot do, and the exit branch needs it to turn
`Lt (leadingIndex M r cols) pc` into `Lt … cols`. (3) **Writing the fuel clause
as `pc + fuel` rather than `fuel + pc` makes two of the three exit leaves the
same derivation**: `Nat.add` recurses on its right argument, so
`Le cols (Nat.add pc 0)` IS `Le cols pc` and the fuel-exhausted leaf and the
`ble cols pc = true` leaf are one proof. (4) **The invariant is built by a Rust
function returning hypothesis TYPES, not declared as a `Prop`** — ADR-1562 §2's
rule, applied: a named `Definition` could be well-typed and mean something
else, while an inline Pi in each theorem's own type cannot. Two prerequisites
ADR-1571's table did not predict were needed and are landed:
`Rat.leadingIndex_congr_row` (pointwise row agreement gives an equal leading
index, so the placed prefix survives a step **without `funext`**) and
`Rat.pivotSearch_ge_start`.
Index-status: accepted

Related: ADR-1554 (the row-echelon form and its four obligations), ADR-1571
(obligations 2 and 3, and the re-sizing of 4), ADR-1562 (the bridge orientation
and the pivot-section equation), ADR-1558 (rank-nullity in column form),
ADR-1555 (`Rat.rank`, and why the row form needs `funext`), ADR-0603 (graded
statement families), ADR-0601 (one trust anchor).

## Context

ADR-1554 stated four obligations for the row-echelon form. ADR-1562 closed the
bridge modulo one hypothesis and completed obligation 2's value half; ADR-1571
closed obligation 3, completed obligation 2, and landed three of what it
measured as obligation 4's four prerequisites, leaving:

> | `Rat.rowSwap` preserving a zero range | the swap happens BEFORE the sweep, between two rows both in `[pr, rows)` | **NOT landed** |
> | the invariant as an explicit `Prop`, and its fuel induction | obligation 4 proper | **NOT landed** |
> | the exit derivation, an induction over `isEchelonAux`'s own fuel | obligation 4 proper | **NOT landed** |

All three are landed here, and the last row of that table turns out not to be a
separate induction at all.

## Decision

### 1. Carry the ANSWER as the conclusion, and the exit stops being an induction

The obvious shape for a loop lemma is *invariant in, invariant out*:

```text
INV M pr pc → INV (echelonAux rows cols fuel M pr pc) ?pr' ?pc'
```

and it is unusable, because the conclusion has to name cursors the caller does
not know. The standard repair is a second induction that consumes the invariant
at whatever cursors the loop stopped at. ADR-1571 §3 predicted exactly that, and
sized obligation 4 as an invariant plus two inductions.

What is landed instead is

```text
Rat.echelonAux_isEchelon : ∀ rows cols fuel M pr pc,
  Le pc cols →
  (∀ r, Lt (succ r) pr →
     echelonStepOk (leadingIndex M r cols) (leadingIndex M (succ r) cols) cols = true) →
  (∀ r, Lt r pr → Lt (leadingIndex M r cols) pc) →
  (∀ s c, Le pr s → Lt s rows → Lt c pc → Eq Rat (M s c) Rat.zero) →
  Le cols (Nat.add pc fuel) →
  Eq Bool (isEchelon (echelonAux rows cols fuel M pr pc) rows cols) true
```

— the conclusion at **every** fuel level is already the answer. The three leaves
that stop the loop (fuel exhausted; `Nat.ble rows pr = true`;
`Nat.ble cols pc = true`) each discharge it from the invariant on the spot, and
the two recursive branches simply re-establish the five clauses and apply the
induction hypothesis. **Nothing in the proof ever names the cursors the loop
stopped at**, so there is nothing for a second induction to be about.

The generalisable rule, which is not about matrices: **a loop lemma whose
conclusion is the invariant needs a separate exit derivation; a loop lemma whose
conclusion is the POSTCONDITION does not.** The cost is that the postcondition
must be stated at every intermediate state, which is only possible when it does
not mention the loop's own cursors — as here, where `isEchelon E rows cols`
mentions only the dimensions.

`Rat.isEchelon_of_pairs` is what makes each leaf cheap: it is a separate,
reusable induction over `isEchelonAux`'s fuel saying *the computed `Bool`
predicate is exactly the adjacent-pair condition*, and it needs no fuel bound at
all — by ADR-1571 §2's rule, because `isEchelonAux` answers `true` on exhaustion
and `true` is the conclusion.

### 2. The invariant has five clauses, and `Le pc cols` is not redundant

```text
H0 : Le pc cols
H1 : ∀ r, Lt (succ r) pr → echelonStepOk (leadingIndex M r cols)
                             (leadingIndex M (succ r) cols) cols = true
H2 : ∀ r, Lt r pr → Lt (leadingIndex M r cols) pc
H3 : ∀ s c, Le pr s → Lt s rows → Lt c pc → Eq Rat (M s c) Rat.zero
H4 : Le cols (Nat.add pc fuel)
```

ADR-1571 §3 described three clauses: H1+H2 as one ("rows `[0, pr)` have strictly
increasing leading indices all below `pc`"), H3, and H4. Two corrections came
out of doing it.

**H1 is stated on ADJACENT PAIRS, not as strict increase.** The exit consumes
`isEchelon`, which only ever asks about adjacent pairs, so a full
strictly-increasing statement would be strictly more than is needed and would
have to be re-derived down to pairs at the exit. Splitting the "all below `pc`"
half off as H2 is what makes the boundary pair (the last placed row against the
freshly placed pivot) provable: H2 gives `Lt (leadingIndex M r cols) pc` and the
new row's leading index is `pc` exactly, so `Rat.echelonStepOk_of_lt` closes it.

**H0 is a fifth clause and is not implied by H4.** H4 bounds `pc` from BELOW
through the remaining fuel; the exit branch needs the bound the other way. It
reads `Lt (leadingIndex M r cols) pc` off H2 and has to turn it into
`Lt … cols`, and without `Le pc cols` that step is simply false. H0 costs
nothing to carry — the recursive branches are taken only when
`Nat.ble cols pc = false`, and `Lt pc cols` **is** `Le (succ pc) cols`, so the
branch condition is literally the next H0.

### 3. `pc + fuel`, not `fuel + pc` — and two exit leaves become one

`Nat.add` in this kernel recurses on its RIGHT argument. So with H4 written as
`Le cols (Nat.add pc fuel)`:

- at `fuel = 0` it is `Le cols (Nat.add pc 0)`, which is **definitionally**
  `Le cols pc` — the fuel-exhausted leaf and the `Nat.ble cols pc = true` leaf
  share one derivation, passed the same term;
- in the step it is `Le cols (Nat.add pc (succ n))`, definitionally
  `Le cols (succ (Nat.add pc n))`, and the next level wants
  `Le cols (Nat.add (succ pc) n)` — one `Nat.succ_add`.

Written the other way round (`Nat.add fuel pc`) the base case needs
`Nat.zero_add` and the two leaves do not coincide. The wrapper pays one
`Nat.zero_add` either way. **Which argument of a `Nat.add` the loop counter sits
in is a proof-cost decision, not a presentation one**, and the right question to
ask is which side the recursion consumes.

### 4. The invariant is a Rust builder, not a `Prop`

ADR-1562 §2 stated the rule for the pivot-section hypothesis — *"It is stated
inline as a Pi, never as a named `Definition`. A named `Prop` could be
well-typed and mean something else; an inline Pi in the theorem's own type
cannot."* — and it applies here with more force, because the invariant has five
clauses and is repeated in a motive.

`invariant_hyps` is a Rust function returning the five hypothesis **types**. A
reader gets the same single place to look that a named predicate would give,
while `Rat.echelonAux_isEchelon`'s type in the kernel still carries all five
clauses literally, so `kernel_declaration_projection` shows them and the fact
ledger's regex can anchor on them.

### 5. Two prerequisites ADR-1571's table did not predict

| landed here | why it was needed | ADR-1571 §3 predicted it? |
|---|---|---|
| `Rat.rowSwap_preserves_zero_range` | H3's old columns survive the swap | yes |
| `Rat.leadingIndex_congr_row` | H1/H2 survive a step over the placed rows | **no** |
| `Rat.clearBelow_rowSwap_off` | the pointwise input that congruence consumes | **no** |
| `Rat.pivotSearch_ge_start` | both of the above need `Le pr piv` | **no** |
| `Rat.isEchelon_of_pairs` | each exit leaf | it predicted an induction, not a lemma |
| `Rat.echelonStepOk_of_lt` / `_both_cols` | the two disjuncts of the test | **no** |

The one worth carrying forward is the congruence. H1 and H2 are statements about
`leadingIndex E r cols` for rows `r` the step does not touch, and the step
produces a NEW matrix. Relating the two leading indices looks like it needs the
two matrices to be equal, which is `funext` — exactly what ADR-1555 measured the
ROW form of rank invariance to need. It does not:

```text
Rat.leadingIndex_congr_row : ∀ M N r r' cols,
  (∀ j, Eq Rat (M r j) (N r' j)) →
  Eq Nat (leadingIndex M r cols) (leadingIndex N r' cols)
```

**pointwise in, pointwise out.** The scan reads one row and advances the COLUMN,
so the hypothesis it needs is the same at every fuel level and travels OUTSIDE
the induction — unlike `clearBelowAux_preserves_zero`, where the matrix itself
is rewritten each step and the hypothesis has to be re-established inside the
motive. `Rat.clearBelow_rowSwap_off` supplies the pointwise agreement directly.

Its proof also spends **no `Bool` split**. The obvious route splits on
`Nat.ble cols c`, then on `Rat.isZeroB (M r c)`, and has to re-derive the second
test's value on the other matrix in each branch. Two transports close it
instead — one moves the recursive call along the induction hypothesis, the other
moves the tested entry along the row hypothesis — because outside those two
positions the two sides are literally the same term. Generalisable: **when two
sides of an equation differ only at a fixed set of positions, rewrite at those
positions instead of case-splitting on what surrounds them.**

## Consequences

- **ADR-1554's obligation 4 is closed and all four obligations are now
  complete.** `Rat.rowEchelon_isEchelon : ∀ M rows cols, isEchelon (rowEchelon M
  rows cols) rows cols = true`, axiom-free in all four rational preludes, with
  no hypothesis on `M` or the dimensions.
- **The ADR-1562 bridge is NOT yet unconditional, and this is the honest
  statement of what remains.** `Rat.rank_eq_rankCols`, `Rat.rank_le_cols` and
  the row-form rank-nullity are still `_of_pivotSection`. Echelon form implies
  the section equation, but the implication is a separate statement and needs
  two more things: a chain argument turning ADJACENT strict increase into
  distinctness at a distance (`isEchelon` gives adjacency only), and a
  "first index satisfying the predicate" characterisation of
  `Rat.pivotRowSearchAux` analogous to
  `Rat.leadingIndexAux_eq_of_first_nonzero`. **Neither is landed.** A reader who
  wants the unconditional forms should read ADR-1562 §2 for the equation still
  owed; what has changed is that the equation is now derivable rather than
  blocked on an open obligation.
- **The dominance document's rank row.** ADR-1571 corrected it from "no `rank`
  function at all" to "built, with one open equation between its two forms".
  That is still the accurate statement — obligation 4 closing does not by itself
  close the equation — and it is left as ADR-1571 wrote it.
- **ADR-0603 grading for everything landed here**: row 1 is the general
  constructive form (the seven facts); row 2 is **empty by proof**, as for the
  whole family — the order on ℚ is decidable, every predicate here is total and
  `Bool`-valued, and there is no Markov-style boundary to refute; row 3 is
  `rat_prelude/echelon_invariant_tests.rs`, which reduces `Rat.isEchelon` to
  `true` on the reduced matrix **and to `false` on the input** at two matrices,
  so neither `rowEchelon` returning its argument nor `isEchelon` accepting
  everything would pass; row 4 is empty — no import.
- **Cost.** Measured on this host with `prelude_build_timing`; see the lane
  status file for the numbers and the run count. The twelve declarations include
  one large induction whose motive carries five hypotheses.

## Alternatives rejected

- **Proving the pivot-section equation directly and skipping `isEchelon`.**
  ADR-1562 §2 records that the section equation is strictly weaker than echelon
  form, so this was the cheaper-looking route. Rejected on measurement: the
  section still needs the leading indices of the placed rows to be pairwise
  distinct, which is the same invariant, and it would leave `isEchelon` —
  the predicate ADR-1554 named as the obligation and the one a referee reads —
  unproved. Proving the stronger statement costs the two disjunct lemmas and
  `isEchelon_of_pairs`, and nothing else.
- **Stating H1 as strict increase over all pairs of placed rows.** It is true and
  it is more than the exit needs; `isEchelon` asks only about adjacent pairs, so
  the extra strength would have to be re-derived downward at three leaves instead
  of being carried at the right shape from the start.
- **Declaring the invariant as `Rat.echelonInv : Mat → Nat → Nat → Nat → Nat →
  Prop`.** Rejected under ADR-1562 §2: a five-clause `Definition` is exactly the
  case where "well-typed and means something else" is most likely, and the
  projection a referee reads would show a name instead of the clauses.

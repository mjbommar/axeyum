# ADR-1555: `Rat.rank` is an UNCAPPED count over the row-echelon form, and rank invariance under the elementary row operations does NOT follow from the three inverse laws

Status: accepted
Date: 2026-09-02
Index-summary: `Rat.rank M rows cols` lands as a `Definition` the kernel
REDUCES — `Nat.countRange (nonzeroRowB (rowEchelon M rows cols) cols) rows`,
the number of nonzero rows of the echelon form, with "nonzero" decided by
`Rat.leadingIndex < cols`. Nine axiom-free declarations in
`rat_prelude/rank.rs`. Three things are decided. (1) The count is NOT capped
at `cols`: `min (…) cols` would make `rank ≤ cols` free, and would also make a
broken elimination unobservable — four nonzero rows in three columns would be
reported as `3` and no evaluation test could see it. A bound that holds because
the definition truncates is not a theorem about rank, so `rank_le_cols` is left
OPEN rather than bought. (2) `rank_le_rows` is unconditional and free
(`Nat.countRange_le`), because it uses no property of `rowEchelon` at all; both
degenerate dimensions land too, and `rank_zero_cols` is an EQUALITY, which is
the control a definition ignoring the leading index would fail. (3) **ADR-1554's
handoff is corrected**: rank invariance under `rowSwap`/`rowScale`/`rowAddMul`
does NOT follow from the three inverse laws, for two independent reasons —
those laws are POINTWISE and this kernel has no `funext`, so they cannot be
transported under `rank` at all; and even granting `funext` they would give
`rank (op⁻¹ (op A)) = rank A`, never `rank (op A) = rank A`. Invariance is
therefore checked where it is decidable — by reduction at concrete 2×2
matrices, ADR-0603 row 3 — and the general statement is sized here as needing
ADR-1554 obligation 4.
Index-status: accepted

Related: ADR-1554 (the row-echelon form this reads), ADR-0603 (graded statement
families), ADR-0601 (one trust anchor), the 2026-08-27 architecture review
§3a (computed, not extracted) and §3b (the two congruence regimes).

## Context

ADR-1554 landed `Rat.rowEchelon` — Gaussian elimination over ℚ as a
`Definition` the kernel reduces — together with `Rat.leadingIndex`, the
decidable `Rat.isEchelon`, and the three elementary row operations with their
inverse laws. It deliberately did not attempt `rowEchelon_isEchelon` (its
obligation 4: the loop invariant that says the output really is in echelon
form), and it did not attempt `rank`.

Its handoff named three things `rank` would need — `leadingIndex` over the rows
of `rowEchelon`, a count of the rows whose leading index is below `cols`, and
the `isZeroB` bridges — and added one claim that this ADR corrects:

> Rank INVARIANCE needs only the three inverse laws — it does **not** depend on
> obligation 4 above, and sizing it as blocked on `rowEchelon_isEchelon` would
> be wrong.

**On the retrieval evidence, stated as it was actually gathered.** This lane
did not run `shape_search` before writing the code — the existence question was
answered from `rat_prelude.rs`'s field struct and from `grep` over
`crates/`, which found `Nat.countRange` and its laws (`countRange_le`,
`countRange_congr`, `countRange_split`, `countRange_compl`) and found no `rank`
field. `shape_search` was run AFTERWARDS, on a FRESH index built in this lane's
worktree (2,130 declarations; the previous lane's own status file records a
stale binary reporting a false ABSENT, so freshness is not optional here). It
reports `--name-like rank` → exactly the five declarations this lane added, and
`--name-like nonzerorow` → exactly the four it added; `--name-contains
countRange --ns Nat` → 23. So nothing pre-existing was duplicated, and the
control is newer than the change it is being asked about — but that is a
post-hoc check, not the step 0 the contributor guide asks for, and it is
recorded as such.

## Decision 1 — `rank` is a `Nat.countRange` over the ROWS, computed

```
Rat.nonzeroRowB E cols r := Nat.ble (Nat.succ (Rat.leadingIndex E r cols)) cols
Rat.rank        M rows cols := Nat.countRange (Rat.nonzeroRowB (Rat.rowEchelon M rows cols) cols) rows
```

`echelon.rs` chose `leadingIndex = cols` for a zero row, and that convention is
load-bearing exactly here: it turns "this row is nonzero" into one strict
comparison instead of a three-way case split, and it is the only reason
`nonzeroRowB` is a plain `Nat.ble` rather than a search of its own.

The matrix comes first and the row index LAST, so `nonzeroRowB E cols` is
already the `Nat → Bool` predicate `Nat.countRange` consumes. A signature with
`r` in the middle would force a lambda at every use site, and a lambda is what
`Nat.countRange_congr` cannot see through — a small ordering decision that
decides whether the ℕ prelude's counting laws apply to `rank` at all.

Everything is computed. `rank [[1,2],[3,4]] 2 2` reduces to `2`, and the
trusted gate cannot tell you otherwise: `rank` has type
`Mat → Nat → Nat → Nat` whether it counts nonzero rows, counts every row, or
returns `0`. So the discriminating evidence is the evaluation table, not the
admission.

| matrix | echelon form | `rank` | what only this row separates |
| --- | --- | --- | --- |
| `[[1,2],[3,4]]` | `[[1,2],[0,-2]]` | `2` | kills "return `0`" |
| `[[1,2],[2,4]]` | `[[1,2],[0,0]]` | `1` | kills "return `rows`" — the zero row must be EXCLUDED |
| `[[0,0],[0,0]]` | `[[0,0],[0,0]]` | `0` | kills "return `rows`" a second way, at every row |
| `[[1,2,3],[2,4,6],[1,1,1]]` | `[[1,2,3],[0,-1,-2],[0,0,0]]` | `2` | needs the ECHELON form, not the input: the input has three nonzero rows |
| 3×3 identity | itself | `3` | separates "count nonzero rows" from "count rows below the last pivot" |

Each is asserted against a control at `want ± 1` that must FAIL to be defeq.

## Decision 2 — the count is NOT capped at `cols`

`Rat.rank M rows cols := Nat.min (countRange …) cols` would make
`rank_le_cols` free, and it would be *mathematically* harmless: rank really is
at most `cols`, so on any correct elimination the cap never fires.

It is rejected anyway. An elimination that produced four nonzero rows in three
columns would be reported as `3`, and no evaluation test could tell the
difference between a working `rowEchelon` and a broken one. That is the
"checker that cannot fail" shape `CLAUDE.md` names: the cap does not prove
`rank ≤ cols`, it makes the statement unfalsifiable. A bound that holds because
the definition truncates is not a theorem about rank.

The consequence is accepted openly: **`rank_le_cols` does not land.** It says
the echelon form has at most one pivot per column — i.e. that the leading
indices of the nonzero rows strictly increase — which is precisely
`rowEchelon_isEchelon`, ADR-1554's obligation 4.

## Decision 3 — the inverse laws do NOT give rank invariance

ADR-1554's handoff is wrong on this point, and the correction matters because
sizing the next lane off it would budget a week of proof for something that has
no route.

**Reason A — no `funext`, so the laws cannot be applied under `rank` at all.**
Every law in `echelon.rs` is stated POINTWISE, because this kernel has no
`funext` and an `Eq` between two matrices is not available:

```
Rat.rowSwap_involutive : ∀ i j M r c, rowSwap i j (rowSwap i j M) r c = M r c
```

`rank` takes the matrix as an ARGUMENT. To rewrite under it you need
`rowSwap i j (rowSwap i j M) = M` as an equation between terms of type
`Nat → Nat → Rat`, and that is exactly what a pointwise law is not. This is
structural, not a proof-search difficulty: no amount of effort turns the
pointwise law into the matrix equation in this kernel. It is the same wall
`det_congr` was built to climb (2026-08-27 architecture review §3b, the two
congruence regimes), and the analogous fix — a `rank_congr` proved by induction
through `leadingIndexAux`, `pivotSearchAux`, `clearBelowAux` and `echelonAux` —
is a lane of its own and is NOT attempted here.

**Reason B — even with `funext`, the inverse laws prove the wrong statement.**
Grant matrix equality for a moment. The three laws say each operation is
invertible, so they give

```
rank (op⁻¹ (op A)) = rank A
```

which is `rank A = rank A` with extra steps. What invariance asserts is
`rank (op A) = rank A`, relating the elimination of two DIFFERENT matrices.
The standard "bounded both ways" trick — `rank A = rank (op⁻¹ (op A)) ≤
rank (op A) ≤ rank A` — is real, and it does reduce two directions to one; but
the surviving direction `rank (op A) ≤ rank A` is a statement about what
Gaussian elimination produces, and every route to it goes through the echelon
form's correctness. The inverse laws shorten the proof; they do not start it.

**What lands instead.** Invariance is a decidable statement at a concrete
matrix, so it is checked by REDUCTION (ADR-0603 row 3): at `[[1,2],[3,4]]`
(rank 2) and `[[1,2],[2,4]]` (rank 1), for each of `rowSwap 0 1`,
`rowScale 0 3` and `rowAddMul 1 0 2`, with a control per case asserting the
operated matrix genuinely differs from the original — otherwise "the operation
is the identity" passes. The boundary is checked too: `rowScale 0 0` drops the
rank from 2 to 1, which is the `k ≠ 0` side condition of `rowScale_inverse`
showing up as a number.

## What landed

Nine declarations in `crates/axeyum-lean-kernel/src/rat_prelude/rank.rs`, every
one admitted with an EMPTY `Kernel::axiom_footprint` read from the kernel by
`the_rank_family_is_axiom_free`:

| declaration | kind | how |
| --- | --- | --- |
| `Rat.nonzeroRowB` | Definition | `ble (succ (leadingIndex E r cols)) cols` |
| `Rat.nonzeroRowB_eq_ble` | Theorem | `Eq.refl` — the defining equation |
| `Rat.nonzeroRowB_zero_cols` | Theorem | `Eq.refl` at a SYMBOLIC matrix: `ble (succ _) zero` is `false` by ι |
| `Rat.rank` | Definition | `countRange (nonzeroRowB (rowEchelon M rows cols) cols) rows` |
| `Rat.rank_eq_countRange` | Theorem | `Eq.refl` — the only route the ℕ counting laws have to `rank` |
| `Rat.rank_le_rows` | Theorem | one `Nat.countRange_le` |
| `Rat.rank_zero_rows` | Theorem | `Eq.refl` |
| `Rat.countRange_nonzeroRowB_zero` | Theorem | induction on `n`, matrix generalised |
| `Rat.rank_zero_cols` | Theorem | the above at `rowEchelon M rows 0` |

Two details are worth keeping.

`rank_le_rows` uses **no property of `rowEchelon`, `leadingIndex` or the row
operations** — a count over `[0, rows)` cannot exceed `rows` whatever the
predicate does. That is why this half of the dimension bound is free and the
other half is not, and it is a useful diagnostic: any "bound" on rank that
needs nothing about the elimination is telling you about `countRange`, not
about rank.

`rank_zero_cols` needed the matrix generalised before the induction.
`rank M rows 0` is `countRange (nonzeroRowB (rowEchelon M rows 0) 0) rows`, and
the matrix `rowEchelon M rows 0` depends on the induction variable `rows`, so
an induction done in place faces a different predicate in the step than the one
the induction hypothesis is about. `Rat.countRange_nonzeroRowB_zero` fixes `E`
first; both cases then close by ι-reduction alone, because the increment is
`bool_select_nat false 1 0` and `Nat.add` recurses on its right argument.

## ADR-0603 grading

| row | content |
| --- | --- |
| 1. general constructive form | `Rat.rank_le_rows`, `Rat.rank_zero_rows`, `Rat.rank_zero_cols` — all at symbolic matrix and symbolic dimensions |
| 2. boundary refutation | **EMPTY by proof**, for the same reason as ADR-1554: the order on the constructed rationals is decidable, `nonzeroRowB` is total and `Bool`-valued, and there is no Markov-style boundary to refute |
| 3. decidable-fragment exact form | the five-matrix evaluation table, and rank invariance under each of the three row operations at 2×2 by reduction, each with a non-vacuity control |
| 4. labeled import | none — nothing here was taken from Mathlib |

## Consequences

Open, with sizing, in the order a lane should take them:

1. **`Rat.rank_le_cols`** — blocked on ADR-1554 obligation 4. Beyond obligation
   4 it needs a counting induction: `countRange pred n ≤ leadingIndex E n cols`
   for every `n ≤ rows`, whose step is a two-case split on `pred n` using
   `echelonStepOk`'s two clauses (strict increase, or both rows zero). One lane
   on top of obligation 4, not one lane total.
2. **Rank invariance** — blocked on the same obligation, and additionally on a
   `rank_congr` (Reason A) if the route goes anywhere near rewriting a matrix
   argument.
3. **Rank-nullity** — and here the sizing is BETTER than it looks, which is the
   most useful thing in this ADR for the next lane. Do not define
   `nullity := cols - rank`; that makes rank-nullity depend on `rank ≤ cols`
   and inherits everything above. Define nullity by counting COLUMNS instead:
   a computed `Rat.isPivotColB E rows cols j` ("some row below `rows` has
   leading index exactly `j`", a bounded search of the shape `pivotSearchAux`
   already demonstrates), then

   ```
   rankCols  E rows cols := Nat.countRange (isPivotColB E rows cols) cols
   nullity   E rows cols := Nat.countRange (setCompl (isPivotColB E rows cols)) cols
   ```

   and `rankCols + nullity = cols` is `Nat.countRange_compl` — which already
   exists, `∀ p n, countRange p n + countRange (setCompl p) n = n`, and needs
   nothing whatever about echelon form. The whole content of rank-nullity then
   concentrates into the single bridge `rank = rankCols` (the number of nonzero
   ROWS equals the number of pivot COLUMNS), which is where obligation 4 is
   genuinely required and where it should be spent. That decomposition turns
   one open theorem into one free theorem plus one honest obligation.

# ADR-1185: General-row determinant expansion CLOSES — and the summand's guard had to be a recursion, not the closed form

Status: accepted
Date: 2026-08-31
Index-summary: ADR-1155 landed general-row expansion's index and range layers
and named the remainder: a summand on the whole square with a `Nat.beq`
diagonal guard, two index lemmas, two identifications, an `altSign` parity
step, and the assembly. All of it lands here, and `Rat.det_row_expansion` —
expansion along a **general** row at symbolic dimension — is admitted
axiom-free. Twenty declarations. Three corrections to ADR-1155's sizing, one
of them load-bearing: its `W` names the inner minor's row as `0` where the
double expansion needs `i`. The shape finding is that `Rat.unskip` must be a
DOUBLE `Nat.rec` and not the `Nat.ble`/`Nat.pred` closed form ADR-1155
names — the closed form leaves a stuck guard that a `Bool.rec` split cannot
reach, because reducing `ble (succ p) (succ c)` re-creates the very scrutinee
the split abstracted. With that, the row-`0` identification needs no case
split at all. **Transpose invariance is now strictly downstream.**
Index-status: accepted

## Context

[ADR-1120](adr-1120-the-general-n-determinant-is-a-function-plus-a-bound.md)
declared `Rat.det` at symbolic `n` and named four open laws.
[ADR-1135](adr-1135-a-determinant-congruence-is-what-the-absence-of-funext-costs.md)
closed `det matId n = 1` and declined to size the rest.
[ADR-1155](adr-1155-general-row-expansion-is-one-fubini-once-the-range-is-full.md)
sized general-row expansion, landed its index layer (`matSkip_zero`,
`matSkip_succ_succ`, `matSkip_comm`, `matMinor_col_comm`,
`det_minor_col_comm`) and its range layer (`sumRange_peel_head`,
`sumRange_matSkip`), and named the remainder in four pieces.

This ADR is that remainder, executed. Its route claims were **re-run, not
inherited** — `adr-1155-laplace-route-checks.py` exits 0 on this tree — because
a plan's "verified numerically" is itself a claim and one of them was false six
days ago.

## Decision

**Land the summand and close the law.** Twenty declarations in
`crates/axeyum-lean-kernel/src/rat_prelude/matrix_det.rs`, all admitted by the
trusted gate, all with an empty `Kernel::axiom_footprint`:

| declaration | statement |
| --- | --- |
| `Rat.unskip` | `Nat → Nat → Nat`, the left inverse of `matSkip` |
| `Rat.unskip_zero` | `unskip 0 q = Nat.pred q` (`Eq.refl`) |
| `Rat.unskip_succ_zero` | `unskip (succ p) 0 = 0` (`Eq.refl`) |
| `Rat.unskip_succ_succ` | `unskip (succ p) (succ q) = succ (unskip p q)` (`Eq.refl`) |
| `Rat.unskip_matSkip` | `unskip p (matSkip p k) = k` — unconditionally |
| `Rat.beq_matSkip` | `Nat.beq j (matSkip j k) = false` |
| `Rat.beq_matSkip_left` | `Nat.beq (matSkip j k) j = false` |
| `Rat.altSign_succ_add` | `altSign (add (succ n) k) = neg (altSign (add n k))` |
| `Rat.ble_flip_of_false` | `ble (succ x) y = false → ble y x = true` |
| `Rat.unskip_le` | `ble q p = true → unskip p q = q` |
| `Rat.unskip_gt` | `ble p q = true → unskip p (succ q) = q` |
| `Rat.matMinor_double_comm_lo` / `_hi` | the double minor exchange, pointwise, in each column order |
| `Rat.det_double_comm_lo` / `_hi` | … through `det_congr` |
| `Rat.mul_perm4` | `x·(a·(y·(b·d))) = y·(b·(x·(a·d)))` |
| `Rat.laplaceSummand` | the summand, on the whole square |
| `Rat.laplaceSummand_rowZero` | it is the row-`0`-then-row-`i` summand |
| `Rat.laplaceSummand_rowI` | it is the row-`i`-then-row-`0` summand |
| `Rat.laplaceSummand_diag` | `laplaceSummand A i m p p = 0` |
| **`Rat.det_row_expansion`** | **cofactor expansion along a GENERAL row** |

The headline type, read from the kernel rather than from this table:

```text
(m : AxNat) -> (A : AxNat -> AxNat -> Rat) -> (i : AxNat) ->
(AxNat.ble i m = Bool.true) ->
  Rat.det A (succ m)
    = Rat.sumRange (fun q => Rat.altSign (AxNat.add q i)
                     * (A i q * Rat.det (Rat.matMinor A i q) m)) (succ m)
```

## The shape finding: the guard has to be a recursion

ADR-1155 names the inner-column recovery function by its closed form,
`unskip p q := if Nat.ble (succ p) q then Nat.pred q else q`. That form
computes the right function — checked at all 64 pairs below 8 — and it is the
**wrong shape to reason with**, for a reason that generalises past this file.

`unskip p (matSkip p c)` then carries TWO stuck `Nat.ble` guards. Split on the
inner one with a `Bool.rec` and you do not reach the outer, because reducing
`Nat.ble (succ p) (succ c)` **re-creates `Nat.ble p c`** — the very scrutinee
the split had just abstracted away. The obvious device fails, and it fails
silently: the branch simply does not close.

Declared instead as a double `Nat.rec` — the construction `Nat.ble` and
`Nat.beq` already use — all three rows hold by ι alone:

```text
unskip zero     q        ≡ Nat.pred q
unskip (succ p) zero     ≡ zero
unskip (succ p) (succ q) ≡ succ (unskip p q)
```

and `unskip_matSkip` becomes a two-level induction with **no case split at
all**. This is `matSkip_succ_succ`'s finding (ADR-1155) arriving from the other
side: there, a `succ` could not be pushed through a stuck recursor and the
answer was a `Bool.rec`; here, a `Bool.rec` cannot reach a guard that reduction
regenerates and the answer is to make the definition structural.

A second, smaller instance of the same preference: `unskip_gt` is stated as
`ble p q = true → unskip p (succ q) = q` rather than the `Nat.pred` form the
closed definition suggests. The `pred` form's successor step ends at
`succ (Nat.pred q') = q'` and needs a further inversion; this form's successor
step **is** the induction hypothesis.

## Two devices, and they are not interchangeable

`bool_cases` (already in the file) abstracts the scrutinee out of the goal and
replaces it by each constructor. `bool_cases_eq` (new) leaves the goal alone
and hands each branch `Eq Bool cond true` / `Eq Bool cond false`.

`laplaceSummand_rowI` needs the second, and the reason is worth stating: its
two branches take **different lemmas** rather than reducing one term two ways.
Which of `q` and `k` is larger decides what `matSkip q k` is (`succ k` or `k`),
hence which `altSign` carries the extra `neg`; what `unskip (matSkip q k) q` is
(`unskip_le` or `unskip_gt`); and which orientation of the double minor
exchange applies (`det_double_comm_hi` or `_lo`). A device that rewrites the
goal cannot express that.

The `= false` branch splits again, on `q`, because `Nat.pred q` is only `q''`
once `q` is exposed as `succ q''`. That second split costs nothing:
`Nat.ble zero k ≡ true`, so `q = 0` makes the branch hypothesis `true = false`.

## Three corrections to ADR-1155's sizing

1. **Its `W` is wrong in one index, and it is load-bearing.** ADR-1155 writes
   the summand's inner minor as `matMinor (matMinor A 0 p) 0 (unskip p q)` —
   row `0`. The double expansion runs the inner expansion along row `i-1` **of
   the minor**, so it must be `i`. Caught by re-deriving the numeric check
   rather than inheriting it. The correction propagates: with row `i` there,
   the row half of the double-minor bridge is `matSkip_comm` at `a = 0` rather
   than the `Eq.refl` ADR-1155 predicts.
2. **`rowZero` needs no case split.** ADR-1155 sizes both identifications as
   "a case split each". `beq_matSkip` and `unskip_matSkip` are both
   *unconditional* along the reindexing, so `rowZero` is two rewrites. Only
   `rowI` splits.
3. **`matMinor_col_comm` does not carry the double expansion**, and ADR-1155's
   "row bridge whose row half is `Eq.refl`" understates it. That lemma keeps
   the ROW indices fixed on both sides — correct for a double expansion along
   ONE row, and not what relating two different rows needs, where `(0, i)`
   becomes `(succ i, 0)`. Two new pointwise statements were required, one per
   column order, and neither follows from it.

## What the classical route would have cost, and did not

ADR-1155 measured that the two double sums agree TERMWISE for every row index
at once, and concluded that the adjacent-swap ladder — and with it row
antisymmetry — is off the critical path. That prediction held exactly.
`det_row_expansion` is ONE induction on the dimension whose step splits on the
row; `Rat.det_succ` is the `i = 0` case **definitionally**, and there is no
transposition anywhere in the proof.

One detail buys that last part: the sign is written `altSign (q + i)` and not
`altSign (i + q)`. `Nat.add` recurses on its right argument, so `add q 0`
reduces to `q` and the `i = 0` branch is `det_succ` verbatim. The mirrored form
would need `Nat.zero_add` at the base case and again in the step.

The step is five moves on each side: `det_succ` (resp. the induction
hypothesis) opens the inner expansion, two `Rat.mul_sumRange` pulls take the
cofactor coefficients inside, `laplaceSummand_rowZero` (resp. `_rowI`)
identifies the result as the summand along `matSkip`, and the inner range is
filled out to the whole square. Then `Rat.sumRange_swap`, once. The outer step
uses `sumRange_congr_lt` rather than `sumRange_congr` because the fill needs
`Nat.ble p m' = true`, which holds only below the bound.

## The route checks, re-executable

```sh
python3 docs/research/09-decisions/adr-1155-laplace-route-checks.py   # 0 failures
python3 docs/research/09-decisions/adr-1185-laplace-summand-checks.py # 0 failures
```

The second is this ADR's, and it re-derives the summand **this lane actually
builds** rather than ADR-1155's `W` — which is how correction 1 above was
found. It carries its own controls in both directions: a wrong `unskip`
recursion must differ (49 of 64 pairs), and removing the diagonal guard must
break the assembly (126 cases). Verified to fail — 10 of its 13 checks — when
`matSkip`'s branches are swapped.

## The mutation table, both columns

ADR-1155's refined standard: **a rejected declaration and a false statement are
different findings**, and a declaration rejected while its theorem stays true
adds no coverage — its proof merely names the branches in order. Both columns
below are measured. The declaration column comes from one run with
`declare_matrix_det` rewritten to REPORT each rejection instead of
short-circuiting; the statement column from re-simulating the mutated
definition in Python (`--` section 7 of this ADR's script).

**Mutation A — `Rat.matSkip`'s two `bool_select_nat` branches swapped**, the
one ADR-1135 and ADR-1155 both use.

| declaration | declaration under mutation | statement under mutation | coverage added |
| --- | --- | --- | --- |
| `unskip` | ADMITTED | — (a `Definition`) | none, by construction |
| `unskip_zero` / `_succ_zero` / `_succ_succ` | ADMITTED | TRUE | none — they mention no `matSkip` |
| `unskip_matSkip` | REJECTED (`TypeMismatch`) | **FALSE**, 72 of 81 | **yes** |
| `beq_matSkip` | REJECTED (`TypeMismatch`) | **FALSE**, 17 of 81 | **yes** |
| `beq_matSkip_left` | not reached — its sibling in the same `declare_*` failed first | **FALSE**, 17 of 81 | yes, on the statement |
| `altSign_succ_add` | ADMITTED | TRUE | none |
| `ble_flip_of_false` | ADMITTED | TRUE | none |
| `unskip_le`, `unskip_gt` | ADMITTED | TRUE | none |
| `matMinor_double_comm_lo/hi`, `det_double_comm_lo/hi` | `UnknownConst` — confounded by the absent `matSkip_comm` | **FALSE**, 580 of 2100 | yes, on the statement |
| `mul_perm4` | ADMITTED | TRUE | none |
| `laplaceSummand` | ADMITTED | — (a `Definition`) | none |
| `laplaceSummand_rowZero` | `UnknownConst` — confounded | **FALSE**, 180 of 300 | yes, on the statement |
| `laplaceSummand_rowI` | REJECTED (`TypeMismatch`), on its own merits | **FALSE**, 166 of 300 | **yes** |
| `laplaceSummand_diag` | ADMITTED | TRUE | none, by construction |
| `det_row_expansion` | `UnknownConst` — confounded | **FALSE**, 105 of 120 | yes, on the statement |

**The honest reading of that table is that nine of the twenty declarations are
ADMITTED with their statements still true**, so this mutation says nothing
about them. That is not a gap in the proofs; it is the wrong probe for half the
work, which is about `Rat.unskip` and about `Rat`-level algebra. So a second
mutation was run.

**Mutation B — `Rat.unskip`'s `succ`/`succ` row forgets its own `succ`**, the
negative control the Python script already carries (49 of 64 pairs differ).

| declaration | declaration under mutation |
| --- | --- |
| `unskip` | ADMITTED (`Definition`s cannot fail this way) |
| `unskip_zero` / `_succ_zero` / `_succ_succ` | REJECTED (`DeclarationValueMismatch`) |
| `unskip_matSkip` | REJECTED (`TypeMismatch`) |
| `beq_matSkip`, `beq_matSkip_left` | ADMITTED — correctly, they do not mention `unskip` |
| `unskip_le`, `unskip_gt` | REJECTED (`TypeMismatch`) |
| `matMinor_double_comm_*`, `det_double_comm_*`, `mul_perm4` | ADMITTED — correctly |
| `laplaceSummand_rowZero`, `_rowI`, `det_row_expansion` | REJECTED (confounded) |

The two mutations together leave exactly four declarations untouched by either
— `altSign_succ_add`, `ble_flip_of_false`, `mul_perm4`, and
`laplaceSummand_diag` — and each is a statement about `Rat` algebra or `Nat.ble`
that genuinely does not depend on either definition.

### What the controls do NOT catch

- **No index-layer statement in this file separates a sign error**, because no
  sign appears in any of them. ADR-1155 recorded this and named
  `det_eval_example` (value `13`) as the only theorem that did.
  `det_row_expansion_evaluates_at_every_row_and_pins_the_sign` is the new one:
  it expands the same pinned 3×3 along rows 0, 1 and 2 and requires `13` each
  time, and its negative control — the same sum with the alternation shifted by
  one — must equal `-13`. That is asserted POSITIVELY rather than as a failed
  `def_eq`, because a failing `def_eq` has no early exit and a pathological
  control is a documented hazard here.
- **Neither mutation probes `Nat.ble`'s guard ORDER inside `matSkip`.**
  `det_eq_det2` remains the discriminator for that, exactly as ADR-1135 said.
- `the_laplace_summand_layer_computes` covers the two new `Definition`s, which
  the trusted gate cannot: `unskip 2 1 = 1` and `unskip 2 3 = 2` are one pair
  on purpose — identity branch and `Nat.pred` branch — so a definition taking
  either branch everywhere fails one of them, and **neither alone would**.

## Consequences

- **Transpose invariance is now strictly downstream.** ADR-1155 predicted this
  and the prediction is now cashable: `det (transpose A) n` expands along a
  column of `A`, its inner sums are `matSkip`-reindexed, and filling them to
  the full range is the same move. `Rat.det_row_expansion` gives the other half
  directly — a column of `A` is a row of `Aᵀ`.
- **ADR-1120's four-law list becomes**: two proved (`det matId n = 1`,
  general-row expansion); transpose invariance unattempted but downstream of
  landed machinery; multiplicativity still blocked on an aggregate type this
  kernel does not have (ADR-1135), which is a different kind of obstacle and
  unaffected by any of this.
- **Prefer a structural recursion to a `Nat.ble` closed form for any index
  helper that a proof will case-split on.** The two agree at every argument and
  only one of them is reachable by `Bool.rec`. This is the third time in this
  file that reduction regenerating a scrutinee has decided a shape.
- Do not reach for `Rat.matMinor_col_comm` when the two expansions use
  different rows; it is the fixed-row statement and the double exchange is
  genuinely two more lemmas.

## Cost

The `rat` prelude build measured **13.15 s** with ADR-1155's seven
declarations landed and **14.37 s** with all twenty of this lane's on top —
a 1.2 s delta across the whole summand layer, and nothing resembling the
runaway shape ADR-0584 describes. (ADR-1155's status note records the build at
31.8 s; measured here on the same commit it is 13.15 s, so that figure was
taken under lane contention and should not be used as a baseline.)

Full sweep: `cargo test -p axeyum-lean-kernel --lib rat_prelude::` —
**154 passed, 0 failed, 224.83 s**.

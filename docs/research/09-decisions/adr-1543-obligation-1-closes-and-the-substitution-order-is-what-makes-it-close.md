# ADR-1543: Determinant multiplicativity at symbolic `n` lands, and the row-substitution's recursion order is the whole reason the induction closes

Status: accepted
Date: 2026-09-02
Index-summary: ADR-1440's obligation 1 — the Cauchy–Binet expansion of
`det (A·B) n` over the function space of index maps — is closed, and with
ADR-1541's obligation 2 it gives `Rat.det_matMul : ∀ n A B,
det (matMul A B n) n = det A n * det B n`, axiom-free at a fully symbolic
dimension. Twenty-two declarations: `Rat.prodRange` and `Rat.sumMaps` (ports
of the `Int` originals, absent over ℚ and measured absent by `shape_search`),
`Rat.matSetRow`/`Rat.matSubstRows` (the cursor's row surgery),
`Rat.sumMaps_congr_mapsInto` (what carries `det_row_selection`'s `MapsInto`
hypothesis through the sum), `Rat.det_matMul_expand` and `Rat.det_matMul`.
The load-bearing design decision is `matSubstRows`'s recursion order: peeling
the OUTERMOST row first makes `matSubstRows B (succ j) s (cons k g) M` and
`matSubstRows B j (succ s) g (matSetRow s (B k) M)` the same term up to ι and
η, so the induction step needs no commutation lemma between "set row `s`" and
"substitute the rows above `s`". Peeling the innermost row first needs exactly
that lemma. Two secondary choices were measured and are recorded: `matSetRow`
uses `Rat.matId`'s `bool_select_rat` rather than a recursion on the row index,
which turns both of its equations from inductions into single rewrites; and
the cursor's row is `Nat.add s i` (offset LEFT), so `add s 0` ι-reduces and
the peeled row is literally `s`, leaving one `Nat.succ_add` as the entire
arithmetic cost of the cursor.
Index-status: accepted

Related: ADR-1541 (obligation 2, and both of its blockers being stale),
ADR-1470 (the corrected selection statement), ADR-1440 (the two obligations),
ADR-1310 (a fold is not a type), ADR-1135 (the claim this refutes over ℚ),
ADR-1120 (`Rat.det` at symbolic `n`).

## Context

[ADR-1440](adr-1440-multiplicativity-needs-a-selection-lemma-not-a-leibniz-agreement.md)
reduced `det (A·B) n = det A n · det B n` at symbolic `n` to two obligations.
[ADR-1541](adr-1541-both-blockers-on-the-selection-lemma-were-stale.md) closed
obligation 2 (the selection lemma) and measured obligation 1 as the whole
remainder, naming three things it needed and finding all three absent:

- `Rat.sumMaps` — a sum indexed by the function space `[0,m) → [0,n)`.
  `Int.sumMaps` is the template at ~1,000 lines plus a 354-line evaluation
  test module.
- `Rat.prodRange` — the coefficient of each index map is a product over rows.
- an expansion whose intermediate object is "the first `k` rows replaced by
  rows of `B` chosen by `g`", with the peeling order forced by `Int.sumMaps`'s
  successor equation consing at the FRONT.

Step 0 confirmed the two absences against a FRESH 2,048-declaration index
(`shape_search --name-like Rat.sumMaps` / `--name-like Rat.prodRange`, both
ABSENT), with `Int.sumMaps` (FOUND 5), `Int.prodRange` and `Rat.sumRange` as
same-kind positive controls in the same runs.

## Decision

Land obligation 1 and `Rat.det_matMul`. Twenty-two axiom-free declarations, in
two new modules:

`rat_prelude/sum_maps.rs` — `Rat.prodRange` with `prodRange_zero`,
`prodRange_succ`, `prodRange_shiftFront`, `prodRange_congr`;
`Rat.sumRange_mul_right` / `_mul_left`; `Rat.sumMaps` with `sumMaps_zero`,
`sumMaps_succ`, `sumMaps_congr`, `sumMaps_mul_left`, `sumMaps_mul_right`.

`rat_prelude/det_mul.rs` — `Rat.matSetRow` with `matSetRow_at` /
`matSetRow_off`; `Rat.matSubstRows` with `matSubstRows_below` /
`matSubstRows_at`; `Rat.sumMaps_congr_mapsInto`; `Rat.det_matMul_expand`;
`Rat.det_matMul`.

## Why the substitution's recursion order is the decision, not a detail

The expansion is an induction on a **cursor** — how many rows are still to be
expanded — against an **offset** — which row is next. Every step needs the
partially-substituted matrix as an actual TERM, because `Rat.det_row_smul` and
`Rat.det_row_replaced` take the reference matrix as an argument rather than as
a hypothesis. So a `matSubstRows` is unavoidable; the question is which end it
peels.

`Rat.sumMaps`'s successor equation extends its map with `cons` at the FRONT:

```text
sumMaps (m+1) n F = sumRange (fun k => sumMaps m n (fun g => F (cons k g))) n
```

so the outer summation index is the map's value at 0, i.e. the FIRST row. With
`matSubstRows` peeling the outermost row first,

```text
matSubstRows B (m+1) s g M
  = matSubstRows B m (s+1) (g ∘ succ) (matSetRow s (B (g 0)) M)
```

the right-hand side of the induction step is literally

```text
matSubstRows B (succ j) s (cons k g) M
  ≡ matSubstRows B j (succ s) g (matSetRow s (B k) M)
```

by ι-reduction (`cons k g 0 ↝ k`) and η (`fun i => cons k g (succ i)` versus
`g`). Both sides of the step are then the SAME TERM and the induction
hypothesis applies with no bridging lemma at all.

Peeling the innermost row first — the shape one writes by default, because it
reads as "substitute the rest, then fix this row" — produces
`matSetRow s h (matSubstRows B j (succ s) g M)` against the hypothesis's
`matSubstRows B j (succ s) g (matSetRow s h M)`. Those touch disjoint rows and
are pointwise equal, but not definitionally, so the step needs a commutation
lemma proved by its own induction with a case split on the row index. That
lemma is not hard; it is simply unnecessary, and only if the recursion order is
chosen against `sumMaps`'s.

**The general form worth carrying:** when an induction is going to consume an
aggregate's own successor equation, build the accompanying construction so its
recursion peels at the same END the aggregate does. The alternative is a
commutation lemma for every mismatch.

## Two secondary choices, both measured

**`Rat.matSetRow` selects, it does not recurse.** Defining `matSetRow t h M`
as `fun r c => bool_select_rat (Nat.beq r t) (h c) (M r c)` — `Rat.matId`'s own
encoding — makes `matSetRow_at` one `Nat.beq_refl` rewrite and `matSetRow_off`
one application of the hypothesis. The obvious alternative, structural
recursion on `t`, makes the first an induction on `t` and the second an
induction with a nested case split on `r`, plus a `Bool` false-elimination in
the `t = 0` leg. Same two theorems, roughly six times the term.

**The cursor's row is `Nat.add s i`, offset LEFT.** `Nat.add` recurses on its
RIGHT argument, so `add s 0` ι-reduces to `s` and the row the step peels is
literally `s` — no rewrite at the point where every lemma application needs the
index. The whole arithmetic cost of the cursor is then one `Nat.succ_add` in
`matSubstRows_at`'s successor leg and one `Nat.zero_add` at the top-level
instantiation at `s := 0`. Writing the row `add i s` instead moves the
`succ_add` onto the peel, where it is paid inside every hypothesis transport of
every step.

## Why the selection lemma needed one more lemma than expected

`Rat.det_row_selection` carries `MapsInto g n`, and ADR-1470 established that
the hypothesis is part of the proposition rather than an artefact. The sum the
expansion produces ranges over every `g : Nat → Nat` as far as the TYPE is
concerned. In fact every map `Rat.sumMaps` enumerates is a `cons` tower over
the constant-zero map and therefore does map `[0,n)` into `[0,n)` — but nothing
carries that, and `Rat.sumMaps_congr`'s pointwise hypothesis is unrestricted,
so it cannot be used to rewrite under the selection lemma.

`Rat.sumMaps_congr_mapsInto` is `sumMaps_congr` with the hypothesis weakened to
maps into the range. Its successor step must use `Rat.sumRange_congr_lt`, not
`Rat.sumRange_congr`: the bounded form's `Lt k n` is exactly what proves the
`cons`'s head lands in range. Its base case needs no `0 < n` side condition,
which is the mildly surprising part — `MapsInto` only constrains indices below
`n`, so having any such index at all gives `0 < n`, and `MapsInto (fun _ => 0) n`
holds at every `n` including `0`.

## Consequences

- `Rat.det_matMul` is the last of ADR-1120's four laws over `Rat.det`. The
  determinant is no longer a fixed-size story in this repository; `rank` still
  does not exist. The dominance document's §4.3 row and the paragraph under it
  are corrected accordingly, in place, rather than left to accumulate as a
  stale obstacle.
- The Cauchy–Binet machinery is reusable as it stands: `Rat.det_matMul_expand`
  leaves `Rat.matMul`'s inner bound `n` INDEPENDENT of the determinant's
  dimension, so it is more general than multiplicativity needs and is the right
  starting point for a non-square Cauchy–Binet should one be wanted.
- `Rat.prodRange` deliberately has no algebra beyond its own front peel and a
  congruence. The Cauchy–Binet coefficient is never evaluated: it is the same
  term in both instantiations of the expansion (at `B` and at `matId`), and the
  proof cancels it structurally rather than arithmetically. A lane that wants
  `prodRange_split`, `prodRange_mul` or a permutation lemma should port them
  from `int_prelude/prod.rs` when a consumer needs them, not speculatively.
- Cost: measured with `prelude_build_timing` on the same host, the `rat`
  prelude builds in 1.68 / 1.66 / 1.64 s after, against 1.66 / 1.63 / 1.65 s at
  the merge base — within noise. Nothing here forms a large `Nat` magnitude:
  every numeral the new declarations build is an index.

## What this does not establish

It says nothing about `rank`, about invertibility, or about Cauchy–Binet for
non-square products (`matMul A B k` is used at `k = n` throughout). It gives no
permutation type, no sign and no Leibniz formula — `Rat.sumMaps` is a
summation SCHEDULE, and the non-injective maps are killed by
`Rat.det_row_selection`, not by anything in the expansion. And it is over the
CONSTRUCTED rationals: the axiom footprint of every declaration here is empty,
read from `Kernel::axiom_footprint`.

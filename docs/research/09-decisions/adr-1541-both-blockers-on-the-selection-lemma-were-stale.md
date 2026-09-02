# ADR-1541: Both blockers ADR-1470 named on the selection lemma were stale — one was a Rust visibility wall, the other a search filed under a different topic

Status: accepted
Date: 2026-09-02
Index-summary: ADR-1470 designed the determinant selection lemma's injective
half in full, did not build it, and named two things it needed: a private
two-point swap (because `Nat.transposition`'s pointwise correctness facts are
Rust helpers taking `&mut NatDev<'_>` and `rat_prelude` runs on `IntDev`), and
a decision procedure for `InjectiveOn g n \/ (a duplicate)`, which it recorded
as absent and as "genuinely new, general-purpose infrastructure". It sized the
injective half as a full lane on its own. Both blockers dissolved. A `NameId`
has no Rust type restriction, so declaring four of `transposition.rs`'s
pointwise helpers as THEOREMS removes the first wall for every prelude
permanently; and the search engine for the second already existed as
`Nat.lnp_bounded_search`, filed under the least-number principle, which no
grep for `pigeonhole` / `exists_dup` / `not_injective` can reach. Ten
axiom-free declarations landed (five `Nat`, five `Rat`), closing ADR-1440's
obligation 2: `Rat.det_row_selection` holds with `MapsInto` and NO injectivity
hypothesis. `Rat.det_mul` did NOT land; obligation 1 (the Cauchy–Binet
expansion) is the whole remainder and needs a `Rat` analogue of
`Int.sumMaps` plus a `Rat.prodRange`, neither of which exists.
Index-status: accepted

Related: ADR-1440 (the two obligations), ADR-1470 (the corrected statement and
the route this executes), ADR-1310 (a fold is not a type), ADR-1120
(`Rat.det`).

## Context

[ADR-1440](adr-1440-multiplicativity-needs-a-selection-lemma-not-a-leibniz-agreement.md)
reduced `det (A·B) n = det A n · det B n` at symbolic `n` to two obligations.
[ADR-1470](adr-1470-the-selection-lemma-needs-mapsinto-and-the-injective-case-is-still-open.md)
corrected obligation 2's statement (the literal target is FALSE without
`MapsInto`), landed its free non-injective half, designed the injective half
step by step, and closed with:

> Sizing: this lane spent its full budget on route design plus the free half.
> The injective half is comparable in scope to `Int.prodRange_permute` itself
> … budget a full lane for it, not a continuation.

and named two prerequisites. This ADR records that both were removable at far
lower cost than either was priced at, and what that says about how they were
priced.

## Blocker 1: the Rust visibility wall was a `NameId` away

`nat_prelude/transposition.rs` has had `Nat.transposition` and its involution,
injectivity and `MapsInto` laws as `pub` `NameId` fields since Wilson's
theorem. What it did **not** have as declarations were the five *pointwise*
correctness facts — "the transposition sends `i` to `j`", "it fixes everything
above `j`", and so on. Those exist only as Rust helper functions with the
signature

```rust
pub(crate) fn transposition_eq_at_i(d: &mut NatDev<'_>, …) -> ExprId
```

`rat_prelude` runs on `IntDev`. Both implement the shared `NatOps` trait, and
Rust still will not let a function written against one concrete struct be
called with a value of the other. ADR-1470 diagnosed that correctly and drew
the wrong conclusion from it: it offered two options — generalise the helper
set to `impl NatOps`, or build a second, private, `Nat.beq`-based two-point
swap — and its route took the second.

The third option is the cheap one and it is what this lane did: **declare the
facts you need as theorems.** A `NameId` is reachable from every prelude by
construction. Four theorems, each of which is the existing helper wrapped, with
the statement given at the `Nat.transposition` CONSTANT while the helper proves
the raw case tree (the two are defeq by delta, so no bridging term is needed):

| declaration | statement |
| --- | --- |
| `Nat.transposition_at_i` | `∀ i j, transposition i j i = j` — unconditional |
| `Nat.transposition_at_j` | `∀ i j, Lt i j → transposition i j j = i` |
| `Nat.transposition_gt_j` | `∀ i j k, Lt i j → Lt j k → transposition i j k = k` |
| `Nat.transposition_eq_of_ne` | `∀ i j k, Lt i j → Not (Eq k i) → Not (Eq k j) → transposition i j k = k` |

Only the last is new work: the same five-region nested-`trichotomy` split
`declare_transposition_involutive` already runs, with the two EQUALITY regions
discharged by the `Not` hypotheses through a local `False.rec` instead of
transported. It is the one a row-swap argument actually needs, because
`Rat.det_row_swap`'s third hypothesis quantifies over every row that is
neither of the two being exchanged.

`_at_i` is unconditional and the other three are not, which is worth recording
because it is not guessable: the `i` leaf of `transposition`'s case tree is
reached with no ordering fact at all, while every other leaf sits below at
least one `Nat.ble` cut that only `Lt i j` can settle.

**The general rule.** When a prelude cannot reach another prelude's proof
step, the question is not "how do I copy it" but "does it deserve a name". A
Rust helper is private to one dev struct; a theorem is public to the kernel.
This is at least the fourth file where the `NatDev`/`IntDev` boundary has been
recorded as a wall.

## Blocker 2: the decision procedure existed, under a topic nobody searched

ADR-1470:

> **The missing decidability piece.** … Checked: no
> `not_injective`/`exists_dup`/decidable-pigeonhole lemma exists anywhere in
> `nat_prelude` (grepped `pigeonhole`, `exists_dup`, `not_injective` across
> every file in that directory …). It is buildable by induction on `n`, using a
> bounded-search sub-decision … genuinely new, general-purpose infrastructure.

The grep was competent and its answer was correct. What it could not find is a
lemma whose name says nothing about injectivity:

```text
Nat.lnp_bounded_search : ∀ Q, (∀ n, Or (Q n) (Not (Q n))) → ∀ n,
  Or (∀ k, Lt k n → Not (Q k))
     (∃ m, And (Lt m n) (And (Q m) (∀ k, Lt k m → Not (Q k))))
```

`least_number.rs`, landed for ADR-0603 row 2 on the least-number principle.
That IS the bounded search for a pointwise-decided predicate, which is the
entire content of "search `[0,n)` for a collision". `Nat.injective_on_or_duplicate`
is two nested instances of it and nothing else:

- **inner**, at a fixed `i`: `Q_i j := g j = g i`, over `[0,i)`, decided
  pointwise by `Nat.beq` (`bool_true_or_false`, then `eq_of_beq_eq_true` /
  `ne_of_beq_eq_false`). Searching STRICTLY BELOW `i` is what makes the found
  pair automatically distinct: the conclusion states `Lt a b` and no
  `Not (Eq a b)` obligation is ever discharged.
- **outer**: `R i := ∃ m, Lt m i ∧ g m = g i`, over `[0,n)`, whose pointwise
  decision IS the inner search. `R` deliberately DROPS the leastness clause
  the search returns, because the injectivity branch has to build a collision
  witness from an arbitrary pair, not a least one. The outer no-witness branch
  then yields injectivity through `Nat.trichotomy`, each strict side building
  an `R` at the larger of the two indices.

It is constructive and does not imply excluded middle: the disjunction is
decided by a bounded `Nat.beq` search, which is exactly the hypothesis
`lnp_bounded_search` requires and exactly what `Nat.lnp_unrestricted_implies_em`
shows cannot be dropped in general.

**The retrieval lesson, which is not the usual one.** CLAUDE.md's standing
advice is "search for the STEP, not the NAME". This lane's step *was* searched
for — under the words for the mathematical situation (pigeonhole, duplicate,
injectivity). The tool is filed under the TECHNIQUE (least-number principle,
bounded search). Neither vocabulary reaches the other, and no shape index
reaches it either: `lnp_bounded_search`'s conclusion head is `Or` over a
universally quantified `Q : Nat → Prop`, which matches nothing about
injectivity. So add a third question to the retrieval checklist: **what
GENERAL principle is my specific search an instance of, and is that principle
named here?**

## What landed

Ten declarations, every one with an empty `Kernel::axiom_footprint`, read from
`kernel_declaration_projection`'s own footprint column rather than from source
text.

`nat_prelude`:

- `Nat.transposition_at_i`, `_at_j`, `_gt_j`, `_eq_of_ne` (above).
- `Nat.injective_on_or_duplicate` (above).

`rat_prelude/matrix_det_mul.rs`:

- `Rat.det_congr_lt` — the ROW-bounded determinant congruence.
- `Rat.matSkip_lt_succ` — `Lt c m → Lt (matSkip p c) (succ m)`.
- `Rat.det_congr_entry_lt` — the congruence bounded on BOTH indices.
- `Rat.det_row_selection_injective` — the cursor induction.
- `Rat.det_row_selection` — **obligation 2, closed**:
  `∀ m B g, MapsInto g (succ m) → det (B∘g) (succ m) =
  det (matId∘g) (succ m) * det B (succ m)`.

Facts: `F:rat-det-row-selection`, `F:rat-det-row-selection-injective`,
`F:nat-injective-on-or-duplicate`.

### The two bounded congruences are different lemmas and neither subsumes the other

This is the part of the design that was not anticipated by any prior ADR, and
it is worth stating because a reader will assume one of them is redundant.

- **`det_congr_lt`, bounded on the ROW only** (`∀ r, Lt r n → ∀ c, …`), is
  what a REINDEXING map needs. The cursor induction's base case makes `g` the
  identity on `[0,n)` and says nothing at all about `g` above `n`, so
  `Rat.det_congr`'s unrestricted premise is unavailable — and it is unavailable
  for every map a fold over a function space produces, too.
- **`det_congr_entry_lt`, bounded on BOTH**, is what an IDENTITY LAW needs.
  `Rat.matMul_id_right` is `Lt j n → matMul A matId n i j = A i j`: bounded in
  the COLUMN and holding at every row, so the row-bounded form cannot consume
  it. Identifying `det (matMul A matId n) n` with `det A n` is exactly how
  obligation 1's expansion is turned back into `det A n` at the end, so
  obligation 1's final step needs this one and not the other.

The row-bounded form needs no `matSkip` bound lemma at all, because the
cofactor recursion reaches a column only through `Rat.matSkip`; the
entry-bounded form needs `Rat.matSkip_lt_succ` and `Rat.sumRange_congr_lt` in
place of the unrestricted `sumRange_congr`.

### Two argument orders that the field docs get wrong

Both were found by kernel rejection, not by reading, and both are now
commented at their call sites:

- `Rat.det_row_swap`'s third hypothesis is
  `∀ r, beq r i = false → beq r j = false → ∀ c, B r c = A r c` — the COLUMN
  is bound LAST, inside the two boolean hypotheses, not `∀ r c, …` as
  `RatPrelude::det_row_swap`'s doc reads.
- `Nat.transposition_injective` and `Nat.transposition_maps_into` bind
  `Lt i j` BEFORE the dimension `n`, not after it as their docs read.

And one error message worth its own line: `UnboundFVar { id: 8382 }` names
nothing, and the cause was an `Exists.rec` minor premise built as `fun h => …`
where it must be `fun w h => …` — the witness binder created and never bound.
Check the minor's arity before bisecting.

## What this ADR does NOT claim

- **`Rat.det_mul` is not proved.** Nothing here says
  `det (A·B) n = det A n · det B n`.
- ADR-1440's **obligation 1** is untouched and is now the whole remainder:
  expanding `det (A·B) n` in the rows of `A·B`, each of which is a
  `Rat.sumRange` of rows of `B`, using `Rat.det_row_multilinear` once per row.
  That produces a sum indexed by the function space `[0,n) → [0,n)` and needs
  a `Rat` analogue of `Int.sumMaps` (absent) and a `Rat.prodRange` (absent;
  only `Int.prodRange` exists). `Int.sumMaps` is 1,003 lines with a 354-line
  evaluation-test module, and it is the template.
- The `MapsInto` hypothesis on the selection lemma is **not** removable. It is
  part of the proposition: ADR-1470's counterexample (`n = 1`, `g 0 = 5`,
  `B 5 0 = 7`) stands.
- The dominance document's §2.2 row for determinant multiplicativity, "not
  comparable (2×2 vs general n)", **cannot** be re-scored on this work. The
  general-`n` product law still does not exist; what exists at general `n` is
  the selection lemma it will be built from.
- ADR-1470's sizing was wrong about the two blockers and RIGHT about the
  cursor induction itself, which is the bulk of the code here and follows its
  route step for step. Three details it did not predict: the dimension and the
  matrix must stay outside the induction with the map inside it; the base case
  needs a bounded congruence that did not exist; and the two-point swap can be
  `Nat.transposition` once its facts have names.

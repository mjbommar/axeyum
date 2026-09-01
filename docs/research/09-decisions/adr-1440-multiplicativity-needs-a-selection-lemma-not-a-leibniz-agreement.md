# ADR-1440: Determinant multiplicativity needs a SELECTION lemma, not a Leibniz agreement — and the sign is a definition, not a construction

Status: accepted
Date: 2026-09-01
Index-summary: ADR-1310 named `leibniz`-agrees-with-`det` as the hard theorem
remaining before `det (A·B) = det A · det B`. That framing is avoidable and
this lane did not need it. Take `sgnOrZero g n := det (matId∘g) n` — the sign
is then a DEFINITION with nothing to prove, and Leibniz-agreement is the
`B := matId` instance of the expansion step plus `matMul_id_right`. What is
actually left is a different statement, stated here as a rendered type: the
SELECTION lemma `det (B∘g) n = det (matId∘g) n * det B n`. Landed toward it:
**row multilinearity at symbolic dimension** — `Rat.det_row_replaced`,
`det_row_zero`, `det_row_smul`, `det_row_multilinear` — the prerequisite
ADR-1310 lists first and which nothing in this prelude supplied (what existed
was `row_add_split`, a PRIVATE two-term additivity phrased in private
builders, whose only consumer was `det_row_swap`). Plus `Rat.det_matMul_2`,
multiplicativity at dimension 2 symbolic in both matrices, which is cheap only
because `Rat.det2_mul` predates `Rat.det` and `2` is a literal. All five
admitted axiom-free. Multiplicativity at symbolic `n` is NOT proved.
Index-status: accepted

## Context

[ADR-1310](adr-1310-the-aggregate-absence-is-an-inventory-and-a-fold-is-not-a-type.md)
refuted [ADR-1135](adr-1135-a-determinant-congruence-is-what-the-absence-of-funext-costs.md)'s
"blocked by a type this kernel does not have" and listed four steps toward
`det (A·B) = det A · det B`. Three landed:

1. `Rat.det_row_expansion` — cofactor expansion along a general row.
2. `Rat.det_alternating` — `det A (succ m) = 0` when two distinct in-range
   rows agree.
3. `Rat.det_row_swap` — the sign under a row swap.

This lane was step 4. It did not close it. What follows is what landed and a
precise account of what is left, because the brief is right that a wrong
statement proved correctly is the failure mode nothing here catches.

## What landed

Five theorems in `crates/axeyum-lean-kernel/src/rat_prelude/matrix_det.rs`,
all `Declaration::Theorem`, all with an empty `Kernel::axiom_footprint` (read
from the kernel, not from a list — `every_rat_declaration_is_checked_and_axiom_free`
covers all five).

### Row multilinearity, stated extensionally

`funext` is absent, so no statement here is an `Eq` between two
`Nat → Nat → Rat` values; a matrix relationship is a hypothesis. Writing
`m` for the predecessor of the dimension throughout:

| declaration | statement |
| --- | --- |
| `Rat.det_row_replaced` | `∀ m A M h t, ble t m = true → (∀ c, M t c = h c) → (∀ r, beq r t = false → ∀ c, M r c = A r c) → det M (succ m) = sumRange (fun q => altSign (q+t) * (h q * det (matMinor A t q) m)) (succ m)` |
| `Rat.det_row_zero` | `∀ m M t, ble t m = true → (∀ c, M t c = 0) → det M (succ m) = 0` |
| `Rat.det_row_smul` | `∀ m A M z t, ble t m = true → (∀ c, M t c = z * A t c) → (∀ r, beq r t = false → ∀ c, M r c = A r c) → det M (succ m) = z * det A (succ m)` |
| `Rat.det_row_multilinear` | `∀ m A M coef t n, ble t m = true → (∀ c, M t c = sumRange (fun k => coef k c) n) → (∀ r, beq r t = false → ∀ c, M r c = A r c) → det M (succ m) = sumRange (fun k => sumRange (fun q => altSign (q+t) * (coef k q * det (matMinor A t q) m)) (succ m)) n` |

`det_row_replaced` is the workhorse and the only one that touches
`Rat.det_congr`; the other three reach it through this one. Its content is
one observation: **the row-`t` minor never mentions row `t`**, because
`Rat.beq_matSkip_left` says `matSkip t r` is never `t`, so the "agrees off
row `t`" hypothesis discharges every index the minor can reach. That is the
same fact `row_add_split` used privately, lifted from the private `rset_row`
encoding to an arbitrary hypothesis.

**No new induction anywhere.** `Rat.det_row_expansion` is already
dimension-general, so all four are straight-line at a symbolic `m` — the same
finding `det_row_swap` reported, for the same reason.

`det_row_multilinear` is the Cauchy–Binet expansion step in the form the
determinant needs it: a row of `A·B` is exactly a `Rat.sumRange` of rows of
`B`. After `det_row_replaced` its whole content is moving a `sumRange` out of
the middle of a product — two `Rat.mul_sumRange`s around one `Rat.mul_comm` —
and then `Rat.sumRange_swap`, whose binder order is
`(f, INNER bound, OUTER bound)`.

### Multiplicativity at dimension 2

`Rat.det_matMul_2 : ∀ A B, det (matMul A B 2) 2 = det A 2 * det B 2`,
symbolic in both matrices.

**It is cheap for a reason that does not generalize, and saying so is most of
its value.** The eight-variable ring identity is `Rat.det2_mul`, landed with
the fixed-dimension `matrix` module long before `Rat.det` existed, and
`Rat.det_eq_det2` already identifies `det A 2` with `det2` on the four
entries. All that remained was reducing `matMul A B 2 i j`, which works only
because `2` is a literal so `Rat.sumRange` iota-reduces to
`(0 + A i 0 * B 0 j) + A i 1 * B 1 j`; one `Rat.zero_add` per entry finishes
it. At a symbolic `n` nothing reduces at all — a recursor applied to a bare
free variable is stuck — which is precisely why the general case needs
`det_row_multilinear` and an induction over the rows.

`n = 3` is NOT done and is not cheap the same way: there is no `det3_mul`,
and that identity has eighteen variables.

## The correction to ADR-1310: the sign is a definition

ADR-1310 argued the Leibniz sum is expressible (`sumMaps n n` over all maps
`[0,n) → [0,n)`, with a `sgnOrZero g n` returning `0` at non-injective `g`),
and then flagged the wall:

> *Whether that `leibniz` agrees with `Rat.det` is a separate and hard
> theorem, and nothing here says it is cheap.*

That is a real theorem, but **it is not the obstruction, because it is a
corollary rather than an input.** Define the sign by the determinant it is
supposed to be:

```text
sgnOrZero g n  :=  det (fun r c => matId (g r) c) n
```

Nothing has to be proved about that — it is a definition, it returns `0` at
non-injective `g` for free (two rows of `matId ∘ g` coincide, so
`Rat.det_alternating` applies), and it needs no permutation type, no parity,
and no injectivity predicate. With it, Leibniz-agreement

```text
det A n = sumMaps n n (fun g => sgnOrZero g n * prodRange (fun i => A i (g i)) n)
```

is the `B := matId` instance of the expansion step below, closed by
`Rat.matMul_id_right` and `Rat.det_congr`. It stops being a separate task.

**Do not read this as "ADR-1310 was wrong."** Its `leibniz` was defined the
classical way, from a permutation's sign, and for THAT definition its warning
is correct. The move here is to choose the other definition, and the only
reason it is available is that `Rat.det_matId` and `Rat.det_alternating` were
already proved at symbolic `n`.

## What is actually left, as two statements

### Obligation 1 — the expansion

```text
∀ (n : Nat) (A B : Nat → Nat → Rat),
  det (matMul A B n) n
    = sumMaps n n (fun g => prodRange (fun i => A i (g i)) n
                            * det (fun r c => B (g r) c) n)
```

This is `Rat.det_row_multilinear` applied once per row. The induction is over
the number of rows already replaced, so its intermediate matrices are hybrids
— rows below the cursor taken from `B ∘ g`, rows above still rows of `A·B` —
and `Int.sumMaps`'s `cons` peels the FIRST index of the map, so the cursor
must run from row `0` upward with the map shifting under it. That shape, not
the multilinearity, is the work.

It also needs a carrier port: **`Rat.prodRange` and `Rat.sumMaps` do not
exist.** Measured with `shape_search --include-constructed --name-like`,
which fails on absence and prints a positive control:

```text
Rat.prodRange  -> ABSENT (positive control: any-kind=2835)
                  hint: Int.prodRange, Int.prodRangeIf, …
Rat.sumMaps    -> ABSENT (positive control: any-kind=2835)
                  hint: Int.sumMaps, Int.sumMaps_congr, Int.sumMaps_succ, …
```

ADR-1310 says "nothing structural is in the way of" a `Rat.prodRange`. **This
lane did not verify that** — it never reached obligation 1 — and it is
recorded here as an inherited claim, not a measured one.

### Obligation 2 — the selection lemma

```text
∀ (n : Nat) (B : Nat → Nat → Rat) (g : Nat → Nat),
  det (fun r c => B (g r) c) n
    = det (fun r c => matId (g r) c) n * det B n
```

**This is where the difficulty is, and it is not the statement ADR-1310
named.** With obligation 1 and this, multiplicativity follows: expand
`det (A·B)`, replace each `det (B∘g)` by `sgnOrZero g n * det B n`, pull
`det B n` out of the `sumMaps` with `sumMaps_mul_left`, and recognise what is
left as obligation 1 at `B := matId`, i.e. `det A n`.

The non-injective half is free: if `g i = g j` for distinct in-range `i`, `j`
then both `B ∘ g` and `matId ∘ g` have two equal rows and
`Rat.det_alternating` sends both sides to `0`. Getting from "`g` is not
injective on `[0,n)`" to such a pair is a bounded decidable search over
`Nat.beq` and is ordinary work, but it does not exist yet.

The injective half is the real one. The route that avoids decomposing a
permutation into transpositions is an induction on a cursor `k`:

```text
P(k) : ∀ σ, InjectiveOn σ n → MapsInto σ n → (∀ i, Nat.ble k i = true → σ i = i)
         → det (B∘σ) n = det (matId∘σ) n * det B n
```

- `P(0)`: `σ` is the identity everywhere, so `B ∘ σ` is `B` pointwise and
  `Rat.det_congr` closes it; `det (matId∘σ) n` is `Rat.det_matId`, i.e. `1`.
- `P(k) → P(k+1)`: `σ` fixes everything `≥ k+1`, so it restricts to a
  bijection of `[0,k+1)`. Pigeonhole gives `j` with `σ j = k`, and `j ≤ k`
  because `σ` fixes everything above. Then `σ' := σ ∘ (k j)` fixes everything
  `≥ k`, and `B ∘ σ'` is `B ∘ σ` with rows `k` and `j` exchanged — so
  `Rat.det_row_swap` relates the two determinants with the SAME sign change on
  both sides of the identity, and `P(k)` at `σ'` closes it. When `k = j` the
  swap is trivial and there is no sign.
- The theorem is `P(n)` after normalising `σ` to the identity outside `[0,n)`,
  which costs one `Rat.det_congr`.

Three things that route needs and that this lane confirmed are or are not
present:

- `Nat.injective_on_imp_surjective_on` — **present**, and it is the exact
  pigeonhole `Int.prodRange_permute`'s successor step already uses.
- A transposition `Nat → Nat` and its injectivity — **absent as a named
  declaration.** `shape_search --name-contains swap` returns twelve matches,
  none of them a transposition function. `prod.rs` builds one INLINE inside
  `permute_branch_swap` (`point_swap_eq_between`, `override_eq_gt`), which is
  this repository's hiding place 2: extract it rather than re-deriving it.
- The whole skeleton is `Int.prodRange_permute`'s, with a sign carried. That
  is the transport this repository keeps finding: same proof skeleton, other
  aggregate, other prelude.

**This is a claim about ONE route.** Per the standing rule that a handoff's
"blocked on X" is reliably pessimistic, a later lane should verify each named
prerequisite in-tree and ask whether a different route avoids it, rather than
budgeting to build these three.

## Data points the brief asked for

- **`Rat.det_congr` — needed.** Once, inside `det_row_replaced`, to turn the
  pointwise minor identity into a determinant identity. `det_alternating`
  needed none; `det_row_swap` needed two; this needs one. The pattern is not
  "sometimes yes, sometimes no" — it is that `det_congr` is needed exactly
  when a proof relates a minor to a matrix named somewhere else, which is a
  property of the step and not of the theorem.
- **`Rat.prodRange` — not needed for what landed**, because obligation 1 was
  not reached. Absent from the tree; nothing observed to block it, nothing
  measured either.
- **The `leibniz`-agrees-with-`det` difficulty — did not arise**, and the
  reason is the definitional choice above rather than a better proof.

## Consequences

- Row multilinearity is now public surface and is general: nothing in the four
  theorems mentions matrix multiplication. Any argument that changes one row of
  a matrix — Gaussian elimination, Cramer, the adjugate, the characteristic
  polynomial's leading coefficient — can use them directly.
- `row_add_split` stays private and stays where it is. It is not subsumed:
  its two-layer `wrapped_matrix` shape is what `det_row_swap` needs and the
  extensional form would make that proof longer, not shorter.
- The next lane on this target should do obligation 2 FIRST, not obligation 1.
  Obligation 1 is a port plus a hybrid-matrix induction — long, but every
  ingredient is in the tree. Obligation 2 needs a new combinatorial argument,
  and if it does not close then obligation 1 buys nothing.

## What this ADR does NOT claim

- Multiplicativity at symbolic `n` is not proved.
- `sgnOrZero` is not declared. The definitional choice above is an argument,
  not landed code.
- Neither obligation is attempted. Their statements are written out so a later
  lane can disagree with them before spending a day on them.
- The `n = 2` theorem says nothing about the general case and was not a step
  toward it.

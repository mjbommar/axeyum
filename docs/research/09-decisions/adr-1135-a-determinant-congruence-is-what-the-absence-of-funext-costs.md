# ADR-1135: The first general-`n` determinant law needs a pointwise `det` congruence, which is exactly what the absence of `funext` costs

Status: accepted
Date: 2026-08-31
Index-summary: ADR-1120 left four laws open over `Rat.det` and named the
blocker as "an induction relating minor structure across dimensions". The
blocker is narrower and it is ONE lemma. `Rat.det`'s recursive call is at the
MINOR, so any induction over the dimension arrives at a matrix that is only
POINTWISE the one the induction hypothesis is about -- `matMinor matId 0 0` is
the identity at every index pair and is not the same term -- and this kernel
has no `funext`, so the matrix argument cannot be rewritten. `Rat.det_congr :
forall n A B, (forall r c, A r c = B r c) -> det A n = det B n` supplies it,
with the dimension quantified OUTERMOST so the induction hypothesis is
applicable at a DIFFERENT pair of matrices. Given that, `det matId n = 1` at
symbolic `n` is a short induction: the tail dies definitionally, the surviving
term's coefficients reduce to `Rat.one`, `det_congr` recognises the minor.
Records the measured limits: the new law is NOT a stronger check on the index
shift or the sign than `det_eq_det2` already is, and multiplicativity is
blocked on a Cauchy-Binet-shaped obstruction this kernel cannot express.
Index-status: accepted

## Context

[ADR-1120](adr-1120-the-general-n-determinant-is-a-function-plus-a-bound.md)
landed `Rat.det`, the determinant over the constructed rationals at general
`n`, and closed with four named-but-unproved laws:

1. `det matId n = 1` at symbolic `n`
2. transpose invariance, `det (transpose A) n = det A n`
3. expansion along a general row, not only row 0
4. multiplicativity, `det (A*B) n = det A n * det B n`

Its module doc attributed all four to the same cause: each "needs an induction
over the minor structure and [is] honestly out of scope for this file".

That attribution is right about *where* the difficulty is and wrong about
*what* it is. The difficulty is not the induction. It is that the induction
cannot be stated.

## The obstruction, precisely

`Rat.det`'s recursion is

```text
det A 0        = 1
det A (m+1)    = sum over j < m+1 of altSign j * (A 0 j * det (matMinor A 0 j) m)
```

The recursive call is at a **different matrix**. So an induction on the
dimension whose hypothesis is about some matrix `M` arrives, in the successor
case, needing a fact about `matMinor M 0 j` instead.

For `det matId n = 1` the minor in question is `matMinor matId 0 0`, and it
*is* the identity — at every index pair:

```text
matMinor matId 0 0 r c
  = matId (matSkip 0 r) (matSkip 0 c)     -- by definition
  = matId (succ r) (succ c)               -- Nat.ble 0 r is definitionally true
  = matId r c                             -- Nat.beq (succ r) (succ c) is Nat.beq r c
```

Every one of those steps is a definitional reduction, so
`Rat.matMinor_matId : forall r c, matMinor matId 0 0 r c = matId r c` is
`Eq.refl`. What it is *not* is an equation between two matrices. It is a `Pi`
over two `Nat` indices, because **this kernel has no `funext`** (positive
control of the same kind, present: `congrFun`), and therefore no route from
"agrees at every index pair" to "is the same function".

So the induction hypothesis, which is about `det matId m`, cannot be applied
to `det (matMinor matId 0 0) m`. The two matrix arguments are pointwise equal
and syntactically different, and nothing in the kernel bridges that.

## Decision

**`Rat.det` gets its own congruence, and every law over the general-`n`
determinant goes through it.**

```text
Rat.det_congr : forall n A B, (forall r c, A r c = B r c) -> det A n = det B n
```

Two shape choices are load-bearing.

**The dimension is quantified OUTERMOST, and the matrices live under the
`Nat.rec` motive.** The motive is

```text
fun n => forall A B, (forall r c, A r c = B r c) -> det A n = det B n
```

rather than a motive with `A` and `B` fixed outside the induction. This is
forced: the successor step applies the induction hypothesis at
`matMinor A 0 c` / `matMinor B 0 c`, a *different* pair of matrices from the
`A` / `B` it started with. A motive that fixed them would give an induction
hypothesis that cannot be used.

**The hypothesis is pointwise, and cannot be strengthened.** The unhypothesized
form `forall n A B, det A n = det B n` is false, and this ADR's suite exhibits
two matrices built by the same machinery that separate it (`det matId 3` is
`1`, `det (matMinor matId 0 1) 2` is `0`).

The successor step is then ordinary: `Rat.sumRange_congr` on the two cofactor
sums, with the per-index obligation splitting into the entry (`h 0 c`) and the
minor determinant (the induction hypothesis). The premise the induction
hypothesis wants at the minors is `fun r c' => h (matSkip 0 r) (matSkip c c')`
— well-typed with no bridging lemma, because `Rat.matMinor` delta-beta-reduces
to exactly that application.

## What landed

Four declarations in `crates/axeyum-lean-kernel/src/rat_prelude/matrix_det.rs`,
all admitted by the trusted gate on the first attempt, all with an empty
`Kernel::axiom_footprint`:

| declaration | statement |
| --- | --- |
| `Rat.sumRange_head_of_tail_zero` | `forall f n, (forall k, f (k+1) = 0) -> sumRange f (n+1) = f 0` |
| `Rat.det_congr` | `forall n A B, (forall r c, A r c = B r c) -> det A n = det B n` |
| `Rat.matMinor_matId` | `forall r c, matMinor matId 0 0 r c = matId r c` |
| `Rat.det_matId` | `forall n, det matId n = 1` |

`sumRange_head_of_tail_zero` exists because `Rat.sumRange` peels from the
**right** (`sumRange f (j+1) = sumRange f j + f j`), so its defining equations
hand you the LAST summand and nothing in this prelude hands you the first. The
cofactor expansion of the identity is supported at index 0 alone, so that is
exactly the shape needed.

With those, `det_matId` is a short induction:

1. The tail dies **definitionally**: `matId 0 (k+1)` reduces to `Rat.zero`,
   because `Nat.beq 0 (k+1)` iota-reduces to `false` and `matId` is a
   `Bool.rec`. Each such summand is `sign * (0 * _)`, killed by `mul_comm` and
   `mul_zero`.
2. The surviving `j = 0` term is `1 * (1 * det (matMinor matId 0 0) n)`,
   because `altSign 0` and `matId 0 0` both reduce to `Rat.one`.
3. `det_congr` along `matMinor_matId` carries the minor to `det matId n`, and
   the induction hypothesis closes it.

Every magnitude formed is `0` or `1`, so none of this touches the unary-numeral
cost documented in `CLAUDE.md`.

Facts: `F:rat-det-mat-id-general-n`, `F:rat-det-congr-pointwise`,
`F:rat-sum-range-head-of-tail-zero`.

## What the new law does NOT add, measured

This matters more than the theorem, because the natural reading is wrong.

**`det_matId` is not a stronger check on the index shift or the sign than
`det_eq_det2` already is.** ADR-1120 found by mutation that swapping
`Rat.matSkip`'s two branches is caught at `det_eq_det2`. Re-run in this lane
(mutation applied in an isolated worktree, restored afterwards, `git status`
confirmed clean): the swap makes `build_rat_prelude` fail, and because one bad
declaration poisons the shared prelude build, **every** `rat_prelude::` test
dies rather than a nameable few.

And `Rat.matMinor_matId` **survives that same mutation**, because `matSkip 0 x`
is `x` under both readings — the swap only moves which branch `ble 0 x = true`
selects, and at `p = 0` both readings give a total function that agrees with
the identity's leading minor. So the new refl lemma adds no index coverage at
all. The agreement theorem remains the discriminator.

What the new work *does* add is a general statement at symbolic `n` and a
congruence that laws 2 and 3 will reuse.

The suite's own controls are correspondingly narrow, and each says so at the
declaration: `matMinor matId 0 1 0 0 != matId 0 0` rules out a `matSkip` that
ignores the deleted index; `det (matMinor matId 0 1) 2 != 1` rules out a `det`
that returns `1` regardless of its matrix; `sumRange (fun _ => 1) 2 != 1` rules
out a `sumRange` that collapses to its head. Each is paired with a positive on
an adjacent ground term, which is what makes it non-vacuous — the same `def_eq`
call returns both answers on inputs differing in one index. **None of the three
separates a sign flip**, because `det (matMinor matId 0 1) 2` is `0` and
`neg 0 = 0`; `det_eval_example`, whose value is `13`, is the theorem that does.

## The remaining three laws

**Transpose invariance and general-row expansion are not blocked by a missing
type, unlike multiplicativity — but neither was attempted here and neither is
sized.** `Rat.transpose` already exists (`rat_prelude/matrix_transpose.rs`),
stated pointwise for the same `funext` reason, and both laws will need
`det_congr` wherever they relate a minor to a matrix named elsewhere. What can
be said about the ORDER is that law 3 comes first: `det (transpose A) n`
expands along row 0 of `Aᵀ`, which is expansion along *column* 0 of `A`, and
relating that to expansion along row 0 of `A` is exactly what general-row (and
general-column) expansion provides. So transpose invariance is not a corollary
of what landed, and a lane taking law 2 directly will find itself proving law 3
inside it.

A caution, since this ADR is the kind of document that gets read as a sizing:
"not blocked by a missing type" is a statement about the obstruction below,
not a claim that either law is cheap. Neither was tried.

> **CORRECTION, 2026-08-31 ([ADR-1310](adr-1310-the-aggregate-absence-is-an-inventory-and-a-fold-is-not-a-type.md)): the paragraph below is wrong about its
> middle bullet, and the wrongness is load-bearing.** It reads:
>
> > The Cauchy-Binet / multilinearity route expands `det (A*B)` as a sum over
> > *functions* `[0,n) -> [0,n)`, then kills the non-injective ones by
> > alternation. Same missing type, one level up: the index set of the outer
> > sum is a function space, not a `Nat` range, so `Rat.sumRange` cannot
> > express it.
>
> A finite sum does not need its index set to exist as a type. It needs a
> **fold** over the index set, and a fold is a function.
> `Int.sumMaps m n F` folds `Int.add` over `F g` for every `g : [0,m) -> [0,n)`
> by `Nat.rec` with a higher-order motive -- the same trick `Rat.det` itself
> uses two sections above -- and
> **`Int.prodRange_sumRange_expand` is admitted axiom-free**:
>
> ```text
> forall n m c, prodRange (fun i => sumRange (c i) n) m
>                 = sumMaps m n (fun g => prodRange (fun i => c i (g i)) m)
> ```
>
> That IS the expansion step this bullet calls impossible.
>
> The other two bullets are wrong in the same way and are corrected in
> ADR-1310 as arguments rather than as landed work: the Leibniz sum is a
> well-formed term (`sumMaps n n` plus a `Nat.beq`-decidable injectivity
> indicator), and a factorization LENGTH is a `Nat`, so the
> elementary-operations route carries it the same way every other finite
> family here is carried.
>
> What ADR-1310 does **not** claim is that multiplicativity is cheap. The
> remaining blockers are ADR-1135's own law 3 (general-row expansion), the
> alternating property, and the sign under a row swap -- three substantial
> cofactor inductions, none of them an aggregate question. The correct
> sentence is "three theorems away", not "needs a type this kernel does not
> have".

**Multiplicativity is NOT reachable on this route, and the obstruction is
specific rather than a matter of effort.** The classical proofs all leave the
world this kernel can express:

- The Leibniz route sums over permutations of `[0,n)`. ADR-1120 already records
  that there is no type in which to write that sum — no `List`, `Finset`,
  `Prod`, or vector — and that is not a gap to be filled by a lemma.
- The Cauchy-Binet / multilinearity route expands `det (A*B)` as a sum over
  *functions* `[0,n) -> [0,n)`, then kills the non-injective ones by
  alternation. Same missing type, one level up: the index set of the outer sum
  is a function space, not a `Nat` range, so `Rat.sumRange` cannot express it.
- The elementary-operations route (reduce `A` to a product of elementary
  matrices) needs `det` of a product with an elementary matrix, plus an
  induction on a factorization whose *length* is data this kernel has no way to
  carry.

So multiplicativity is blocked on the same absence ADR-1120 identified for
Leibniz, and no amount of index arithmetic routes around it. Stating this
precisely is the point: a future lane should not spend a budget rediscovering
it, and equally should not read it as "hard" when the honest description is
"needs an aggregate type this kernel does not have". If a `List` or a
`Nat.Fin`-indexed finite-function type ever lands, multiplicativity becomes
ordinary work; until then it stays open.

## Consequences

- Every future law over `Rat.det` at symbolic `n` goes through `det_congr`
  wherever it must relate a minor to a matrix named elsewhere. Do not
  re-derive it, and do not look for `funext`.
- `Rat.sumRange_head_of_tail_zero` is declared in `matrix_det.rs` rather than
  `sum.rs`, following `Rat.sumRange_delta`'s precedent in `matrix_n.rs`:
  nothing else in this prelude sums a function supported at a single index. If
  a second consumer appears, move it.
- The four-law list from ADR-1120 becomes: one proved, two unattempted and not
  blocked by a missing type (take general-row expansion before transpose
  invariance), one blocked on a missing aggregate type with the obstruction
  named above.

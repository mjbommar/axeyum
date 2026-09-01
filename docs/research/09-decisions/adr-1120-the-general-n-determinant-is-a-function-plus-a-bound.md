# ADR-1120: The determinant at general `n` is a `Nat.rec` with a function-valued motive, and its correctness rests on agreement with `det2`/`det3`

Status: accepted
Date: 2026-08-31
Index-summary: `Rat.det : (Nat -> Nat -> Rat) -> Nat -> Rat`, the determinant
at GENERAL `n` -- linear algebra's keystone per ADR-1075's depth proposal --
lands by cofactor expansion along the first row. Two constraints decide the
shape and neither is negotiable: this kernel has no `List`/`Finset`/`Prod`/
vector type, so a matrix stays a function plus a bound and the minor is an
index reindex (`matMinor A i j r c = A (matSkip i r) (matSkip j c)`, with
`matSkip p x = if p <= x then x+1 else x`); and the recursive call is at a
DIFFERENT matrix, so the `Nat.rec` motive must be the function type
`(Nat -> Nat -> Rat) -> Rat` rather than `Rat`. The trusted gate cannot tell
you a `Definition` is wrong, so correctness rests on `det_eq_det2` and
`det_eq_det3` -- agreement with the independently written fixed-arity
determinants, SYMBOLICALLY in a universally quantified matrix -- plus four
discriminating evaluations. Mutation-verified: swapping `matSkip`'s branches
is caught by `det_eq_det2`; a wrong stated numeral is caught by the
evaluation. Records what is NOT proved (multiplicativity, transpose
invariance, general-row expansion, `det matId n = 1`) and why a closed
Leibniz form is not expressible here at all
Index-status: accepted

Related: ADR-1075 (the curriculum measurement that named this keystone),
ADR-0603 (graded statement families), ADR-0512 (`CReal`/`Rat` at trusted
surface 0).

## Context

ADR-1075 measured the kernel against the curriculum DAG and found linear
algebra the thinnest of the three destinations at 55 declarations, against
calculus at 349. Its depth proposal
(`docs/curriculum/DEPTH-PROPOSAL-number-theory-and-linear-algebra.md`) named
the gap precisely: the matrix layer had landed (`Rat.matMul` at symbolic
dimension in `rat_prelude/matrix_n.rs`, `Rat.matTranspose`, a 2x2 adjugate
inverse), but every determinant was at FIXED arity -- `Rat.det2` takes four
scalars, `Rat.det3` takes nine.

Verified before building, because a handoff's "absent" is a hypothesis: no
`detN`, `cofactor`, `adjugate` or matrix `minor` existed anywhere in the
crate, and none of the `Rat.det`/`Rat.matSkip`/`Rat.matMinor`/`Rat.altSign`
names was taken by any prelude (a prelude can declare into another's
namespace -- `int_prelude/wilson.rs` declares `Nat.inverseIndex` -- so the
check was over the whole tree, not over `rat_prelude/`).

## Decision

### The encoding is forced, not chosen

Two kernel facts decide the whole shape:

1. **There is no `List`, `Finset`, `Prod` or vector type.** The complete
   inductive list is `True/False/And/Or/Iff/Eq/Exists/Acc/Bool/Nat/Decidable`
   + `Nat.le` + `Nat.Fin` + `Char` + `Nat.Pair`. A finite family is a
   function plus a bound, which is already how `Rat.matMul` and
   `Rat.dotN` work.

   > **CORRECTION, 2026-08-31 (ADR-1310): the census is right, "forced" is
   > not.** `Nat.Pair` was declared 2026-08-29 and `Nat.Primrec` on
   > 2026-08-31; `Kernel::add_inductive` is an ordinary gate, and an
   > inductive contributes **zero** rows to `Kernel::axiom_footprint`
   > (`Inductive`/`Constructor`/`Recursor` are filtered out;
   > `TRUSTED_KINDS` is `{axiom, opaque, quotient}`). So this is an
   > INVENTORY, not a law.
   >
   > The encoding is still the right one, for a reason this item does not
   > give: `Nat.Fin` **already exists** (`nat_prelude/finite.rs`, 2026-08-23)
   > and has **zero non-test consumers** — the pigeonhole apparatus built
   > around it in the same file is stated over plain `Nat -> Nat` with
   > bounded quantifiers. The development already declined an indexed finite
   > type once. Choose function-plus-bound because it is adopted, not because
   > nothing else is available.
2. **`funext` is absent** (positive control of the same kind, present:
   `congrFun'`). A matrix equation must be stated pointwise.

So `Rat.matMinor` is exposed as a five-argument APPLIED form
(`matMinor A i j r c`), never as a matrix-valued equation -- and deleting a
row or column is an index shift rather than a copy:

```text
Rat.matSkip  p x     := if Nat.ble p x then Nat.succ x else x
Rat.matMinor A i j r c := A (matSkip i r) (matSkip j c)
```

`matSkip` is the order-preserving injection `[0,n) -> [0,n+1)` whose image
misses `p`. `Nat.ble p x` is `p <= x`, so the branch taken AT `x = p` is
`succ x` and index `p` itself is never produced.

### The `Nat.rec` motive is a function type

`det` recurses on the DIMENSION, but the recursive call is at the minor --
a different matrix. So the motive is

```text
fun _ : Nat => (Nat -> Nat -> Rat) -> Rat
```

and the matrix is applied after the recursion, not before it. This is the
only structural subtlety in the definition:

```text
det A 0        = 1
det A (succ m) = sumRange (fun j => altSign j * (A 0 j * det (matMinor A 0 j) m)) (succ m)
```

Both equations are `Eq.refl` (`Rat.det_zero`, `Rat.det_succ`).

### `altSign` is a `Nat.rec`, not a parity test

`Rat.altSign j = (-1)^j` is defined by `altSign 0 = 1`,
`altSign (succ j) = neg (altSign j)`, so both defining equations are
`Eq.refl` too. The alternative -- `if j % 2 = 0 then 1 else -1` -- would make
`altSign_succ` a parity induction for no gain AND would form a `Nat.mod` at
every summand. Every `Nat` numeral this prelude builds is unary and the
kernel's binary-literal fast path never fires, so a formed magnitude is a
real cost; every value `altSign` forms has magnitude 1.

### Correctness rests on AGREEMENT, because the gate cannot supply it

`Kernel::add_declaration` type-checks a stated type. `(Nat -> Nat -> Rat) ->
Nat -> Rat` is that type whatever the function returns, so "the kernel
accepted it" means *well-formed*, never *correct*. The evidence is therefore:

- **`Rat.det_eq_det2 : forall A, det A 2 = det2 (A 0 0) (A 0 1) (A 1 0)
  (A 1 1)`** and **`Rat.det_eq_det3 : forall A, det A 3 = det3 (A 0 0) ...
  (A 2 2)`** -- symbolic in a universally quantified matrix, not evaluations
  at one. `det2`/`det3` were declared independently of this construction, so
  the agreement pins the minor's index shift and the alternating sign at
  once. `n = 3` is where `altSign 2` must come back to `+1` (via
  `Rat.neg_neg`), which `n = 2` cannot test -- hence two facts, not one.
- **`Rat.det_one : forall A, det A 1 = A 0 0`.**
- **Four discriminating evaluations**, each closed by `Eq.refl` against an
  independently computed value: a non-symmetric 3x3 giving 13 (inverted sign
  gives -13, deleting row `j` gives -4), a singular zero-free 3x3 giving 0,
  a 4x4 giving 2 (the first dimension no fixed-arity determinant here
  reaches), and the index shift alone at `matMinor A 0 1 1 0 = 7` where a
  transposed index gives 3 and a shift on the wrong axis gives 8.

The singular case's honest limit is recorded rather than glossed: inverting
the alternating sign leaves a singular matrix singular, so it separates a
deletion bug and NOT a sign bug. A control that cannot fail is worse than no
control, and this one would have been exactly that if used for the sign.

`det_eq_det3` is proved by instantiating `det_eq_det2` at each of the three
minors; their entries reduce definitionally to `A 1 0`, `A 1 2`, ... so the
lemma's conclusion is accepted against the reduced form with no bridge lemma.

### Mutation verification

Both classes of evidence were shown to be load-bearing, in this lane's own
worktree, each mutation restored afterwards with `git diff` confirmed empty
(mutation testing in the SHARED checkout breaks other lanes' builds):

| mutation | outcome |
| --- | --- |
| swap `matSkip`'s two branches | `build_rat_prelude` fails, `DeclarationValueMismatch` at **`Rat.det_eq_det2`** |
| `det_eval_example`'s stated value 13 -> 12 | `build_rat_prelude` fails, `DeclarationValueMismatch` |

The first is the one worth noting: the AGREEMENT theorem, not any evaluation,
is what caught an index bug in the minor.

## What this does NOT establish

Stated plainly, because the surrounding literature makes it easy to assume
otherwise. None of the following is proved:

- multiplicativity (`det (AB) n = det A n * det B n`),
- transpose invariance (`det (matTranspose A) n = det A n`),
- expansion along a general row or column (only row 0 is defined),
- `det matId n = 1` at symbolic `n`,
- any behaviour of `det A n` at symbolic `n` at all beyond the two defining
  equations.

Each needs an induction relating the minor structure across dimensions, and
`sumRange`'s `Nat.rec` over a symbolic bound is where that cost lives.

A **closed Leibniz form** (`det A n = sum over permutations of ...`) is not
merely unproved but not expressible here: it quantifies over permutations of
`[0,n)`, and this kernel has no type in which to write that sum. The
function-plus-bound idiom reaches the cofactor recursion and stops there.

> **CORRECTION, 2026-08-31
> ([ADR-1310](adr-1310-the-aggregate-absence-is-an-inventory-and-a-fold-is-not-a-type.md)):
> the paragraph immediately above is wrong, and it was quoted forward into
> ADR-1135 and into two curriculum pages before anyone tested it.**
>
> A sum does not need its index set to exist as a type; it needs a **fold**
> over the index set, and a fold is a function. `Int.sumMaps m n F` folds over
> every `g : [0,m) -> [0,n)` by `Nat.rec` with a higher-order motive — which is
> the very device `Rat.det` uses for its own recursion — and
> `Int.prodRange_sumRange_expand` is an admitted, axiom-free theorem summing
> over exactly such a function space.
>
> Applied to Leibniz: the permutations of `[0,n)` are the injective maps, and
> injectivity on a bounded range is `Nat.beq`-decidable, so
> `sumMaps n n (fun g => sgnOrZero g n * prodRange (fun i => A i (g i)) n)` is
> a well-formed term in this kernel. **That construction is argued in
> ADR-1310, not built** — no `sgnOrZero` exists, and proving it agrees with
> `Rat.det` is a separate hard theorem. What is settled is only that the
> statement is writable, so "not expressible" is the wrong word.

## Consequences

- `rat_prelude/matrix_det.rs`, 15 declarations, every one axiom-free
  (`Kernel::axiom_footprint` empty, read from the environment by
  `rat_prelude_tests::the_determinant_toolkit_is_axiom_free`).
- Three facts registered: `F:rat-det-general-n-eq-det2`,
  `F:rat-det-general-n-eq-det3`, `F:rat-det-general-n-evaluates`.
- Delta heights 49/50/51 for `matSkip`+`altSign` / `matMinor` / `det`,
  continuing this prelude's "outranks everything it unfolds to" convention
  (the previous maximum was `MAT_INV2_HEIGHT` = 48).
- `rat_prelude/matrix.rs`'s `rdet2` and `rdet3` become `pub(super)` so the
  agreement theorems can state their conclusions; nothing else changed there.
- The `rat_prelude::` sweep is 149 tests, 0 failures, and the prelude build
  is 13.25 s -- unchanged in character by this module, whose formed
  magnitudes are all under 14.

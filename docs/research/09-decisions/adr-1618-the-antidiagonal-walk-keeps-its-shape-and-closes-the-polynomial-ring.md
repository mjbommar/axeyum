# ADR-1618: the antidiagonal walk keeps its shape, and closes the polynomial ring

Status: proposed
Date: 2026-09-04
Lane: `poly-commring`
Roadmap: W2-9 (polynomial rings as a structure) — the residue ADR-1609 left

Index-summary: ADR-1609 stopped 20 of 23 fields into `AlgS.CommRing` for
`R[X]` and recommended moving the build position past `Nat` arithmetic and
restating convolution as `sumRange (fun i => g i (n − i)) (succ n)`. **That
recommendation is declined on measurement, and the walk closes instead**:
twelve new declarations (`antidiagFrom_shift`, `_succ_last`, `_rev`,
`_tail_zero`, `_head`, `_mul_right`, `mul_succ`, `mulComm`, `mulOneR`,
`mulOneL`, `mulAssoc`, **`commRing`**) supply all four missing fields at the
SAME build position, with no `Nat.add`, no `Nat.sub` and **zero kernel
rejections across the whole lane**. The measurement that kills route (a): every
`sumRange` reindexing lemma in the tree is over a CONCRETE carrier folded with
that carrier's own addition (`Nat.sumRange : (Nat → Nat) → Nat → Nat`), so an
abstract `AlgS.CommRing` carrier reuses none of them — `grep sumRange` over the
three `AlgS` modules returns one hit, a comment — and the move would relocate a
1,300-line block inside `build_nat_prelude_uncached` to buy nothing. The
enabling trick is the MOTIVE, not the representation: `Nat.rec` on the first
walk index with `fun i => forall g, …` or `fun i => forall j, …`, because the
walk's successor step calls itself at `succ j` AND at a shifted family.
`mulAssoc` — ADR-1609's "the hard one", sized as needing a two-dimensional
exchange — needs no three-index machinery at all: four applications of the
convolution's own `mul_succ` recursion plus `distribL`/`distribR`, joined by one
`R.mulAssoc` and one `R.addAssoc`. **ℚ[X], ℝ[X] and ℂ[X] are now
machine-checked commutative rings**, each admitted through the trusted gate
with an empty axiom footprint. Setoid cost of the four new fields: **zero** —
every one of them would read identically over `Eq`.
Index-status: proposed

## Context

[ADR-1609](adr-1609-polynomials-modules-and-subgroups-over-the-setoid-spine.md)
built `AlgS.Poly.*`: a polynomial over an abstract `AlgS.CommRing` is a
coefficient function `Nat -> R.carrier`, and convolution is an **antidiagonal
walk**

```text
antidiagFrom g zero     j ≡ g zero j
antidiagFrom g (succ i) j ≡ R.add (g (succ i) j) (antidiagFrom g i (succ j))
```

chosen because `Nat.sub` does not exist at the `AlgS` build position (only
`LogicPrelude` does: `Nat`, `Nat.zero`, `Nat.succ`, `Nat.rec`, and nothing
else). It supplied 20 of `AlgS.CommRing`'s 23 fields and stopped, naming the
obstruction precisely:

| field | ADR-1609's missing lemma |
|---|---|
| `mulOneL` / `mulOneR` | a vanishing-tail collapse, plus a shift lemma because `j + n` cannot be written |
| `mulComm` | the reversal `antidiagFrom g n 0 ~ antidiagFrom (fun i j => g j i) n 0` |
| `mulAssoc` | "the two-dimensional exchange for a triple convolution — the hard one" |

and it recommended: *"move `AlgS.Poly` to a build position after `Nat`
arithmetic …, restate `antidiagFrom` as `sumRange (fun i => g i (n − i))
(succ n)`, and reuse the `ℚ` reindexing proofs' shape."*

This ADR is the report from taking that residue. The recommendation was tried
first, as the lane brief required, and is **declined on measurement**.

## Decision 1 — the walk keeps its shape; the build position does not move

### The measurement that decides it

Route (a)'s premise is that restating convolution over `sumRange` lets "the
standard `sumRange` reindexing lemmas apply". Three measurements say it does
not.

1. **Every `sumRange` in the tree is carrier-specific.** `Nat.sumRange` has
   type `(Nat → Nat) → Nat → Nat`; it folds with `Nat.add` over `Nat`.
   `Rat.sumRange`, `Complex.sumRange` and `CReal.sumRange` likewise fold with
   their own carrier's addition. A polynomial over an abstract
   `R : AlgS.CommRing` has coefficients in `R.carrier` and folds with `R.add`,
   so **none** of those lemmas is applicable — not one of them can even be
   stated at the abstract carrier. There is no `AlgS.sumRange`: `grep sumRange`
   across `structures_setoid.rs`, `polynomial_setoid.rs` and `module_setoid.rs`
   returns exactly **one** hit, a comment in `module_setoid.rs:1023` noting
   that `linComb` follows `Nat.sumRange`'s *convention*. Route (a) would
   therefore have to declare `AlgS.sumRange` and prove every reindexing lemma
   from scratch anyway — the identical proof obligation, in a shape whose
   induction hypothesis is *weaker* (see below).
2. **The move is not local.** `polynomial_setoid::declare_poly_setoid` is
   called at `crates/axeyum-lean-kernel/src/nat_prelude.rs:6719`;
   `declare_subtraction` (which declares `Nat.sub`) at line 8015. Moving the
   `AlgS.Poly` / `AlgS.Module` / `AlgS.Subgroup` block past it is a ~1,300-line
   relocation inside one function, in the file a concurrent lane
   (`hall-sufficiency`) was editing.
3. **The subtraction form has the weaker induction hypothesis.** ADR-1609
   already recorded the walk's advantage and it is the decisive one: because
   the two indices move *in step*, a motive `fun i => forall j, …` makes the
   induction hypothesis available at **every** second index, which is exactly
   what the successor step consumes (it recurses at `succ j`). Under
   `sumRange (fun i => g i (n − i)) (succ n)` the far index is computed from
   `n`, so peeling a term changes both the bound and the summand and the
   generalization has to be reconstructed by hand.

### What replaced it

Not a representation change — a **motive** change. Every lemma below is
`Nat.rec` on the first walk index with the motive generalized over the thing
the successor step varies:

- over the second index, `fun i => forall j, …`, when the step recurses at
  `succ j`;
- over the **cell family**, `fun i => forall g, …`, when the step consumes the
  hypothesis at a *shifted* family.

With that, no lemma here needs arithmetic at all. The far index appears exactly
once, in `antidiagFrom_succ_last`, and it appears as `succ n` — a successor of
the induction variable, not a sum.

## Decision 2 — the three reindexing lemmas, and the six declarations they need

All types below are read from `Kernel::render_lean` in
`poly_setoid_tests::the_polynomial_ring_types_render_over_an_abstract_comm_ring`,
not from this file. `W g i j` abbreviates `AlgS.Poly.antidiagFrom R g i j`.

### The shift lemma — what replaces `j + n`

```text
AlgS.Poly.antidiagFrom_shift : forall (R : AlgS.CommRing) (g : Nat -> Nat -> R.carrier) (i j : Nat),
  R.equiv (W g i (succ j)) (W (fun a b => g a (succ b)) i j)
```

Starting the walk one step along the second index is the same as walking the
shifted family from where you were. Base is `refl` (both sides reduce to
`g 0 (succ j)`); the step is one `addCongr` whose second component is the IH at
`succ j`. **This is the lemma ADR-1609 said was needed "because the index
`j + n` cannot be written without `Nat.add`"** — and it needs no `Nat.add`,
because it never names `j + n`; it moves the shift into the family instead.

### Peel the last cell

```text
AlgS.Poly.antidiagFrom_succ_last : forall R g n,
  R.equiv (W g (succ n) Nat.zero)
          (R.add (W (fun a b => g (succ a) b) n Nat.zero) (g Nat.zero (succ n)))
```

The walk's own recursion peels the FIRST cell; this peels the one it visits
last. Motive `fun n => forall g, …` — the IH is consumed at `fun a b =>
g a (succ b)`, so a motive with `g` fixed is unusable. Base is `refl`
(`W g 1 0` and `W g⁺ 0 0 + g 0 1` are the same term); the step is
shift + IH + one `addAssoc`. This lemma is not in ADR-1609's list; it is what
makes the reversal a two-line induction instead of a two-dimensional argument.

### The reversal — `mulComm`

```text
AlgS.Poly.antidiagFrom_rev : forall R g n,
  R.equiv (W g n Nat.zero) (W (fun a b => g b a) n Nat.zero)
```

Step: `W g (succ m) 0` peels to `g (succ m) 0 + W g m 1`, the shift lemma turns
the tail into `W g↑ m 0`, and the IH at `g↑` gives `W (g↑)ᵀ m 0`. On the other
side, peel-the-last applied to `gᵀ` gives `W (gᵀ)⁺ m 0 + g (succ m) 0`. **The
two families are the same lambda** — `fun a b => g b (succ a)` — so the two
sides differ by exactly one `addComm`.

`AlgS.Poly.mulComm` is then two steps: `antidiagFrom_rev` at
`fun i j => R.mul (p i) (q j)`, then `antidiagFrom_congr` with `R.mulComm` at
each cell.

### The vanishing-tail collapse — `mulOneR`, then `mulOneL`

```text
AlgS.Poly.antidiagFrom_tail_zero : forall R g,
  (forall i j, R.equiv (g i (succ j)) R.zero) ->
  forall i j, R.equiv (W g i (succ j)) R.zero

AlgS.Poly.antidiagFrom_head : forall R g,
  (forall i j, R.equiv (g i (succ j)) R.zero) ->
  forall n, R.equiv (W g n Nat.zero) (g n Nat.zero)
```

`AlgS.Poly.one R (succ j)` iota-reduces to `R.zero`, so the hypothesis at the
family `fun i j => R.mul (p i) (AlgS.Poly.one R j)` is `R.mul (p i) R.zero ~
R.zero` — **`AlgS.mul_zero`, reused by name**, reached through the prefix
projection `AlgS.CommRing.toRingS` (it is stated over `AlgS.Ring`). That is the
only new dependency this lane added: `declare_poly_setoid` now takes a
`PolyDeps { comm_ring_to_ring_s, mul_zero }`, both from
`declare_structures_s_extra`, which runs before it at every call site.

`AlgS.Poly.mulOneL` is **not** proved by a mirror collapse. The mirror family
vanishes off the `i = 0` ROW, whose one surviving cell is the LAST the walk
visits — a genuinely different induction. Commutativity is already available,
so `mulOneL` is `mulComm` then `mulOneR`, one `equivTrans` per coefficient.
Recorded so the mirror is not re-derived.

### The right-factor pull-out

```text
AlgS.Poly.antidiagFrom_mul_right : forall R g (x : R.carrier) i j,
  R.equiv (R.mul (W g i j) x) (W (fun a b => R.mul (g a b) x) i j)
```

One `distribR` per step. It is the only walk lemma `mulAssoc` needs beyond the
convolution's own recursion.

## Decision 3 — `mulAssoc` needs no three-index machinery

ADR-1609 sized `mulAssoc` as "the two-dimensional exchange for a triple
convolution — the hard one". It is not, once the convolution's own recursion is
named:

```text
AlgS.Poly.mul_succ : forall R p q n,
  R.equiv (AlgS.Poly.mul R p q (succ n))
          (R.add (R.mul (p (succ n)) (q Nat.zero))
                 (AlgS.Poly.mul R p (fun j => q (succ j)) n))
```

(the definitional peel plus one shift). `mulAssoc` is then `Nat.rec` on the
coefficient index with motive `fun n => forall p q s, …`, base `R.mulAssoc (p 0)
(q 0) (s 0)`, and a step that is four applications of `mul_succ`:

```text
((p·q)·s)(n+1) ~ (p·q)(n+1)·s0 + ((p·q)·s↑)(n)                      [mul_succ]
               ~ (p(n+1)·q0 + (p·q↑)(n))·s0 + (p·(q·s↑))(n)         [mul_succ, IH at (p, q, s↑)]
               ~ ((p(n+1)·q0)·s0 + (p·q↑)(n)·s0) + (p·(q·s↑))(n)    [distribR]

(p·(q·s))(n+1) ~ p(n+1)·(q·s)(0) + (p·(λj.(q·s)(j+1)))(n)           [mul_succ]
               ~ p(n+1)·(q0·s0) + (p·(λj. q(j+1)·s0 + (q·s↑)(j)))(n)[mul_succ under Poly.mulCongr]
               ~ p(n+1)·(q0·s0) + ((p·q↑)(n)·s0 + (p·(q·s↑))(n))    [Poly.distribL, antidiagFrom_mul_right]
```

and the two lines meet under one `R.mulAssoc` and one `R.addAssoc`. Every
ingredient except `antidiagFrom_mul_right` already existed (`Poly.mulCongr`,
`Poly.distribL`, ADR-1609).

**Why this matters beyond one field.** The three-index route — proving the
double-walk exchange `Σ_{a+b=n} Σ_{c+d=a} G c d b ~ Σ_{a+b=n} Σ_{c+d=b} G a c d`
— was explored first and reduces (after one outer reversal) to invariance of
the triple sum under a cyclic rotation of its arguments, of which the
last-two swap is free (inner reversal) and the first-two swap is the genuine
2-D exchange. That is a real obligation and it is what ADR-1609 sized. It is
also **unnecessary**: convolution's recursion plus distributivity gets there
first. Recorded so the next lane does not build the three-index machinery.

## Decision 4 — `AlgS.Poly.commRing`, and the concrete instances

```text
AlgS.Poly.commRing : AlgS.CommRing -> AlgS.CommRing
```

A `Definition` producing a genuine `AlgS.CommRing` VALUE, so
`Kernel::add_declaration` checked all 23 fields. Twelve additive fields are
`R`'s own field applied at the coefficient index (identical to
`AlgS.Poly.commGroup`); the seven multiplicative ones are `Poly.mulCongr`,
`Poly.mulAssoc`, `Poly.mulOneL`, `Poly.mulOneR`, `Poly.distribL`,
`Poly.distribR`, `Poly.mulComm`.

**Instantiated concretely** (`tests/poly_comm_ring_concrete.rs`, an integration
test because `AlgS.Poly.*` is declared long before these carriers exist):

| ring | argument | verdict |
|---|---|---|
| **ℚ[X]** | `AlgS.CommRing.ofAlg Alg.Rat.commRing` | admits, axiom footprint empty |
| **ℝ[X]** | `CReal.commRingS` (ADR-1588) | admits, axiom footprint empty |
| **ℂ[X]** | `Complex.commRingS` | admits, axiom footprint empty |

so the concrete coefficient arithmetic that already existed is now an instance
of the abstract ring, and the trusted gate re-checked all 23 laws at each
carrier. These are admitted into a test-local kernel, not landed as named
prelude declarations; landing them is a small separate step (one `BuildStep`
per prelude, no prelude-struct widening needed if the names are dropped the way
`declare_poly_setoid`'s are).

### What was found already done, and what is genuinely open

The lane brief asked for `Rat.polyEval_mul` "and its `Complex` twin".
**`Complex.polyEval_polyMul` already exists** — read from a freshly built
`shape_search` index (`declarations=3935`):

```text
Complex.polyEval_polyMul  theorem  arity=7
  Complex -> Complex -> Nat -> Nat -> Complex.polyDegreeLt
          -> Complex.polyDegreeLt -> Complex -> Complex.Equiv
```

`complex/poly.rs` builds `Complex.polyMul` as
`fun c g k => sumRange (fun i => mul (c i) (g (Nat.sub k i))) (Nat.succ k)` —
i.e. route (a)'s representation, at a build position where `Nat.sub` exists —
together with `Complex.polyDegreeLt_polyMul` and the `hornerFromTop` /
`factorQuotient` chain. So "evaluation is a ring homomorphism" is **already
landed over ℂ**, and ADR-1609's parenthetical that it is open "for the same
reason" as the abstract case is stale for ℂ and accurate only for ℚ.

`Rat.polyEval_mul` remains open. `Rat.polyEval`, `Rat.polyEval_add`,
`Rat.polyEval_smul`, `Rat.polyEval_succ`, `Rat.polyEval_zero` and
`Rat.polyEval_deg1` exist; `Rat.polyMul` and `Rat.polyDegreeLt` do not.
**Sizing**: it is a port of `complex/poly.rs`'s ~800-line chain (`polyMul`,
`polyDegreeLt_polyMul`, the diagonal reindexing, `polyEval_polyMul`) to the
`Rat` carrier, which is a lane of its own and NOT reachable from the abstract
`AlgS.Poly.mulAssoc` this lane proved — the abstract theorem is about the walk,
`Rat.polyEval_mul` would be about `Rat.sumRange` with `Nat.sub`, and the two
representations are not connected by anything in the tree. Connecting them (an
agreement lemma `AlgS.Poly.mul (ofAlg Rat.commRing) p q n ~ Rat.polyMul p q n`)
is the cheaper route and is itself a reindexing obligation of the same family.
Do not price `Rat.polyEval_mul` as small.

`Complex.factorQuotient` (the degree drop on division by a linear factor) was
**not** connected: it lives on the `sumRange`/`Nat.sub` representation, so
connecting it needs the same agreement lemma. Not cheap; not done.

## The measurement — setoid cost

ADR-1595 asks every algebra lane for this. For the four fields this lane added:

| field | what the setoid presentation adds | free under `Eq`? |
|---|---|---|
| `mulComm` | nothing — `Poly.equiv R (mul p q) (mul q p)` unfolds to `forall n, R.equiv (…) (…)`, and the `Eq` form would be an equality of lambdas | **not statable** under `Eq` |
| `mulOneL` / `mulOneR` | nothing | not statable under `Eq` |
| `mulAssoc` | nothing | not statable under `Eq` |
| the six walk lemmas | nothing — every one is a statement about a `Nat`-indexed fold and reads identically with `Eq` | n/a (they are about cells, not about the carrier's equality) |

**Setoid cost of this lane: zero.** No obligation here was created, widened or
made harder by carrying `equiv` as a field. The one place the discipline is
visible is a benefit: `AlgS.Poly.commRing`'s law fields are `AlgS.Poly.equiv R
lhs rhs`, which delta-beta reduces to a pointwise statement, so `mulComm` is
discharged coefficientwise. On the `Alg` spine the same field would be
`Eq (fun n => …) (fun n => …)`, needing `funext`, which this kernel does not
have — ADR-1609's finding, unchanged and now carried through the *whole* ring
rather than only its additive group. **No evidence to reopen ADR-1595.**

## The aggregate

| measure | value |
|---|---|
| declarations added | **12** (1 definition, 11 theorems), all under `AlgS.Poly.*` |
| `AlgS.Poly.*` roster | 15 → **27** (`PolyNames::all()` is derived from the struct, so a dropped declaration breaks a test) |
| axiom footprint | **empty on all 27**, read from `Kernel::axiom_footprint` |
| **kernel rejections during the lane** | **0** — every declaration was admitted on its first submission |
| tests added | 9 (suite 8 → 17), plus a 3-test integration suite for the concrete rings |
| negative controls | 5, each with a positive twin in the same test |
| build position moved | **no** |
| `Nat.add` / `Nat.sub` used | **none** |

Zero rejections over twelve declarations, four of them the ones a previous lane
stopped at, is the number to compare against ADR-1609's "one rejection across
58 declarations". The obstruction was never the kernel; it was the induction
motive.

## Verification

Reproducible from the tree:

```sh
# the suite -- must print a NONZERO count (17)
scripts/cargo-serialized.sh test --release -p axeyum-lean-kernel \
  --lib poly_setoid_tests -- --test-threads=4

# the concrete rings: Q[X], R[X], C[X] (3 tests)
scripts/cargo-serialized.sh test --release -p axeyum-lean-kernel \
  --test poly_comm_ring_concrete -- --test-threads=2

# nothing upstream moved
scripts/cargo-serialized.sh test --release -p axeyum-lean-kernel \
  --lib structures_setoid -- --test-threads=4
scripts/cargo-serialized.sh test --release -p axeyum-lean-kernel \
  --lib module_setoid_tests -- --test-threads=4

# the roster, against a FRESHLY BUILT binary
scripts/cargo-serialized.sh build --release -p axeyum-lean-kernel \
  --example shape_search
target/release/examples/shape_search --include-constructed \
  --name AlgS.Poly.commGroup --expect 1     # positive control, predates this lane
target/release/examples/shape_search --include-constructed \
  --name AlgS.Poly.commRing --expect 1      # this lane's headline
target/release/examples/shape_search --include-constructed \
  --ns AlgS --name-contains Poly --expect 26
```

Measured 2026-09-04 against a binary rebuilt after the lane's commits:
`declarations=3947`, up from `3935` before it — exactly the twelve declarations
added. `--name-contains Poly` returns **26**, not 27, for the reason ADR-1609
already records: `AlgS.add_add_add_comm` is declared into the `AlgS` root, not
into the sub-namespace. `AlgS.Poly.commRing` renders as
`AlgS.CommRing -> AlgS.CommRing`.

The two `checker_command`s on this lane's facts were run and **their exit
status depends on the finding**: both exit 0 at the real counts, and the same
command with the previous pinned count (`8 passed`, which
`F:algs-poly-distrib-l` carried before this lane) exits **1**.

### The mutation table

Every negative control was mutated to the honest statement (so the "mutant"
and the positive twin coincide) and the suite re-run. **Exactly the five
mutated tests died; the other twelve passed.** A control that cannot fail would
have stayed green.

| # | mutation | expected | measured |
|---|---|---|---|
| MT1 | `the_reversal_is_rejected_when_the_family_is_not_transposed`: mutant := honest | that test dies | **FAILED** |
| MT2 | `peeling_the_last_cell_is_rejected_at_the_wrong_far_index`: mutant := honest | that test dies | **FAILED** |
| MT3 | `the_tail_collapse_is_rejected_at_the_other_end_of_the_antidiagonal`: mutant := honest | that test dies | **FAILED** |
| MT4 | `the_exchange_is_rejected_with_the_inner_factors_swapped`: mutant := honest | that test dies | **FAILED** |
| MT5 | `the_ring_instance_is_rejected_when_mulonel_is_supplied_by_mulone_r`: mutant := honest | that test dies | **FAILED** |
| — | the other twelve tests, unmutated | pass | **12 passed** |
| M6 | source: `mulAssoc`'s join step instantiated at `(p(S m), s 0, q 0)` instead of `(p(S m), q 0, s 0)` | the TRUSTED GATE refuses | `declare_poly_setoid` returned `TypeMismatch`; **all 17 tests died** on the fixture's `expect` |

M6 is the documented "one bad declaration poisons the shared build" shape: a
record-field or proof-term mutation cannot kill exactly one test, which is
precisely why every negative control here carries a positive twin *in the same
test*. Without the twin, a refusal would be evidence that the reconstruction is
broken, not that the field is load-bearing.

## Related

- [ADR-1609](adr-1609-polynomials-modules-and-subgroups-over-the-setoid-spine.md)
  — built `AlgS.Poly.*`, named this residue, and recommended the build-position
  move this ADR declines.
- [ADR-1595](adr-1595-quotients-stay-setoids-and-quot-sound-stays-out.md) — the
  setoid decision this lane reports zero cost against.
- [ADR-1588](adr-1588-a-setoid-flavored-alg-spine-for-creal.md) — the `AlgS`
  spine and `CReal.commRingS`, which is ℝ[X]'s coefficient ring here.
- [ADR-1578](adr-1578-a-magma-to-field-record-spine-with-ml-int-q-instances.md)
  — `declare_record`, `Alg.Rat.commRing`, and the `FieldKind` universe rule.

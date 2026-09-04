# ADR-1606: ℝⁿ is a function carrier with the dimension in the equivalence relation, not in the type

Status: proposed
Date: 2026-09-04
Lane: `rn-carrier`
Roadmap: W2-4 (the ℝⁿ carrier), convergence point C7 — reviewers 02 (constructive analysis), 05 (geometry), and downstream 03 / 11

Index-summary: three reviewers need a finite-dimensional real
inner-product space, and the library had two fixed-dimension ones (`CPoint`,
`Complex`) and one over ℚ (`Rat.dotN`, which has no square root and so cannot
carry a norm). The obvious carrier — `Fin n → CReal` — **cannot be built in
this kernel**: `Fin` does not exist, and neither does `Subtype` or `Sigma`, so
there is nothing to carve it out of. The decision is to make a vector a
**coefficient function `Nat → CReal` plus an explicit bound**, exactly the
shape `Rat.dotN` already uses, and to **put the dimension in the equivalence
relation rather than in the type**: `RN.EqOn n u v := ∀ i, Nat.lt i n →
CReal.Equiv (u i) (v i)`. ℝⁿ is then one setoid per `n` over one carrier, and
`RN.metric : Nat → Metric` is one metric space per dimension. **58
declarations, every one with an empty `Kernel::axiom_footprint`, 24 tests in
~75 s.** The headline result is
`RN.cauchy_schwarz : ∀ u v n, ⟨u,v⟩ₙ ≤ ‖u‖ₙ·‖v‖ₙ` — **unsquared, at symbolic
dimension** — and its proof is a *generalization* of
`Metric.CPoint.dotLeSqrtMul` rather than a rebuild: the induction step at
dimension `n+1` is one application of that plane lemma at the points
`(‖u‖ₙ, uₙ)` and `(‖v‖ₙ, vₙ)`.
Index-status: proposed

## Context

Three reviewers were waiting on the same missing object.

- **02 — constructive analysis** needs it for multivariate calculus: a
  derivative of a function of several variables is a linear map, and there was
  no ℝⁿ to be linear on.
- **05 — geometry** has the plane (`creal_point.rs`, 21 335 lines) and nothing
  above it. Every one of its theorems — Varignon, Stewart, Heron, the
  orthocentre — is written coordinate by coordinate in `x` and `y`.
- **11 — applied and computational** needs it for function spaces.

What the library actually had, measured 2026-09-04 with
`shape_search --include-constructed` (3 651 declarations, positive control
`--name Metric.creal_complete --expect 1` → FOUND 1):

| existing | dimension | scalars | norm? | Cauchy–Schwarz |
|---|---|---|---|---|
| `CPoint` (`creal_point.rs`) | 2, fixed | ℝ | via `Metric.CPoint.dist` | squared, plus unsquared as of ADR-1602 |
| `Complex` (`complex.rs`) | 2, fixed | ℝ | `Complex.normSq` + `abs` | — (different multiplication) |
| `Rat.dotN` (`rat_prelude::vector`) | **symbolic** | ℚ | **impossible** (ℚ has no √) | squared only |

So the n-dimensional inner product existed, and the norm existed, and no
single object had both. `--name-like dotn` returns ten `Rat.dotN*` rows and
nothing over `CReal`; `--name-like norm` returns `Complex.normSq*` and nothing
n-dimensional.

## The decision

**A vector is a function `Nat → CReal`; the dimension is a parameter of the
equivalence relation.**

```text
RN.Vec  : Sort 1                 := Nat → CReal
RN.EqOn : Nat → Vec → Vec → Prop := fun n u v => ∀ i, Nat.lt i n → CReal.Equiv (u i) (v i)
```

Two vectors that agree below `n` **are** the same point of ℝⁿ, whatever they
do above it. That is precisely the quotient a dependent tuple type would have
provided, obtained without one — and it is obtained the way ADR-1595 decided
every quotient in this development is obtained, by a setoid rather than by
`Quot`.

Everything downstream is parameterised the same way. `RN.dot u v n` and
`RN.norm u n` take the bound LAST (matching `Rat.dotN`, so the two
n-dimensional inner products in the tree read alike); `RN.dist n u v` takes it
FIRST, so that the `Metric` record's `dist : carrier → carrier → CReal` field
is the partial application `RN.dist n` with no eta-expanding lambda in the
instance. The same is true of all eleven law fields.

### The rejected alternatives

**`Fin n → CReal`.** Ruled out by the kernel, not by taste. `Fin` does not
exist here (`grep '"Fin'` over `crates/axeyum-lean-kernel/src/` returns one
`name_str` lookup in `nat_prelude` and no declaration), and the two ways to
build it are both closed or expensive:

- as a subtype `{ i : Nat // i < n }` — **there is no `Subtype` and no
  `Sigma`/`PSigma` in this kernel** (verified 2026-09-04, `grep '"Subtype\|
  "Sigma\|"PSigma'` returns nothing), so this route does not exist at all;
- as a fresh indexed inductive family — buildable, but what it buys is an
  index type that carries its own bound, whose only use downstream would be to
  re-derive the `Nat.lt i n` hypothesis `EqOn` already carries. It also makes
  every operation an application over a dependent index, so `dot`, `add` and
  `smul` stop being ordinary function composition and every congruence needs a
  transport.

**A length-indexed vector `Vect n`.** Same objection plus a sharper one:
`CReal.sumRange` — the finite sum this entire module is built on — is
*already* `Nat.rec` on a **bound**, and its whole apparatus (`sumRange_congr`,
`sumRange_add`, `mul_sumRange`, `sumRange_le`) is stated that way. A
length-indexed carrier would be fighting the one primitive it needs, and every
one of those four lemmas would have to be restated.

**A `Nat → CReal` whose values are forced to `zero` above `n`.** That is a
different setoid (ℝ^ω with a support condition), it needs a decidable
comparison inside every definition, and it turns `RN.ofCPoint` from two
`Nat.rec` branches into an `if`-expression over `Nat.beq`.

`Rat.dotN`'s own doc comment had already recorded this decision for ℚ in one
line — *"this kernel has no product/tuple type, so a 'vector' is not reified as
its own carrier"* — and this ADR is that decision carried to ℝ, where it
additionally has to support a norm and therefore a `Metric` instance.

## The measurement

### What landed

`crates/axeyum-lean-kernel/src/rn.rs` and `src/rn/rn_tests.rs`, commits
`b37c3e5ef` and `61120f0eb`. **58 declarations** in a new `RN.*` namespace, all
admitted by `Kernel::add_declaration`, all with an empty
`Kernel::axiom_footprint`.

| group | count | what |
|---|---|---|
| `RN.CReal.*` | 10 | `CReal` facts `creal.rs` does not name (see below) |
| carrier + setoid | 5 | `Vec`, `EqOn`, refl/symm/trans |
| vector space | 12 | `zero`/`add`/`neg`/`sub`/`smul`, three congruences, four group laws |
| inner product | 10 | `dot` + zero/succ/comm/congr/add_left/add_right/smul_left/self_nonneg/two |
| norm | 6 | `norm` + nonneg/sq/congr, **`cauchy_schwarz`**, `norm_add_le` |
| metric | 9 | `dist` + six obligations, `metric : Nat → Metric`, the reduction probe |
| the `CPoint` bridge | 6 | `ofCPoint` + agreement on `dot`, `distSq`, `dist`, and both directions of the equivalence |

Read from the kernel:

```text
RN.cauchy_schwarz : (u v : RN.Vec) -> (n : Nat) ->
                    CReal.le (RN.dot u v n) (CReal.mul (RN.norm u n) (RN.norm v n))
RN.norm_add_le    : (u v : RN.Vec) -> (n : Nat) ->
                    CReal.le (RN.norm (RN.add u v) n)
                             (CReal.add (RN.norm u n) (RN.norm v n))
RN.metric         : Nat -> Metric
RN.ofCPoint_dist  : (P Q : CPoint) ->
                    CReal.Equiv (RN.dist 2 (RN.ofCPoint P) (RN.ofCPoint Q))
                                (Metric.CPoint.dist P Q)
```

### Cauchy–Schwarz: the plane lemma IS the induction step

This is the part worth reusing. ADR-1602's `Metric.CPoint.dotLeSqrtMul`
proved unsquared Cauchy–Schwarz **on the plane**, refuting a doc comment in
`creal_point.rs` that called the norm form "not expressible here". The brief
for this lane said to generalize that argument rather than rebuild it. It
generalizes more literally than expected.

Induction on the bound. At `n+1`, write `A = ⟨u,u⟩ₙ`, `C = ⟨v,v⟩ₙ`, `x = uₙ`,
`y = vₙ`. The target is

```text
⟨u,v⟩ₙ + x·y  ≤  √(A + x²) · √(C + y²)
```

The induction hypothesis bounds the first summand by `√A · √C`, so
(`add_le_add` against `le_refl (x·y)`) it suffices that

```text
√A · √C + x·y  ≤  √((A + x²)(C + y²))
```

and **that is `dotLeSqrtMul` at the two plane points `P = (√A, x)` and
`Q = (√C, y)`**. Its left side `CPoint.dot P Q` is *definitionally*
`√A·√C + x·y`; its right side is `√(⟨P,P⟩·⟨Q,Q⟩)`, and `⟨P,P⟩` is
`√A·√A + x·x`, which `CReal.mul_self_sqrt` (available because `A ≥ 0` by
`RN.dot_self_nonneg`) rewrites to `A + x²`. One `CReal.sqrt_mul` splits the
root at the end. So **the n-dimensional inequality is the 2-dimensional one
applied n times, with the norm carrying the accumulated dimensions in its
first coordinate.**

What does *not* appear is as informative. No discriminant, no minimizing
scalar `t := −B/A`, no case split on whether `⟨u,u⟩` vanishes.
`Rat.dotN_cauchy_schwarz` needs all three, and its doc comment records the
three-case shape (`A > 0`, `A = 0 ∧ C > 0`, `A = 0 ∧ C = 0`). Over `CReal`
that case split is **not available at all** — there is no `le_total`, and the
converse of `not_equiv_of_apart` is Markov's principle, which this development
neither proves nor assumes. So the plane lemma was not a convenience; it was
the only engine available.

### What the ten `RN.CReal.*` facts are, and why they are not in `creal.rs`

Six are ordinary ordered-field facts `creal.rs` happens not to name —
`zeroAdd` (it has `add_zero` and `add_comm` but no left unit), `rightDistrib`
(it has `left_distrib` only), `addNonneg`, `negUnique` (uniqueness of the
additive inverse), `eqOfSubZero`, and `negSub`. Four are about finite sums.

One of the four is the load-bearing one. **`RN.CReal.sumRangeCongrLt` is the
BOUND-RESTRICTED finite-sum congruence**:

```text
∀ f g n, (∀ i, Nat.lt i n → Equiv (f i) (g i)) → Equiv (sumRange f n) (sumRange g n)
```

`CReal.sumRange_congr` demands agreement at **every** index, and a setoid whose
equality is `EqOn n` supplies it only below `n`. So every `RN` congruence
consumes this form and none can consume the existing one. `Nat`, `Rat` and
`Complex` all have a `sumRange_congr_lt`; `CReal` did not. It costs nothing —
two applications of `CReal.sumRange_le` closed by `CReal.equiv_of_le_le`, no
new induction — which is presumably why nobody noticed it was missing.

They live under `RN.CReal.*` rather than in `creal.rs` for the reason
`metric.rs` gives for its own `Metric.CReal.*` block: `creal.rs` fuses the name
registry, the field struct, the build order and the dispatch in one 441-field
type (the 2026-08-27 architecture review), it is actively edited by other
lanes, and a new file that touches none of it is additive by construction.

### The `CPoint` bridge, and what it cost

`RN.ofCPoint P` is `Nat.rec` with `CPoint.x P` at zero and `CPoint.y P` at
every successor — two branches, no decidable comparison, because indices above
1 are irrelevant when the equality is `EqOn 2`. Cost: **six declarations, all
by `Equiv.refl` or one congruence**, because `RN.dot`'s recursion at bound 2
ι-reduces to `(0 + x_P·x_Q) + y_P·y_Q` and `CPoint.dot` is
`x_P·x_Q + y_P·y_Q`, so the entire gap is one `zeroAdd`. Agreement holds on
`dot`, on `distSq`, and on `Metric.CPoint.dist`, and the equivalence transports
**both ways** (`ofCPoint_congr` and `cpointEquiv_of_eqOn`), so `ofCPoint` is a
setoid embedding rather than merely a map.

**A full isomorphism did not land, and should not be claimed.** `RN.metric 2`
and `Metric.cpoint` have different carriers (`RN.Vec` and `CPoint`), so no
equality between the two `Metric` values is even statable without a transport
this kernel does not have. The inverse map
(`fun u => CPoint.mk (u 0) (u 1)`) and a round-trip lemma are the remaining
pieces; they are cheap and nobody needed them yet.

## Consequences

- Everything `metric.rs` states for an **arbitrary** `Metric` now reads on ℝⁿ
  with no further work: `Metric.dist_self`, `Metric.dist_quadrilateral`,
  `Metric.CauchyAt`, `Metric.Cauchy`, `Metric.TendsToAt`, `Metric.TendsTo`,
  `Metric.Complete`. `rn_tests::the_generic_metric_theorems_apply_to_rn`
  checks one of them by instantiation.
- ADR-1602's recommendation is reinforced by a second instance: the metric
  layer carried a whole new space without a topology decision being made.
- The obvious next steps are completeness of ℝⁿ (coordinatewise from
  `CReal.converges_of_cauchy`, needing the undeclared bound
  `|uᵢ − vᵢ| ≤ d(u,v)`), the linear-map layer reviewer 02 wants, and lifting
  the plane's geometry theorems to `RN` through `ofCPoint`.

## What did not land

Stated as precisely as what did.

1. **Cauchy–Schwarz in SQUARED form**, `⟨u,v⟩² ≤ ⟨u,u⟩⟨v,v⟩` — the form
   `Rat.dotN_cauchy_schwarz` and `CPoint.cauchy_schwarz` take. It needs
   `|⟨u,v⟩| ≤ ‖u‖‖v‖`, i.e. the bound at `−v` as well as at `v`, and that needs
   `⟨u, −v⟩ ~ −⟨u,v⟩`, which needs `CReal.neg_add` and `CReal.mul_neg`. **Both
   exist only as unnamed inline steps inside `creal.rs`** (`creal/series.rs`
   builds `neg (a+b) ~ neg a + neg b` privately). Declaring them is a
   `creal.rs` edit, which this lane does not own. Estimated cost once they are
   named: ~60 lines.
2. **Completeness of ℝⁿ.** See above.
3. **The inverse of `ofCPoint`, and hence a genuine isomorphism.** See above.
4. **`smul`'s vector-space laws beyond congruence.** `dot_smul_left` is proved;
   `smul_smul`, `one_smul` and the two distributivities are not, because
   nothing consumed them.

## Discipline notes

Two things in this lane are worth copying.

**Name the refused step.** `KernelError::DeclarationValueMismatch` carries two
bare `ExprId`s and no label, so a `?` chain through 55 `declare_*` calls turns
one rejection into a bisect at ~4 minutes a release build.
`build_rn_prelude` runs its steps through a `declare_each!` macro that prints
the step's own identifier and renders both types. It located all four defects
in this lane directly — a wrong arrow in `RN.smul`'s declared type and three
`equiv_symm` argument-order slips — at one build each instead of six.

**The build is the checker, for the definitions.** Mutation testing found this
and it is the honest limit of the test suite. Dropping the `sqrt` from
`RN.norm` does not make one test fail; it makes the prelude refuse at
`declare_norm_nonneg` and **all 24 tests die**, because every one of them
depends on the shared build. That is the "one bad declaration poisons the
shared build" pattern, and it means a producer mutation cannot be a
discriminating one here: every definition in this module is pinned at build
time by at least one theorem in the same prelude whose proof depends on its
exact form. So the suite's remaining jobs are (i) that the build happens,
(ii) that the *statements* are the intended ones — checked verbatim against
`Kernel::render_lean` — and (iii) that a plausible alternative structure
nobody would have written is refused: the SQUARED distance, a negated norm, a
mismatched dimension in the equivalence, a reflexivity proof for another
relation. Each of those four is paired with
`the_instance_probe_accepts_the_real_instance`, so none can pass vacuously,
and the mutation table below shows two checker mutations each killing exactly
one test.

| # | mutant | expected | observed |
|---|---|---|---|
| M1 | `RN.norm` drops the `sqrt` (producer) | prelude refused | refused at `declare_norm_nonneg`; **all 24 tests die** — a poisoned shared build, not a discriminating mutation. This is the finding. |
| M2 | drop `RN.cauchy_schwarz` from `all_declarations` (checker) | exactly 1 dies | exactly 1: `the_declaration_list_covers_every_rn_name` |
| M3 | the squared-distance control substitutes the REAL distance (checker) | exactly 1 dies | exactly 1: `a_squared_distance_is_refused_as_a_metric` |

**Teach the retrieval tools the new group.** `shape_search` and
`kernel_declaration_projection` were both blind to `Metric` before ADR-1602 and
would have reported a confident ABSENT for all 49 of its declarations. Both are
taught the `rn` group here. Checked, not assumed: the projection's `rn` block
adds **exactly 58 names** to `metric`'s, all under `RN.`, and removes none.

# ADR-1659: parallelism is stated positively, and then both coordinate planes are affine

Status: proposed
Date: 2026-09-06
Lane: `playfair`
Roadmap: W3-8 (synthetic incidence geometry with the coordinate plane as a model), third slice

Index-summary: `Geo.Affine` lands — `Geo.Incidence` plus Playfair's parallel
axiom — with **both** coordinate planes as models (`Geo.qaffine`, `Geo.raffine`)
and three theorems derived once over an arbitrary affine plane, among them
Playfair's classical corollary that parallelism is transitive. ADR-1652 § 5
sized this and predicted the shape; the prediction holds and the four ℝ helpers
it named (`defectAC`, `defectBC`, `defectSwap`, `onOfDefects`) are reused
unchanged, with `geo/rplane.rs` and `geo/qplane.rs` not edited at all. The
decision is that parallelism is a PRIMITIVE FIELD stated positively — same
direction plus a distinctness each model witnesses — and not
`Geo.Incidence.Parallel`, the classical "no common point", which is negative
and forces uniqueness through tightness. Two findings ADR-1652 did not predict.
First, **the ℝ existence half needs no division at all**: the parallel through
`P` reuses `l`'s leading coefficients so its non-degeneracy is `l`'s outright,
and its distinctness witness is the PRODUCT of two `PosBound` moduli, assembled
from `pos_of_pos_bound`/`mul_pos`/`pos_bound_of_lt` — positivity is closed under
multiplication constructively, and that one fact replaces the two
`Rat.mul_eq_zero` case analyses the ℚ existence proof needs. Second, a latent
defect in the shared `ring::rat` producer: `scale_item`'s `count == -1` branch
returns `item.negated()` but proves its conclusion at `Rat.neg it`, so
multiplying an ALREADY-NEGATED monomial by `−1` yields a proof of `… = − − X`
where the caller reads `… = X`. It is invisible to every existing caller and
was found by the kernel refusing this lane's first `parNondegPair`; it is
recorded and routed around here, not fixed.
Index-status: proposed

## Context

ADR-1635 built `Geo.Incidence` and `Geo.qplane`; ADR-1652 built `Geo.rplane`
and then **sized Playfair without landing it**, recording a wrong first answer
worth repeating because this change is that answer's correction:

> Define `Parallel l m := ∀ P, on P l → on P m → False` … Playfair's
> *uniqueness* then needs `Parallel l m → Equiv (a*B − b*A) 0`, and the only
> route from a negative hypothesis is by contradiction … That yields
> `Not (Apart (a*B − b*A) 0)`, and turning that into `Equiv (a*B − b*A) 0` is
> tightness, which `creal.rs` … says is "neither proved nor assumed".

and then:

> **a negative primitive blocks, and the fix is to state the primitive
> positively with a witness, not to acquire a classical principle.**

ADR-1652 § 5 wrote down the positive predicate, three polynomial identities
verified over 300 random tuples with exact `Fraction` arithmetic, and called
the remaining work "a *design* item, not a blocked one". This ADR records what
the design item cost when built.

## Decision

### 1. `Geo.Affine` is a record whose zeroth field is a `Geo.Incidence`

Seven fields, at `Sort 2`, through the ADR-1578 `declare_record` spine:

| # | field | type |
|---|---|---|
| 0 | `inc` | `Geo.Incidence` |
| 1 | `parPos` | `line inc → line inc → Prop` |
| 2 | `off` | `point inc → line inc → Prop` |
| 3 | `offNotOn` | `∀ P l, off P l → on inc P l → False` |
| 4 | `parPosDisjoint` | `∀ l m P, parPos l m → on inc P l → on inc P m → False` |
| 5 | `playfairExists` | `∀ P l, off P l → ∃ m, on inc P m ∧ parPos l m` |
| 6 | `playfairUnique` | `∀ P l m n, parPos l m → parPos l n → on inc P m → on inc P n → lEq inc m n` |

Nesting rather than restating twenty-one fields is what makes the incidence
layer's five derived theorems instantiate at `Geo.Affine.inc A` for free, and
`Geo.Affine.parallelPos_irrefl` below actually consumes one of them. Field 0
has type `Geo.Incidence : Sort 2`, which is the same universe situation a
`CarrierSort` field is in (`Sort 1 : Sort 2`), so it is declared with that
`FieldKind` — which is what puts the `inc` selector's recursor motive at
`Sort 2` — and the spine's own universe control still refuses the identical
field list at `Sort 1`. That control is restated in the open in `geo_tests.rs`.

Fields 5 and 6 split Playfair into existence and uniqueness for the same reason
`joinExists`/`joinUnique` split Hilbert I.1: this kernel has no `ExistsUnique`.

### 2. **The decision: `parPos` is a primitive, and it is positive**

`Geo.Incidence.Parallel` (the classical "no common point") stays exactly where
ADR-1652 left it and is **not** what `Geo.Affine` carries. `parPos` is a field,
and each model supplies the content:

| model | `parPos l m` |
| --- | --- |
| `Geo.qaffine` | `a l * b m = b l * a m`, and `((a l * c m = c l * a m) ∧ (b l * c m = c l * b m)) → False` |
| `Geo.raffine` | `Equiv (a*B − b*A) 0`, and `∃ k, PosBound ((a*C − c*A)² + (b*C − c*B)²) k` |

Read either row as *same direction, and not the same line*. Two coefficient
triples describe one line exactly when all three defects vanish; `parPos` says
the first vanishes and the other two do not both vanish. So "parallel" is
literally "proportional in direction, not proportional overall" — which is why
`Geo.QPlane.onOfProp` and `Geo.RPlane.onOfDefects`, both written for
`joinUnique`, discharge Playfair's uniqueness half with no new machinery.

`off` is the second primitive, and it is needed for the same reason one
dimension down. Playfair's existence half is "through a point NOT ON `l`", and
over ℝ the negation `on P l → False` constructs no modulus, so the existence
proof could not witness that its parallel is distinct from `l`. `Geo.RPlane.off`
is `∃ k, PosBound (e_P * e_P) k`; `Geo.QPlane.off` is the plain negation, which
over ℚ *is* usable because `Rat.mul_eq_zero` consumes it.

The relation back to the classical notion is a theorem, not an assumption:
`Geo.Affine.parallelPos_parallel : ∀ A l m, parPos A l m → Geo.Incidence.Parallel (inc A) l m`,
which is the `parPosDisjoint` field with its arguments reordered.

### 3. The three derived theorems, and why `parallel_trans` carries a hypothesis

```text
Geo.Affine.parallelPos_parallel : ∀ A l m,
    Geo.Affine.parPos A l m → Geo.Incidence.Parallel (Geo.Affine.inc A) l m
Geo.Affine.parallelPos_irrefl : ∀ A l, Geo.Affine.parPos A l l → False
Geo.Affine.parallel_trans : ∀ A l m n,
    Geo.Affine.parPos A m l → Geo.Affine.parPos A m n →
    (Geo.Incidence.lEq (Geo.Affine.inc A) l n → False) →
    Geo.Incidence.Parallel (Geo.Affine.inc A) l n
```

`parallel_trans` **is** Playfair's classical corollary "parallelism is
transitive", in the only form this kernel can state it: two lines each
positively parallel to a common line and DISTINCT share no point. The
distinctness hypothesis is the theorem rather than a weakness of the proof —
`l` and `n` may perfectly well be the same line, and deciding which needs `lEq`
to be decidable, which it is not over ℝ. Dropping it would make the statement
false, not merely unprovable.

`parallelPos_irrefl` is the one that consumes an incidence-layer theorem:
it goes through `parallelPos_parallel` into `Geo.Incidence.parallel_irrefl`,
which is where Hilbert I.2 (every line carries a point) enters. It is also the
theorem the second mutation below makes unprovable, which is how "the
distinctness conjunct earns its place" is checked rather than asserted.

### 4. **Finding: the ℝ existence half needs no division, and ℚ's needs two**

ADR-1652 § 2 found that the ℝ model is *cheaper* than the ℚ one because both of
its divisions are by a witnessed sum of squares. The affine layer sharpens that
and inverts the usual expectation once more.

The parallel to `l` through `P` is `(a, b, −(a·x P + b·y P))` — **the same
leading coefficients**, so its non-degeneracy is `l`'s own with nothing to
prove, in both models (`Geo.RLine0.Nondeg` and `Geo.QLine0.Nondeg` both read
only `a` and `b`, and the projections ι-reduce). What remains is the
distinctness witness, and the two models pay differently:

- **ℝ**: `dAC² + dBC² = (a² + b²)·e_P²` (`Geo.RPlane.parLineNorm`, one ring
  identity), so the witness is the PRODUCT of `Nondeg l`'s modulus and
  `off P l`'s. `Geo.RPlane.posBoundMul` assembles it out of
  `CReal.pos_of_pos_bound`, `CReal.mul_pos` and `CReal.pos_bound_of_lt`. **No
  division, no case split, no `CReal.inv`.** The modulus of the product cannot
  be computed from the two factors' moduli without a lower bound, so
  `posBoundMul`'s conclusion is an existential — harmless, because every
  consumer is a `Prop` and `Exists.rec` eliminates into it.
- **ℚ**: `a*C − c*a = −a·e_P` and its `b` mirror, so `Rat.mul_eq_zero` plus
  `off P l` forces `a = 0` and then, separately, `b = 0`, and `Nondeg l`
  refutes the pair. **Two case analyses**, one per coefficient.

The general lesson, and it is the affine-layer form of ADR-1652 § 2's:
**positivity is closed under multiplication constructively, and a decidable
disequality is not.** Where a ℚ development reaches for `mul_eq_zero` twice,
ask whether the ℝ statement is a product of two things the hypotheses already
witness as positive; if it is, the ℝ proof is the shorter one.

Uniqueness is the only place either model divides, and each divides once:
`Geo.RPlane.dirPivot` cancels `a² + b²` through `Geo.RPlane.cancelPosBound`
(the lemma `rplane.rs` factored out for `joinUnique`), and `Geo.QPlane.dirPivot`
splits on `Geo.QLine0.nondeg_or` and cancels through `Rat.mul_eq_zero`. Both
rest on the same six-variable identity, verified by the respective ring
producer:

```text
(a² + b²)·(A*B' − B*A') = (a*A + b*B)·(a*B' − b*A') − (a*A' + b*B')·(a*B − b*A)
```

with the ℚ version taking the `a`- and `b`-halves separately because it has a
pivot to choose:

```text
a·(A*B' − B*A') = A·(a*B' − b*A') − A'·(a*B − b*A)
b·(A*B' − B*A') = B·(a*B' − b*A') − B'·(a*B − b*A)
```

### 5. **Finding: a latent defect in `ring::rat::scale_item`, routed around**

The kernel refused this lane's first `Geo.QPlane.parNondegPair` with a
`TypeMismatch` whose two sides differed only by a double negation:

```text
expected : Eq Rat (Rat.mul (Rat.neg ((a*a)*x)) (Rat.neg Rat.one)) ((a*a)*x)
got      : Eq Rat (Rat.mul (Rat.neg ((a*a)*x)) (Rat.neg Rat.one))
                  (Rat.neg (Rat.neg ((a*a)*x)))
```

`crates/axeyum-lean-kernel/src/ring/rat.rs`'s `scale_item`, in its
`count == -1` branch, returns `vec![item.negated()]` as the resulting monomial
list but builds its proof at `target = rneg(d, it)`. When `it` is a monomial
that is ALREADY negated, `item.negated()` folds to the un-negated term while
`rneg(d, it)` is a double negation, and the two disagree. Every existing caller
scales an un-negated monomial by `−1`, so the branch has never been exercised
on the failing shape.

**It is not fixed here.** `ring::rat` is a shared producer with 800-plus anchor
points across the mutation suites, and a lane that lands geometry should not
also land a change to the ring normaliser without its own controls; the finding
is recorded for whoever takes it. What this change does is route around it, and
the route is worth stating because it is the general one: a correction whose
coefficient is a bare `−1` should be applied as `Rat.neg` of the whole
difference, not as a coefficient `(−1) * …`. Distributing `neg` goes through
`Rat.neg_add`/`Rat.neg_neg`/`Rat.mul_neg` and never reaches `scale_item`.

`geo/qaffine.rs`'s general `vanish` combinator (unconditional ring identity plus
a list of vanishing summands, the ℚ counterpart of `rplane.rs`'s
`sum_hyp_zero`) is safe as long as no coefficient is a literal `0`, `1` or
`−1`; every call site in that file passes a compound coefficient, and the one
that wanted `−1` is written with `Rat.neg` instead, with the reason in a comment
at the call site.

## Consequences

- `Geo.Incidence` now has two models and `Geo.Affine` has two models over them,
  with structurally different equalities (`Eq` on ℚ points, `CPoint.Equiv` on ℝ
  points), different apartness notions, and now different DISTINCTNESS notions
  for parallelism — a negation over ℚ, a `PosBound` witness over ℝ. That one
  record serves both is checked by
  `the_derived_affine_theorems_instantiate_at_both_models`.
- `geo/rplane.rs` and `geo/qplane.rs` are **not edited**. ADR-1652 § 5 predicted
  that the ℝ affine layer "reuses `defectAC`, `defectBC`, `cancelPosBound` and
  `onOfDefects` unchanged", and it does, plus `defectSwap`. The prediction was
  made before the code existed and holds without amendment.
- The two files each re-state ~20 lines of term shorthands (`la`/`lb`/`lc`,
  `lval`/`lsub`/`lprop`, `and_intro`, `exists_intro`, `sum_hyp_zero`, …) that
  are private to `qplane.rs`/`rplane.rs`. A sibling module cannot see a
  sibling's private items and the brief forbade editing those two files beyond
  `pub use`, so the duplication is deliberate. The right home for them is a
  `geo/shared.rs`; recorded so the next lane finds the fact rather than making
  a third copy — the same trade, and the same disclosure, ADR-1652 § 4 made for
  `CPoint.Equiv`'s setoid laws.
- `geo_tests.rs`'s every-declaration sweep is environment-derived, so the 45 new
  names had to be added to the handle list; the vacuity floor moves 110 → 160.
- A new mutation suite `geo-affine` exists beside `geo-incidence` and runs in
  the OPPOSITE profile. `geo-incidence` is deliberately debug because its
  mutants fail at prelude-build time and compiling dominates; that inverted here
  because the prelude-build test itself grew — measured 2026-09-06, ~45 s in
  release against ~435 s in debug, while the per-mutant recompile is ~4 min in
  release against ~30 s in debug. Release is the cheaper total for this suite.
  Two suites over one module disagreeing on profile is not an oversight; each
  has been measured.

## The mutations, run

`python3 scripts/tests/mutation_controls.py geo-affine`, baseline green at
1 test, **two of two killed**:

```text
  Playfair's uniqueness concludes at the two parallels in order        killed 1
  positive parallelism carries a distinctness witness, not only a
      direction                                                        killed 1
```

Both fail at PRELUDE-BUILD time, and that is the finding rather than an
inconvenience: neither predicate can be weakened and left provable.

- **The uniqueness mutant** swaps the conclusion to `lEq n m`. Extensional line
  equality is `∀ P, (on P l → on P m) ∧ (on P m → on P l)`, so the swap is
  `And A B` against `And B A` — symmetric propositionally and **not**
  definitionally — and neither model's `playfairUnique` has the field's type any
  more.
- **The distinctness mutant** drops the second conjunct of
  `Geo.RPlane.parPosRaw`. `Geo.RPlane.parPosDisjoint` then has no witness to
  contradict. The degenerate consequence is computed rather than argued, in
  `dropping_the_distinctness_conjunct_would_make_a_line_parallel_to_itself`: at
  the line `(1, 0, 0)` all three proportionalities against ITSELF reduce to
  `Rat.zero = Rat.zero`, so the direction identity alone is satisfied by a line
  against itself and `Geo.Affine.parallelPos_irrefl` could not hold.

## Alternatives considered

- **Derive `parPos` over an arbitrary `Geo.Incidence`** instead of carrying it
  as a field. Rejected because "same direction" has no meaning in an abstract
  incidence structure: there is no algebra to state the cross product in. The
  only derivable notion is the negative one that ADR-1652 § 5 measured as
  blocking.
- **State Playfair's uniqueness with `off P l` as a hypothesis**, as the
  classical statement does ("through a point not on `l`"). Rejected as
  redundant: if `P` were on `l`, `parPosDisjoint` refutes the hypotheses
  immediately, so the uniqueness half holds vacuously there and both models
  prove the stronger unhypothesised form directly. Existence genuinely needs
  `off`; uniqueness does not.
- **Give `Geo.Affine` a `parPosSymm` field.** `parPos` is symmetric in both
  models (the direction defect negates, the distinctness sum of squares is
  invariant), but proving it is real work in each and nothing in this slice
  consumes it. Left out rather than asserted; a field that no model is forced to
  justify is an axiom.
- **Fix `ring::rat::scale_item` rather than route around it.** Rejected for
  scope, with the defect recorded in § 5 above and at the call site that
  avoids it.

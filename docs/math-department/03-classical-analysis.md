# 03 — Classical analysis

Reviewer: a classical analyst — measure theory, functional analysis, PDE
Verdict, 2026-09-06: **moved, and one complete function space short of interested**
Last measured: 2026-09-06 at `d38d49fce`

> "You have a very careful Riemann integral. I have not used a Riemann
> integral since graduate school." — 2026-09-04
>
> "Now there is an integral, a metric, a frame, and an L¹. None of the L¹ is
> complete. That is my whole subject in one sentence." — 2026-09-06

> **AUDITED 2026-09-04.** Every absence claim in the 2026-09-04 reading was
> re-checked against a freshly rebuilt kernel index. See
> [AUDIT-2026-09-04.md](AUDIT-2026-09-04.md) for the evidence; row **B12** is
> the one that touches this file (Next Five item 1 was already partly decided
> by ADR-0603 and ADR-1010). Across the twelve files, 11 of 76 absence claims
> were false and 12 more overstated the gap; the cause is that the ledger
> characterises only 38% of its proved facts and does not cover 430 kernel
> theorems at all (ADR-1605). **This file was re-measured again on 2026-09-06**
> and six more of its rows were false by then — see the last progress-log row.

> **Retired 2026-09-06 (ADR-1674):** the 430 is not reproducible by its own
> method - three later readings give 599, 620, 721 and 973 on three different
> denominators. The measured, gated figure is **721 of 3,079 registered
> kernel theorem names uncovered**, ratcheted by `gen-ledger-coverage`.

## The persona

Works with Lebesgue integration, Banach and Hilbert spaces, and the
convergence theorems that make them usable. Reaches for dominated convergence
several times a week and for excluded middle without noticing. Regards
constructivity as an interesting philosophical position and a professional
handicap. Their test for a library is whether you can state and use "L² is
complete".

## What the library has today

Measured at `d38d49fce`. The kernel index reports **4,765 declarations** across
sixteen prelude groups; the namespaces this reviewer cares about are
`Metric` 97, `IntSpace` 98, `RN` 58, `Top` 53, `Complex` 196, `CReal` 629. The
ledger holds **2,954 facts, 2,678 proved**.

| what they want | what exists, 2026-09-06 |
|---|---|
| Lebesgue integral | no. `IntSpace` (98 declarations) is a **predicative pre-integration space**: the integral is the primitive and measure is derived (ADR-1612). Three instances — the interval Riemann integral, finite sums, a Dirac space |
| measure, σ-algebra | measure yes, σ-algebra no. `IntSpace.measure` is the integral of an integrable indicator, with `measure_nonneg`, `measure_le_total`, `measure_univ`, `measure_const`, `measure_witness_independent`, `countingMeasure` and `dirac_measure_detachable`. Nothing named `sigmaAlgebra` or `Measurable` is declared — the one `measurable` occurrence in the kernel is a doc comment in `intspace/measure.rs` |
| dominated / monotone convergence | monotone only, and on a hypothesis: `IntSpace.MonotoneSeq`, `MonotoneConvergence`, `RealMonotoneConvergence`, `monotone_convergence_of_real` — an ADR-0603 graded family whose classical member carries a decision principle on one binder. **No dominated convergence for an integral**; the four declarations matching "dominated" are series comparison tests (`CReal.sumRange_converges_of_dominated` and kin) |
| metric space | yes, and it is the load-bearing layer. `Metric`: a 12-field record, ℝ and the plane as instances, `Complete`, `TotallyBounded`, `Compact`/`CompactOn` (Bishop's, no covers), `Continuous`/`UniformlyContinuous` over an arbitrary pair of spaces, `subspace`, and `prod` (the max metric) with completeness transfer |
| topological space, open sets, compactness | a **frame**, not a family of open sets: `Top.Frame`, `Top.Opens`, `Top.MemOpen`, 53 declarations, with `Top.ballFrame` — the open-ball frame of the real line — as the instance (ADR-1602, ADR-1643). Compactness lives on the metric side; nothing on the frame side is compact |
| normed space, Banach, Hilbert | nothing abstract: no declaration in the kernel matches `banach` or `hilbert`. Concretely `RN` (58 declarations) is ℝⁿ with `dot`, `norm`, **unsquared `cauchy_schwarz` at symbolic dimension**, Minkowski (`norm_add_le`), and hence `RN.metric n`. **ℝⁿ is not proved complete** |
| Lᵖ spaces | L¹, as a metric space only: `IntSpace.bundledL1` on bundled integrable functions with the seminorm `∫ \|f−g\|`, `L1Equiv` as constructive "equal almost everywhere", and two instances (`crealIntervalL1`, `crealFiniteL1`). **Not complete, and there is no completion functor** — no declaration matches `completion` |
| Fourier analysis | nothing. `Complex.IsRootOfUnity` exists; no transform and no orthogonality relation is on `main` |
| distributions, Sobolev, PDE | nothing |
| complex analysis | a **uniform** derivative on a closed disc, and holomorphy over it: 46 declarations across `complex/{deriv,estimates,leibniz,uc_closure,polyderiv,components,cauchy_riemann}.rs` — const/id/neg/add/**mul**/**pow** rules, `HolomorphicOn` as a `Sigma`, `BoundedOn` and `UniformlyContinuousOn` closed under `+` and `·`, the three modulus-versus-component inequalities, and the disc-membership bridge. **No Cauchy–Riemann equations, no polynomial derivative, no contour integral, no Cauchy theorem** — nothing matches `cauchyRiemann` or `hasDerivative_poly` |
| what does exist | IVT; EVT, now **as an instance of the metric-space theorem** rather than a one-off; uniform continuity on intervals; derivatives; Riemann integration on an interval-relative mesh; exp/cos/π/√; and power series with a radius of convergence (`CReal.powerSeriesConvergesWithinRadius`, ADR-1638), with exp and cos exhibited as instances |

## Their verdict

The 2026-09-04 reading said the analysis shelf stops in 1867. That is no longer
the sentence. In two days the library acquired a metric layer, Bishop
compactness, ℝⁿ with Cauchy–Schwarz at symbolic dimension, a pointfree
topological carrier, an integration space with a derived measure, L¹ as a
metric space, a radius of convergence, and a complex derivative with a product
and a power rule. Four of this reviewer's five Next Five items moved.

What has not changed is the thing they actually test for. **Nothing in the
library is a complete function space.** `Metric.Complete` exists as a general
predicate, and the whole kernel contains exactly two proofs of it —
`Metric.creal_complete` (ℝ) and `Metric.prod_complete` (transfer across a
product). It is not proved for ℝⁿ, for L¹[a,b], or for anything else.
`IntSpace.bundledL1` is a metric space whose points are functions, which is
genuinely the first object here they would recognise as theirs — and the
completeness statement about it is unproved, not merely unstated. There is no
L², because there is no inner product on a function space; `RN.dot` is
finite-dimensional by construction.

Their two 2026-09-04 objections still stand, one of them now with a decision
attached:

**Constructive analysis makes the wrong theorems true.** The classical
statements they use are often constructively false, not merely unproved: a
continuous function on a closed interval need not attain its maximum, and the
library's EVT is a different theorem than the one they teach. This is now
*recorded* rather than argued about: `CC:creal-real` in the carrier-
correspondence ledger grades `CReal`↔Mathlib's `Real` `constructively-stronger`
on IVT with footprints `[]` against `[propext, Classical.choice, Quot.sound]`,
and carries EVT as a deliberately non-dominant second witness (ADR-1665). A
Mathlib-parity claim in analysis is still not meaningful without saying which
statement is meant — but there is now a table that says it.

**Measure theory is where the subject actually lives, and it needs classical
logic.** The project answered this and the answer went against them: ADR-1601
decides that classical principles enter as **hypotheses, never axioms**. The
measurement behind it was that carrying a decision principle costs 11 binders
and 14 argument positions across ten theorems and zero proof obligations, and
does not grow with depth; the axiom route would have cost at least three axioms
(EM, countable choice, `funext`) and killed three passing gates. What arrived
under that policy is exactly what the policy predicts: monotone convergence as
a graded family with the classical member on one explicit binder. This
reviewer's response is that a decision principle on a binder is a fine
*bookkeeping* answer, and it does not make `∫ lim = lim ∫` a lemma they can
apply without thinking, which is the property they were asking for.

Their one point of genuine interest is unchanged and is now paying: the
library's habit of recording
[graded statement families](../research/09-decisions/adr-0603-classical-theorems-land-as-graded-statement-families.md)
lets the classical statement be present and labelled rather than absent or
silently substituted. Monotone convergence is the first analysis theorem to
land in that shape.

## What they would say is missing

Reordered by what would change their assessment first, now that the carriers
exist.

- **A completion.** Any one complete function space, by any route. This is the
  single item standing between the library and their test. Sized once already:
  of the 33 declarations in `creal/completeness.rs` and `creal/convergence.rs`,
  the l1-completion lane measured **1 as reusable** (`CReal.limit`), because
  every other one is stated about `CReal` alone and `CReal` is not the
  completion functor applied to ℚ (ADR-1625). *That 33 is the lane's count and
  is not re-derivable by the same method today — `convergence.rs` declares
  through `creal.rs`'s shared step table, not through a local name struct — but
  its consequence is re-measured and holds: only ℝ and a product are complete.*
- **Dominated convergence**, in whatever regime ADR-1601 forces. Monotone
  convergence landed; the dominated theorem is the one they reach for, and it
  is not stated.
- **A σ-algebra, or an argued replacement.** ADR-1612 derives measure from the
  integral and never builds a measurable-set structure. That is a defensible
  construction order; it is not one this reviewer can map onto their own
  training without a written correspondence.
- **Complex analysis above the derivative.** Cauchy–Riemann, contour
  integration, Cauchy's theorem, residues. The derivative shelf is real; the
  theorems that make complex analysis *useful* start one level up. This is also
  the gate on analytic number theory
  ([01-number-theory.md](01-number-theory.md)).
- **Multivariate calculus.** `RN` gives the carrier, the inner product and the
  norm; there are no partial derivatives, no differentials, and no Fubini for
  integrals (the eight `fubini` hits in the kernel source are all the
  *discrete* sum-swap lemma over ℕ and ℚ).

## The blocker

**No longer a decision — a construction, and the library knows which one.**

The 2026-09-04 reading said the blocker was a policy question about excluded
middle. That question is closed (ADR-1601: hypotheses, not axioms), and the
route it left open works: a classical member of a graded family carries its
decision principle on a binder, the axiom footprint stays empty, and the ledger
still reports which statement is which.

What blocks this reviewer now is measured and narrow: **every completeness
proof in the library is about `CReal`.** `Metric.Complete` is a general
predicate — the metric layer generalized the *statement* — but the only
witnesses in 4,765 declarations are `Metric.creal_complete` and the transfer
`Metric.prod_complete`. There is no generic `Metric.completion`, and the
l1-completion lane's number for why is 1 of 33. So L¹ is a metric space nobody
can complete, ℝⁿ is a metric space nobody has completed, and the reviewer's
test sentence — "L² is complete" — fails at two independent points: no L², and
no completion.

The second-order finding, which the department should carry: **the general
theorems are cheap and the instances are the work.** The metric lane measured
34 declarations for every carrier against 10 more for one interval; the L¹ lane
measured all six of its analytic obligations discharged by existing lemmas and
zero new estimates. Sizing future analysis work should weight instantiation at
least as heavily as the theorem.

## Next five, in their priority order

The 2026-09-04 list, with today's state and a measured reason for each.

- [x] **1. Decide and document the classical-axiom policy.** Landed
      `80aa8e52c` (ADR-1601): classical principles stay **hypotheses**, never
      axioms. The lane says plainly this is not the answer the reviewer asked
      for.
- [x] **2. A topological-space carrier**, ℝ as the first instance. Landed
      `e0f0be745` (ADR-1643): `Top.Frame` as a 16-field frame record with
      `Nat`-indexed joins, `Top.ballFrame` the open-ball frame of ℝ, **53
      declarations in the `Top` namespace**. Pointfree, per ADR-1602 — not the
      open-set carrier this item asked for.
- [~] **3. Metric and normed spaces, with completeness.** Metric landed
      (`b7df58b7b`, `5bb30b809`, `84320ce9e`): **97 indexed `Metric`
      declarations plus 12 in `metric_prod.rs` that the index does not see.**
      ℝⁿ landed (`d00d2a33c`, ADR-1606): **58 `RN` declarations** with norm,
      unsquared Cauchy–Schwarz and Minkowski. **Open:** no abstract normed- or
      inner-product-space record, and `Metric.Complete` has exactly two
      witnesses — ℝ and the product transfer — so ℝⁿ is not complete.
- [~] **4. Measure and the Lebesgue integral on ℝ.** Opened `3d5320f68`
      (ADR-1612) and extended `a46e882b9` (ADR-1625): **98 `IntSpace`
      declarations**, measure derived from the integral, monotone convergence
      as a graded family, L¹ as a metric space with two instances. **Open:** no
      σ-algebra, no Lebesgue integral as a primitive, no dominated convergence,
      L¹ not complete.
- [~] **5. Complex analysis: holomorphy and Cauchy's integral theorem.** Four
      slices landed (`8900ed072`, `dbe5a5169`, `feb36ea21`, and the
      `holomorphic_pow` follow-on `2758e7b18`): **46 declarations across seven
      modules** — uniform derivative on a disc, holomorphy, Leibniz, the
      estimate shelf, uniform continuity closed under `+` and `·`, the power
      rule, the modulus-versus-component inequalities and the disc-membership
      bridge. **Open:** the Cauchy–Riemann equations themselves (blocked on
      component extraction — the real part has no homomorphism law for
      products), the polynomial derivative (needs a recursion building
      magnitude bounds along the coefficient list), contour integration, and
      Cauchy's theorem.

**What they would put first now**, given items 1 and 2 are closed:
(a) `Metric.completion`, or completeness of any one function space;
(b) dominated convergence in ADR-1601's regime;
(c) the Cauchy–Riemann equations, the last brick before the contour integral.
Each is named as an obstruction in a landed lane's own record, so none of the
three needs a fresh design decision first.

## Progress log

| date | change | evidence |
|---|---|---|
| 2026-09-04 | File created. Baseline: no measure, no topology, no normed spaces, no complex analysis. Riemann integration and the interval theorems only. | ledger snapshot at `1856cdb3c` |
| 2026-09-04 | **Next Five item 1 landed, and the answer is not the one this reviewer wanted** (roadmap W0-2, ADR-1601): classical principles stay **hypotheses**, never axioms. The measurement: carrying one costs 11 binders and 14 argument positions across ten theorems, and **zero obligations**, and does not grow with depth. Three findings decided it — the axiom option is at least three axioms (EM, countable choice and `funext`, which this file's blocker named together and nobody had priced), it devalues the certificates whose content is that a classical conclusion costs a decision principle, and it kills three passing gates. Items 2–5 are unaffected in substance; measure theory unblocks with a *stated shape* rather than with classical logic available by default. | `80aa8e52c` |
| 2026-09-04 | **Next Five item 4 opened, and not in the shape this reviewer asked for** (roadmap W3-1, ADR-1612). Measure theory arrives integral-first: a predicative pre-integration space with the interval integral, finite sums and a Dirac space as instances, measure *derived* as the integral of an integrable indicator, and monotone convergence as a graded family whose classical member carries a decision principle on one binder. No σ-algebra, no Lebesgue integral as a primitive, and dominated convergence not yet stated. The lane says plainly that this reviewer may reasonably say an integration space is not their subject. The honest count: 70 declarations, 1 of 6 interval theorems re-derived generically — the rest *are* the space's axioms — and L¹ as a completion blocked on `Sigma`'s absence. | `3d5320f68` |
| 2026-09-05 | **L¹ is a metric space** (roadmap W3-1 follow-on, ADR-1625): `IntSpace.bundledL1` on bundled integrable functions with the seminorm `∫|f − g|`, and "equal almost everywhere" as the constructive equivalence `∫|f−g| ~ 0`. Interval and finite instances at zero new estimates. **L¹ is not yet complete**: the reuse number against the real line's completion machinery is 1 of 33, because every completeness lemma is stated about `CReal` alone and `CReal` is not the completion functor applied to ℚ. A generic `Metric.completion` is sized at four `CReal.limit` lemmas and is the next lane. This reviewer's function-space complaint is now one construction away rather than one shelf away. | `a46e882b9`; `intspace::` + `metric::` 56 passed |
| 2026-09-05 | **This reviewer's "may be a different theorem" is now a table** (ADR-1665, `docs/math-department/14-lean-lang.md` Next Ten item 4): `CC:creal-real` grades `CReal`↔`Real` `constructively-stronger` on IVT (`CReal.ivt_approx` vs `intermediate_value_Icc`, footprint 0 vs `[propext, Classical.choice, Quot.sound]`) and carries EVT as a second, deliberately non-dominant witness citing ADR-1030's `different-object` concession verbatim rather than re-litigating it. `CC:complex-complex` grades `Complex`↔`Complex` `constructively-stronger` on `Complex.no_compatible_order` (a constructive impossibility proof here against a silent instance omission there). `CC:intspace-lebesgue-integral` grades `IntSpace`↔the Bochner integral `different-object`: the construction order is reversed (integral-first here, measure-first there per ADR-1612), and flags one open item for a future lane — a general (non-interval) `integral_nonneg` in the pinned Bochner files could not be located and needs a fresh grep before any row cites one by name. | `artifacts/carrier-correspondence/carrier-correspondence-v1.json`; `python3 scripts/check-carrier-correspondence.py --check` |
| 2026-09-05 | **The composition question this file's blocker raises is decided** ([ADR-1664](../research/09-decisions/adr-1664-an-originated-theorem-may-rest-on-an-import-on-a-route-of-its-own.md), `14-lean-lang.md` Next Ten item 8). The blocker said "no decision says whether an originated theorem may *depend* on an imported one, so imports cannot compose with anything we prove." There is one now: it may, on a distinct `kernel-lean-over-import` route that carries the imported proof's axioms **plus** the import route's three assumptions, and never counts toward the axiom-free headline. Measured rather than argued: propagation through `Kernel::axiom_footprint` is transitive **and per proof term**, so two originated theorems of the same type in one kernel measure the import's whole six-name closure and `[]` respectively — loading an import does not contaminate what is proved beside it. Composition costs 0.19 ms at the trusted gate against 0.09 ms without. **This unblocks the route, not the mathematics.** Measure theory may now be built on a Mathlib import and land as a fact, but the ADR also measures that our preludes and an import cannot yet share one environment (17 shared `Init` names; `build_nat_prelude` into an imported kernel is rejected at `False`), so a composed theorem must live wholly in the imported vocabulary until item 4's carrier-correspondence bridge lands. **This file's verdict line is unchanged**: nothing measure-theoretic was proved here. | `08b97603b`; `cargo test -p axeyum-lean-import --test imported_composition_footprint` 3 passed, 1 ignored |
| 2026-09-05 | **Item 5, first slice** (roadmap W3-5, ADR-1642): `Complex.HasDerivativeOn` in Bishop's uniform form on a closed disc, mirroring the real shelf (which has no pointwise derivative), with const/id/neg/add rules, and `Complex.HolomorphicOn` as a `Sigma` over the derivative; 18 axiom-free declarations. The ring half of each transcription collapses to one producer call; the analysis half is verbatim from the real shelf. **Leibniz is blocked on estimates, not algebra**: `Complex.BoundedOn` and `UniformlyContinuousOn` do not exist. That is the next brick before any of Cauchy–Riemann, complex power series, or the integral theorem. | `8900ed072`; `complex::` 73 passed in the lane |
| 2026-09-05 | **Item 5, second slice** (roadmap W3-5, ADR-1646): the bounded and uniformly-continuous predicates on ℂ, the product rule with the real shelf's hypotheses, and the modulus-versus-component inequalities Cauchy–Riemann needs; 17 axiom-free declarations. Two hypothesis placements in the earlier ADR's prose were wrong and are corrected. Next: closure of uniform continuity under products (for polynomial derivatives), then the CR bridge. | `dbe5a5169`; `complex::` 86 passed in the lane |
| 2026-09-06 | **Item 5, third slice** (roadmap W3-5, ADR-1656): uniform continuity closed under sums and products, the power rule with its holomorphic instance, and the bridge from disc membership to segment endpoints that Cauchy–Riemann needs, which cost two rewriting steps and no estimate; 10 axiom-free declarations. Polynomial derivatives wait on a recursion building the magnitude bounds along the coefficient list; the CR equations wait on component extraction, since the real part has no homomorphism law for products. | `feb36ea21`; `complex::` 92 passed in the lane |
| 2026-09-06 | **Re-measured end to end; the verdict moves from "unmoved" to "moved, and one complete function space short of interested".** Four of the five Next Five items have landed or partly landed since 2026-09-04, and six rows of this file's 2026-09-04 table were false by today. Measured at `d38d49fce`: the kernel index reports **4,765 declarations**, with `Metric` 97 (+12 in `metric_prod.rs`, which `shape_search` does **not** index — a blind spot confirmed today by `Metric.prod` returning 0 matches in a dump of all 4,765 names, and re-read from source), `IntSpace` 98, `RN` 58, `Top` 53, `Complex` 196, `CReal` 629. The ledger holds **2,954 facts, 2,678 proved, 1,576 landmark (58.85%)**; all 14 `Metric`/`RN`/`Top` facts, all 6 `IntSpace` facts and all 32 complex-derivative/estimate facts read `proved`. Corrections: "metric space — nothing" was false (a whole layer, with Bishop compactness and EVT as an instance); "topological space — nothing" was false (`Top.Frame`, pointfree); "measure — nothing, the 117 grep hits are the word *measured*" was false (`IntSpace.measure` and five theorems about it); "Lᵖ — nothing" was false (L¹ as a metric space); "no holomorphy" was false (46 declarations across seven modules, up to a power rule); and the file's own re-measure recipe now returns misleading NONZERO counts for `hilbert` (prose about Hilbert's incidence axioms in `geo.rs`), `fubini` (the discrete sum-swap over ℕ/ℚ) and `measure` (191 files, mostly the word "measured") — so the recipe is replaced below with one that counts declarations. What did **not** move, verified against the full name dump with `Metric`/`IntSpace` (193 names) as the positive control in the same invocation: zero declarations match `banach`, `hilbert`, `lebesgue`, `sigmaAlgebra`, `Measurable`, `completion`, `contour`, `fourier`, `cauchyRiemann` or `hasDerivative_poly`, and `Metric.Complete` has exactly two witnesses (`Metric.creal_complete`, `Metric.prod_complete`). No worktree ahead of `main` carries analysis work: the 24 branches touching `complex`/`creal`/`creal_point` are all stale checkpoints from 2026-08-23…28. | `d38d49fce`; `shape_search --include-constructed --list-namespaces` (build 231.6 s, `declarations=4765`); `shape_search --include-constructed --limit 6000 --kind theorem --kind definition --kind axiom --kind inductive --kind constructor --kind recursor` → 4,765 names; `python3 scripts/count-landmark-facts.py` → `total=2954 proved=2678 landmark=1576` |

## How to re-measure

The old recipe grepped the kernel *source* for eleven words and read a zero as
absence. It no longer discriminates: `measure` returns 191 files (mostly the
word "measured"), `hilbert` returns 1 (prose about Hilbert's incidence axioms
in `geo.rs`), `fubini` returns 8 (the *discrete* sum-swap lemma). Count
declarations, not files.

```sh
# 1. The namespace census. ~2-4 min: it builds every constructed prelude.
#    Metric / IntSpace / RN / Top / Complex are this reviewer's shelves.
cargo run --release -p axeyum-lean-kernel --example shape_search -- \
  --include-constructed --list-namespaces

# 2. Every declaration name, once, so an absence has a same-invocation
#    positive control. Grepping this file is the ONLY honest absence test
#    here: a word in a doc comment is not a declaration.
cargo run --release -p axeyum-lean-kernel --example shape_search -- \
  --include-constructed --limit 6000 --kind theorem --kind definition \
  --kind axiom --kind inductive --kind constructor --kind recursor \
  | awk '$1=="MATCH"{print $2}' > /tmp/axeyum-names.txt
grep -icE 'banach|hilbert|lebesgue|sigmaAlgebra|Measurable|completion|contour|fourier' /tmp/axeyum-names.txt
grep -cE '^(Metric|IntSpace)\.' /tmp/axeyum-names.txt   # positive control, must be non-zero

# 3. metric_prod.rs is NOT in that index (measured 2026-09-06: `Metric.prod`
#    returns 0 matches in the dump above). Read it from source; the names
#    struct has one field per declaration.
grep -cE '^\s+pub [a-z_0-9]+: NameId,' crates/axeyum-lean-kernel/src/metric_prod.rs

# 4. The complex-analysis shelf, module by module, the same way.
for m in deriv estimates leibniz uc_closure polyderiv components cauchy_riemann; do
  printf '%-16s %s\n' "$m" \
    "$(grep -cE '^\s+pub [a-z_0-9]+: NameId,' crates/axeyum-lean-kernel/src/complex/$m.rs)"
done

# 5. The ledger.
python3 scripts/count-landmark-facts.py
ls artifacts/facts/ | grep -cE '^F-(metric|rn|top|intspace)-'
```

## Related

- [02-constructive-analysis.md](02-constructive-analysis.md) — the same shelf,
  judged favourably
- [06-topology.md](06-topology.md) — the prerequisite, now partly built
- [08-probability-and-statistics.md](08-probability-and-statistics.md) —
  blocked behind measure theory
- [ADR-0603](../research/09-decisions/adr-0603-classical-theorems-land-as-graded-statement-families.md)
  — classical theorems land as graded statement families
- [ADR-1601](../research/09-decisions/adr-1601-classical-logic-enters-as-a-hypothesis-not-as-an-axiom.md)
  — classical logic enters as a hypothesis, not as an axiom
- [ADR-1612](../research/09-decisions/adr-1612-the-integral-is-primitive-and-measure-is-derived-predicatively.md)
  — the integral is primitive and measure is derived predicatively
- [ADR-1625](../research/09-decisions/adr-1625-l1-is-a-metric-space-from-a-pointwise-distance-and-the-completion-functor-does-not-exist-yet.md)
  — L¹ is a metric space; the completion functor does not exist yet
- [ADR-1643](../research/09-decisions/adr-1643-the-frame-carrier-is-nat-indexed-and-the-ball-index-is-not-a-nat.md)
  — the frame carrier is `Nat`-indexed

# 00 — The roadmap

A top-down synthesis of the twelve reviewers' Next Five lists into one ordered
programme, with a live status board and a history log.

Created 2026-09-04 at `f36120646`. Status board last reconciled 2026-09-04.

> This is the department's *view* of what to build and in what order. It is not
> the work queue. A roadmap item becomes work when a lane brief cites it and
> [PLAN.md](../../PLAN.md) carries the task; the status column here is updated
> from what landed, never used to schedule.

## How this was derived

Each of the twelve persona files ends with five items in that reviewer's own
priority order — sixty items. Collapsing the ones that are the same request
made by different fields leaves **51 distinct items** and, more usefully,
**seven convergence points** where two or three independent reviewers asked for
the same thing without coordinating. Those convergences drive the ordering,
because an item three fields need is worth more than an item one field ranks
first.

The other input is the dependency structure: several items cannot start until a
decision is written, and a small number of carriers unlock whole shelves.

## The seven convergences

Ranked by how many reviewers independently asked, then by what they unblock.

| # | item | asked by | why it converges |
|---|---|---|---|
| C1 | **Quotient and extensionality decision** | 04.1, 09.3, 12.1 | `Quot.sound` and `funext` gate abstract algebra, categories, algebraic geometry, and function spaces. One ADR, four fields. |
| C2 | **Close a `computed` result into a kernel statement** (Rado) | 07.1, 11.1, 12.4 | The project's own thesis, one step short of demonstrated on its most research-level result. |
| C3 | **A metric-space carrier**, ℝ and `CPoint` as instances | 02.4, 03.3, 06.2 | Turns per-carrier analysis theorems into instances. The cheapest proof that a topology design pays. |
| C4 | **Classical-axiom policy decision** | 03.1, 12.2 | Also gates 08's limit theorems and 10.3's completeness. EM as a labelled footprint entry, or as a discharged hypothesis. |
| C5 | **Measure and the Lebesgue integral** | 03.4, 08.5 | The single largest shelf, and the gate on measure-theoretic probability. |
| C6 | **Write down the kernel's metatheoretic status** | 10.5, 12.5 | No code. Nobody outside can assess the headline metric without it. |
| C7 | **ℝⁿ as a carrier** | 05.2, implied by 02 and 03 | Multivariate calculus, differential geometry, and function spaces all start here. |

## The dependency picture

```
        C1 quotient/extensionality ADR ─┬─> abstract algebra (04.2–04.5)
                                        ├─> categories (09.4–09.5)
                                        ├─> algebraic geometry (05, deferred)
                                        └─> algebraic topology (06, deferred)

        C4 classical-axiom ADR ─────────┬─> measure theory C5 ──> probability (08.3–08.5)
                                        ├─> FO completeness (10.3)
                                        └─> classical analysis (03.4–03.5)

        topology design ADR (06.1) ─────┴─> topology carrier (W2-21) ──> C5

        C3 metric spaces ──> Bishop compactness (06.3) ──> EVT as an instance
        C7 ℝⁿ ──> multivariate calculus ──> differential geometry (05)

        (no gate)  C2 Rado · C6 metatheory writeup · FTC (02.1) · graphs (07.2)
                   primitive roots (01.1) · universal properties (09.1)
                   producers to ℝ (11.2) · landmark count (12.3)
```

## Wave 0 — the four decisions

Days of writing, not quarters of implementation, and six of twelve fields wait
on them. The chair's finding is that these have been deferred because the
current metric does not punish deferring them.

| id | item | source | status | note |
|---|---|---|---|---|
| W0-1 | Quotient and extensionality ADR (C1) | 04.1, 09.3, 12.1 | **landed** `2a640c9b6` | **Decided by measurement: setoid quotients; `Quot.sound` stays out.** [ADR-1595](../research/09-decisions/adr-1595-quotients-stay-setoids-and-quot-sound-stays-out.md), Proposed. Net cost of not having the axiom, measured on W2-8: **three lines**. Two findings that decided it: the footprint filter counts the whole quotient package, so it is five entries not one; and it would not reach the classical statement anyway, because `Subtype` and `Sigma` are absent. Reversible on evidence — a named theorem shown unreachable over setoids reopens it. |
| W0-2 | Classical-axiom policy ADR (C4) | 03.1, 12.2 | **landed** `80aa8e52c` | **Decided by measurement: classical principles stay hypotheses, never axioms.** [ADR-1601](../research/09-decisions/adr-1601-classical-logic-enters-as-a-hypothesis-not-as-an-axiom.md), Proposed. Cost of the hypothesis route across ten theorems: **11 binders, 14 argument positions, zero obligations**, and it does not grow with depth. Three findings beyond the cost: the axiom option is at least *three* axioms (EM, countable choice, `funext`), never priced by the reviewer who asked; it retroactively devalues the certificates whose content is that a classical conclusion *costs* a decision principle; and it kills three environment-scan gates that pass today. **Honest caveat from the lane: this does not give reviewer 03 what they asked for.** |
| W0-3 | Constructive topology design ADR | 06.1 | **landed** `b7df58b7b` | **Decided by building the metric carrier: metric layer first, pointfree (frames/locales) for topology proper when needed, open-set topological spaces never.** [ADR-1602](../research/09-decisions/adr-1602-the-metric-layer-first-then-pointfree-and-not-open-sets.md), Proposed. Apartness is not a third option — a metric supplies it, and `CReal` already has `Apart` with its laws. What the build taught: **nothing in the record is a subset**, so the reviewer's objection to membership predicates never arose. |
| W0-5 | **Dependent pairs**: `Sigma`, `Subtype`, `Fin` — added 2026-09-04 | ADR-1595 §, ADR-1602 §, ADR-1612 § | **in progress** | Absent from the kernel, and the absence blocked three shelves in one day. An ordinary inductive, not an axiom. Decided by re-testing the three blocked sites and counting how many unblock. |
| W0-4 | Kernel metatheoretic status (C6) | 10.5, 12.5 | **landed** `8b4f277d4` | [ADR-1600](../research/09-decisions/adr-1600-the-kernels-metatheoretic-status-what-is-trusted-and-what-is-not.md). Trusted base measured at **5,526 function-body lines across 9 files**, by call-graph closure from the four admission gates, out of 378,049 in the crate. Three soundness guards demonstrated firing in an isolated copy; **a fourth kills zero tests** and is recorded as an open finding rather than hidden. |

**W0-1 and W0-3 should be written together.** The morphism-equality question
(09.3) and the topology-carrier question are the same fork seen from two sides:
if the answer is setoids, both are built over setoids, and the `AlgS` spine is
the precedent for both.

## Wave 1 — unblocked, no decision required

Everything here can start today. Ordered by convergence count, then by yield.

| id | item | source | status | note |
|---|---|---|---|---|
| W1-1 | Rado numbers in-kernel; close the computed→proved gap (C2) | 07.1, 11.1, 12.4 | **landed** `de0cd02da` | 17 declarations in `nat_prelude/rado.rs`, footprint 0, and **Schur's number `R_2(x = y + z) = 5` proved in-kernel from search in BOTH halves** — the upper by a case tree, the lower by reflection over a `Nat.Finset` colouring. `Nat.Finset` *is* a 2-colouring with no side condition. **The brief's unary-numeral constraint was wrong**: `IsRadoNumber 5 3 4 625` type-checks, because a `Prop` mentioning a numeral never reduces it; the cost is a cost of *reduction*. The real residue is combinatorial — `Arrows 5 3 4 625` needs a term over 4⁶²⁵ colourings, and colourings are functions. Both `computed` facts correctly stay `computed`. ADR-1596. |
| W1-2 | Fundamental theorem of calculus | 02.1 | **landed** `182d0dd7d` | **The item was based on a false absence: both directions were proved 2026-08-27**, before the review that asked for them. What landed is the `_of_uc` pair with the redundant boundedness witness removed (arity 7→5 and 9→7), and the finding that **W2-20 is not a prerequisite** — FTC-II routes through `constant_of_zero_deriv` and the modulus's uniformity replaces the MVT's asserted point. Root cause of the false absence: ADR-1605. |
| W1-3 | Name the universal properties already proved | 09.1 | **landed** `c64893719` | `Nat.Peano.initial` (ℕ initial in pointed unary algebras, **no hypothesis on the target**) and `Int.Characterization.initial` (ℤ initial among ℤ-structures, hypotheses only the two mutual-inverse laws), both from already-checked theorems with no new induction. Two mutation defects added, both refused by the kernel. [ADR-1610](../research/09-decisions/adr-1610-name-the-universal-properties.md). |
| W1-4 | Landmark count beside the total | 12.3 | **landed** `8b4f277d4` | `scripts/count-landmark-facts.py`, registered in `check.sh` and the justfile with its own control suite. **2,487 proved, 1,432 landmark (57.6%).** Rule: proved, and the title is not `[generated]`. |
| W1-5 | Extend `ring` and `decide` to ℝ | 11.2 | **landed** `a3f4f528c` | `ring::generic` extended (not forked) with the same `Backend` shape `linarith` used; **six goal shapes proved at `CReal.commRingS`** that were unreachable before, plus a corrupted-certificate battery where the *kernel* refuses with the producer's own check disabled. **`decide` cannot reach ℝ**, and the reason is measured: `CReal.Equiv`/`le`/`lt` are quantifier-headed, and no apartness-witness definition exists to give it a decidable fragment. **Zero retirements**: wiring it into `creal/ring_helpers.rs` produced a real `Decline::NotAnIdentity` in the prelude build and the lane reverted rather than ship it — the "a producer cannot retire its own primitives" trap, confirmed at cost (ADR-1599). |
| W1-6 | A graph carrier | 07.2 | **landed** `0a499a6d8` | `Nat.Graph`, 39 declarations, footprint 0: decidable adjacency with **symmetry and irreflexivity forced inside `adjB` by conjunction**, so a malformed table yields fewer edges, never more; `neighbors` as a `Nat.Finset`, `degree`, `degree_le_order`. Walks and connectivity did not land (a scoping call, plan in [ADR-1608](../research/09-decisions/adr-1608-the-graph-carrier-forces-symmetry-and-irreflexivity.md)). |
| W1-7 | Structure of (ℤ/n)\* and primitive roots | 01.1 | **landed** `a9ef9465d` | 11 declarations in `int_prelude/mult_order.rs`, footprint 0: multiplicative order, order divides the totient, `pow ≡ 1 ↔ order ∣ k`, primitive roots, power injectivity (ADR-1598). **Existence mod a prime did not land**, and the obstruction is named: `∑_{d∣n} φ(d) = n` needs a divisor-set aggregate and the `d ↦ n/d` reindexing of a predicate-restricted sum, which does not exist. |
| W1-8 | Angle measure; laws of sines and cosines | 05.1 | **landed** `c7ddfeca1` | 32 declarations in the `cpoint` group, footprint 0, **cosine-first with no `arccos`**: `norm`, `crossV` with `cross_eq_crossV` by `Equiv.refl` (the triangle determinant *is* the vector cross product, so every Ceva/Menelaus/area fact transports free), the Lagrange identity, the hypothesis-free law of cosines in `dot` form, `cosAngle`/`sinAngle` under a `PosBound` witness, `sin² + cos² = 1` **with no trigonometric name in its dependency closure**, and both laws. **The brief's premise was false**: `CReal.sin_sq_add_cos_sq` does not exist under any spelling. Five stale doc comments in `creal_point.rs` still say `sqrt` does not exist. First follow-on: a producer for the `PosBound (‖U‖‖V‖) k` witness, two lemmas. [ADR-1615](../research/09-decisions/adr-1615-the-angle-is-a-cosine-not-a-number.md). |
| W1-9 | Extend the reverse-mathematics map | 10.1 | **landed** `80aa8e52c` | Six implications over ℕ with empty footprints — `em_implies_lpo`, `lpo_implies_wlpo`, `lpo_implies_markov`, `lpo_implies_llpo`, `wlpo_and_markov_imply_lpo` (the converse half), and `lnp_unrestricted_implies_lpo` joining the existing calibration point. Plus four order theorems over ℝ on an explicit decision hypothesis, whose conclusions the real prelude's own field docs record as unavailable. Every separation is **cited, not claimed** — a separation needs a model of the kernel, not a term in it. |
| W1-10 | Generalize finite probability over `AlgS.OrderedRing` | 08.2 | **landed** `86c7a1065` | `rat_prelude/probability_s.rs`, 29 declarations, footprint 0: `IsDistribution`, `expectation`, `variance`, `covariance`, linearity, Markov, `variance_nonneg`, `expectation_map`, all once over `(R : AlgS.OrderedRing)`. **Instance count, measured by the kernel: 9 of 11 attempted ℚ theorems are instances outright, 2 more with a stated adjustment** (`Rat.markov_inequality` after dropping two hypotheses its own proof never used, so the generic statement is *stronger*); the five definitions are definitionally the ℚ constants. ~19 ℚ theorems untried and not claimed. **Expectation's linearity is a consequence, not an axiom** — ADR-1612's warning was checked and does not bite here. Cost that did bite: three generic ring lemmas and two forgetful projections ADR-1592 never declared. [ADR-1616](../research/09-decisions/adr-1616-finite-probability-over-algs-orderedring-independence-and-the-integral-bridge.md). |
| W1-11 | Homomorphisms, kernels, images, subgroups | 04.3 | **landed** `2a640c9b6`, residue `ecbf403f0` | Homomorphisms, kernels and images with W2-8; **subgroups as a meet-semilattice** with the algebra lane: `IsSub` (four conjuncts, one of them the equivalence-respecting one, which is load-bearing because `bot` is the identity's *class*), `le`, `inter`, `top`, `bot`, `ker_isSub`, and the lattice laws. Join is absent — it needs a word-closure inductive, which is also what would make a *normal* subgroup statable. |
| W1-12 | Measure the exact-real performance envelope | 11.4 | **landed** `0ba67b82e` — and the number is bad | `examples/creal_eval_cost.rs`. Trivial constants normalize in under 5 ms at any index, so the caller's encoding is not the cost. **`e` at index 0 — the loosest possible request — did not fully normalize in 400 s; π not in 480 s.** The series' own internal `Nat.rec` recursion is unary regardless of the caller's numeral, so the kernel's literal fast path never fires inside it. The library's own bound theorems never force this reduction, which is why nobody had measured it. `artifacts/measurements/creal-eval-cost-2026-09-04.md`; [ADR-1617](../research/09-decisions/adr-1617-exact-real-cost-and-cas-internal-residue-measured.md). Reviewer 11's reservation is confirmed, not answered. |
| W1-13 | Measure and reduce the `cas-internal` residue | 11.5 | **landed** `0ba67b82e` | **60 `cas-certificate` facts: 14 reconstruct, 46 are `cas-internal` (76.7%), 0 unrecognized.** Concentrated in number theory, hypergeometric identities, GF(2) and SOS — the families with no kernel bridge. `scripts/check-cas-internal-residue.py` is a registered ratchet with a four-guard control suite, each guard killing exactly one test under `mutation_controls.py`. `artifacts/measurements/cas-internal-residue-2026-09-04.md`. **Follow-on landed `f0bc8a692`**: Pratt and CRT certificates now reconstruct into kernel terms via square-and-multiply with reduction at every step (largest numeral formed n², not aⁿ⁻¹); **residue 46 → 45, reconstructed 14 → 16, floor raised to 16**. The brief nominated Pratt; measuring each family's largest numeral against the unary budget made CRT the only one whose every claimed instance the kernel reaches, so its fact flipped whole. Largest prime certified: 251 in 398 s, 101 inside a gate. The Mersenne-89 Pratt fact deliberately did NOT flip — no numeral budget reaches 2⁸⁹−1 — so the total understates two routes landing. [ADR-1622](../research/09-decisions/adr-1622-modular-exponentiation-is-what-makes-a-number-theory-certificate-reconstruct.md). |

## Wave 2 — carriers that convert theorems into instances

Each of these takes existing per-carrier results and makes them instances of
something. W2-1 and W2-2 depend on W0-3; the rest do not.

| id | item | source | status | blocked by |
|---|---|---|---|---|
| W2-1 | Metric-space carrier with ℝ and `CPoint` (C3) | 02.4, 03.3, 06.2 | **landed** `b7df58b7b` | **49 declarations, every footprint empty.** A 12-field `Metric` record; `Metric.creal` with `|x−y|` and `Metric.cpoint` with `sqrt distSq`, each `dist` selector proved to reduce definitionally. **Completeness generalized off ℝ** (`Metric.Complete`, `Metric.creal_complete`) at a cost of two bridge lemmas that already existed — the obstruction was that the convergence predicates are phrased on rational samples, not any topology. The plane's **unsquared** triangle inequality landed on the first kernel run, refuting a doc comment that called that statement inexpressible. |
| W2-2 | Continuity as a topological notion; `UniformlyContinuousOn` implies it | 06.4 | **landed** `5bb30b809` | 15 declarations over an *arbitrary pair* of metric spaces: uniform and pointwise continuity with `*On` twins, uniform ⇒ pointwise proved, the converse absent on purpose (Heine–Cantor needs the finite subcover ADR-1602 declines). **The `CReal` bridge cost zero estimates**: `Metric.dist creal x y` reduces to `abs (x + -y)` and the modulus was already in the `1/(k+1)` shape, so the two predicates are definitionally the same proposition. That was the case that could have refuted ADR-1602. [ADR-1607](../research/09-decisions/adr-1607-the-metric-layer-carries-w2-2-and-w2-3.md). |
| W2-3 | Bishop compactness on intervals; EVT re-derived as an instance | 06.3 | **landed** `5bb30b809` | Total boundedness plus completeness, no covers; `Metric.evt_approx_max` over any totally bounded subset of any metric space — **assuming total boundedness alone**, completeness never used, and a test pins that the rendered type mentions neither. A closed real interval is Bishop-compact. **The EVT derivation is a measurement, not a reading**: the interval EVT via `supOn` and the interval EVT via the general theorem carry the **same interned `ExprId`**, built by separate code in two modules. Finding to plan around: the general theorems are cheap and the instances are the work — 34 declarations for every carrier, 10 more for one interval. 43 of 44 admitted first time. |
| W2-4 | ℝⁿ as a carrier, `CPoint` as n = 2 (C7) | 05.2 | **landed** `d00d2a33c` | 58 declarations, footprint 0. **A vector is a coefficient function `Nat → CReal` and the dimension lives in the equivalence, not the type**: `EqOn n u v` agrees below `n`, so two vectors agreeing there *are* the same point — the quotient a tuple type would give, without one. `Fin n → CReal` rejected because `Fin` does not exist and the subtype route is closed (no `Subtype`, no `Sigma`). **Unsquared Cauchy–Schwarz at symbolic dimension**, whose induction step *is* the plane lemma `Metric.CPoint.dotLeSqrtMul` at the points `(‖u‖ₙ, uₙ)`, `(‖v‖ₙ, vₙ)` — no case split on vanishing, which `CReal` cannot do. Minkowski, then a `Metric` instance, then `CPoint` embedded as a setoid map with the equivalence transported both ways; the whole gap at bound 2 is one `zeroAdd`. Not landed: completeness of ℝⁿ, the inverse of the embedding (no transport between carriers). [ADR-1606](../research/09-decisions/adr-1606-rn-is-a-function-carrier-with-the-dimension-in-the-relation.md). |
| W2-5 | Power series with a radius of convergence | 02.2 | not started | — |
| W2-6 | Uniform convergence and the interchange theorems | 02.3 | **already done 2026-08-27** | `CReal.UniformConvergesOn`, `uniform_limit_uniformly_continuous`, `hasDerivative_uniform_limit`, `weierstrassMTest`. Audit row A3. |
| W2-7 | The weak law of large numbers | 08.1 | **already done 2026-08-24** | `Rat.weak_law_of_large_numbers` (`54592604a`), ten days before the review called it one limit away. Audit row A2. |
| W2-8 | First isomorphism theorem over `AlgS.Group` | 04.2 | **landed** `2a640c9b6` | Landed early, as W0-1's deciding experiment. 12 declarations in `AlgS.Hom.*`, footprint empty. The construction: a quotient group is the **same carrier under a coarser equivalence**, not a new carrier of classes. |
| W2-9 | Polynomial rings as a structure | 04.4 | **landed** `ecbf403f0`, **completed** `be87f45ca` | `AlgS.Poly.*`, 15 declarations over an abstract `AlgS.CommRing`: a polynomial is a coefficient function, convolution is an antidiagonal walk (because `Nat.sub` does not exist at the `AlgS` build position), with the additive `CommGroup` instance and both distributive laws. **Now a full `CommRing` instance, all 23 fields** (`AlgS.Poly.commRing`, ADR-1618): twelve declarations admitted on first submission, zero kernel rejections, **zero setoid cost**. ADR-1609's advice to restate the walk over `Nat.sub` was tried and declined on measurement — every `sumRange` lemma is over a concrete carrier so nothing would be reused, and the relocation is 1,300 lines. **What unblocked it was the induction motive, not the representation**: `Nat.rec` on the walk index with `∀ g` or `∀ j` in the motive, because the successor step recurses at a shifted family. `mulAssoc` needed no three-index exchange. ℚ[X], ℝ[X], ℂ[X] verified as instances in a test-local kernel. Two negatives: `Complex.polyEval_polyMul` already existed, so ADR-1609's "open for the same reason" was stale for ℂ; `Rat.polyEval_mul` is an ~800-line port not reachable from the abstract theorem, since no agreement lemma between the walk and the `sumRange`/`Nat.sub` representation exists. [ADR-1618](../research/09-decisions/adr-1618-the-antidiagonal-walk-keeps-its-shape-and-closes-the-polynomial-ring.md), [ADR-1609](../research/09-decisions/adr-1609-polynomials-modules-and-subgroups-over-the-setoid-spine.md). |
| W2-10 | Products and subspaces | 06.5 | not started | **should be SPLIT** (ADR-1602): the product is buildable today; the subspace is blocked on `Subtype`, which is absent from the kernel (verified case-sensitively with `Exists` as a positive control), so relativize rather than carve. |
| W2-11 | Ramsey's theorem for two colours | 07.3 | **landed** `0a499a6d8` | **`R(3,3) = 6` in both directions.** Upper bound a 32-leaf case tree over the five edges at vertex 0 — it had to be a *proof* because a graph is a function and the kernel cannot case over all graphs; lower bound a search over the 2¹⁰ five-vertex graphs returning the five-cycle, re-checked by reflection. If the search returns `None`, nothing is declared and the prelude fails to build. Cost: the `Nat` sweep went from ~18 s to 35–76 s, all Ramsey proof terms; `R(3,4)` needs the Ramsey recurrence, not this method. |
| W2-12 | Hall's marriage theorem | 07.4 | **necessity landed** `0a499a6d8`; the choice half of sufficiency closed `bc3eb38a5`; the counting half open | Necessity is one application of `card_le_of_injOn`. **Sufficiency is blocked on choosing the critical subfamily**: with no classical choice, the subset `t` with `card t = card (unionOver nb t)` must be *computed* by bounded search over `2^(bound s)` subsets with its own reflection lemma, and nothing of that shape exists — `allBelow_false_witness` is the one-dimensional model. **Second lane, 2026-09-04**: the subset-search reflection primitive landed — `decode`/`encode` over the existing `Nat.testBit` (found by searching the STEP; a whole bit decoder came off the diff), exhaustiveness, and `existsSubset_of_search`/`forallSubset_of_search` with the membership-congruence premise carried explicitly, because two `Nat.Finset`s with the same members are not `Eq`. `Nat.strongInduction` now exists, named. **The obstruction moved from choice to counting**: transporting `HallCondition` across `sdiff (nb i) (unionOver nb t)` is a counting argument over a union whose bound changes at every step, and `unionOver` has no congruence lemma because it reads the index set's *stored bound*. A next lane should size `unionOver` under family modification, not the search. [ADR-1614](../research/09-decisions/adr-1614-searching-over-subsets-is-a-reflection-primitive-not-a-hall-detail.md). |
| W2-13 | Isometries of the plane | 05.3 | **landed** `c7ddfeca1` | `Isometry f := ∀ P Q, distSq (f P) (f Q) ~ distSq P Q`; identity and composition — a **monoid**, since inverses need a surjectivity the predicate does not carry — `translate`, `rotate` and `reflect` under `c² + s² ~ 1`, `isometry_preserves_dot`, and the doubling map **refused**. The classification is sized at 25–40 declarations and blocked on nothing. |
| W2-14 | Computability layer: machine model, halting problem | 10.2 | **landed** `e15d807c8` | A shallow step-function register machine (`Nat.RM.runFuel`, `Halts`, `diagStep`) and `self_halting_not_decidable`: no total `H : Nat → Bool` is correct in both directions about whether `diagStep H` halts from `1`. Footprint 0. **Scoped precisely and not overclaimed**: a constructive refutation for its own machine, not Turing's theorem for a universal machine. The literal call through `cantor_no_fixed_point` did **not** land — the two cases are Π₁- and Σ₁-shaped — and [ADR-1611](../research/09-decisions/adr-1611-a-computability-layer-and-the-halting-problem.md) says so rather than claiming reuse. FO validity stays `open`. |
| W2-15 | Independence as a definition | 08.3 | **landed** `86c7a1065` | `Independent R A B p n := E[A·B] ~ E[A]·E[B]`, and `uncorrelated_of_independent` derives `covariance ~ 0`; composes into the existing `Rat.variance_add_of_uncorrelated` and the kernel accepts. Needs no commutativity only because `Rat.covariance` is already in computational form while `variance` is centred — relating the two forms needs `mulComm`, which the ordered-ring record cannot carry. **The bridge ADR-1612 named cannot be stated**: `IntSpace` is generic over the function space but hard-wired to `CReal` values, so no ℚ-valued integration space exists. Landed instead: the ℝ-valued expectation *is* the `crealFinite` integral definitionally, and the rational one is the integral across `CReal.ofRat`. |
| W2-16 | Nonlinear producer with Positivstellensatz certificates | 11.3 | not started | — (SOS certificates exist, nothing reconstructs them) |
| W2-17 | Unique factorization as a theorem over `Nat.Multiset` | 01.3 | **already done** | `Nat.Multiset.count_eq_of_prod_eq` with `exists_prime_factorization`. Audit row A5. |
| W2-18 | Multiplicative arithmetic functions as a family | 01.2 | not started | **[AUDIT] partially present**: `Nat.totient_mul_of_coprime` proves totient multiplicativity in exactly the general form the review denied (row A7). Möbius and Dirichlet convolution are confirmed absent. |
| W2-19 | General inclusion-exclusion | 07.5 | not started | — |
| W2-20 | Constructive MVT and differentiability on an interval | 02.5 | **already done 2026-08-27** | `fermat_interiorExtremum`, `rolle_interiorExtremum`, `mvt_interiorExtremum`. Audit row A8. It was never a prerequisite for W1-2 either. |
| W2-21 | A topological-space carrier, ℝ as the first instance | 03.2 | not started | **build it as a FRAME, not as open sets** (ADR-1602), and it is **off the critical path** — the metric layer serves the analysis shelf. |

## Wave 3 — the large shelves

Each is a quarter or more of work and each is gated on Wave 0.

| id | item | source | status | blocked by |
|---|---|---|---|---|
| W3-1 | Measure and the Lebesgue integral on ℝ (C5) | 03.4, 08.5 | **decided and opened** `3d5320f68` | **Integral-first, decided by measurement, and the brief's thesis was PARTIALLY REFUTED.** A predicative pre-integration space (`IntSpace`, 16 fields, 70 declarations, footprint 0) with three instances sharing no machinery — the interval integral, finite sums, and a Dirac space — measure *derived* as the integral of an integrable indicator with both bounds proved generically, every detachable subset of a finite index set proved integrable, and monotone convergence as an ADR-0603 graded family with the classical member on one binder. **The deciding number: 1 of 6 interval theorems re-derived, not most of them.** A record whose axioms come from what a development proves cannot re-derive what it took; the interval theorems ARE the record's axioms. What justifies integral-first instead is the three instances and five theorems new on ℝ that also land free on finite sums. Switching to Petrakis–Zeuner cost **zero** — the axioms-from-proofs discipline had already produced a predicative space. **L¹ as a completion: 0 of 78 reusable**, because `Metric.dist` is total while integrability is `Sort 1` data, and `Sigma`'s absence forbids bundling — **the third shelf today blocked by that one absence.** [ADR-1612](../research/09-decisions/adr-1612-the-integral-is-primitive-and-measure-is-derived-predicatively.md). |
| W3-2 | Vector spaces over an abstract field, bases, dimension | 04.5 | **modules landed** `ecbf403f0`; vector spaces blocked | `AlgS.Module.*`, 23 declarations: `IsModule` as five conjuncts plus a congruence conjunct, `selfModule` and `polyModule` instances, `neg_smul`, `smul_zero`, `zero_smul`, and a basis layer (`linComb`, `spans`, `linearIndependent`, `isBasis`). **Two obstructions, both `Quot`-independent**: (a) no module *record* — `declare_record` fixes one universe level per field kind, so a record cannot hold a record, and lifting wholesale puts the carrier where a function type cannot sit; sized in ADR-1609 as a per-field level on `FieldSpec`, a change to shared `structures.rs`, its own lane. (b) dimension needs `AlgS.Field`, which needs `Apart`, the open question ADR-1588 named. The ℚ bridge's real cost is `rowEchelon_isEchelon` (ADR-1554 obligation 4); do not price it as small. |
| W3-3 | Categories, functors, natural transformations | 09.4 | not started | W0-1 |
| W3-4 | Products and coproducts as universal properties | 09.5 | not started | W3-3 |
| W3-5 | Complex analysis: holomorphy, Cauchy's theorem | 03.5 | not started | W2-4, W3-1 |
| W3-6 | First-order model theory: structures, satisfaction, soundness | 10.3 | not started | W0-2 (completeness needs a choice principle) |
| W3-7 | Arithmetization of syntax, toward Gödel I | 10.4 | not started | W2-14 |
| W3-8 | Synthetic incidence geometry, coordinate plane as a model | 05.4 | not started | — |
| W3-9 | Conics as a family | 05.5 | not started | W1-8 |
| W3-10 | Sums of two squares with reusable descent | 01.4 | not started | — |
| W3-11 | Chebyshev-type bounds on π(x) | 01.5 | not started | — |
| W3-12 | Bernoulli and binomial distributions; Hoeffding | 08.4 | not started | W1-10 |
| W3-13 | Universal-property template for new carriers | 09.2 | **landed** `c64893719` | `docs/research/08-planning/universal-property-template.md`: a four-part shape — the category's defining axioms as hypotheses only, the mediating map as a named `Definition`, existence by the map's own computation rules, pointwise uniqueness by induction on the source. |

## What is deliberately not on this roadmap

- **Algebraic geometry, algebraic topology, and representation theory.** All
  three sit behind W0-1 *and* several waves of algebra. Reviewers 05, 06 and 04
  name them; none of them ranks one in a Next Five, which is the correct call.
- **Coverage parity with Mathlib.** The chair refuses the claim
  ([12](12-the-chair.md)); the defensible one is per-statement dominance plus
  uncontested axes.
- **Anything on the `open` Mathlib transcription queue** (262 facts). That is a
  separate, already-running work stream and it does not need a roadmap.

## Status board

One row per wave. Update when something lands, then append to the history log.

| wave | items | not started | in progress | landed |
|---|---|---|---|---|
| wave | items | not started | in progress | landed | **already done** ⁽ᵇ⁾ |
|---|---|---|---|---|---|
| W0 — decisions | 5 | 0 | 1 | **4** | 0 |
| W1 — unblocked | 13 | 0 | 0 | **13** | **1** |
| W2 — carriers | 21 | 8 | 0 | **12** | **2** |
| W3 — large shelves | 13 | 9 | 0 | **3** | **1** |
| **total** | **52** | **17** | **1** | **32** | **4** |

⁽ᵇ⁾ **Already done before the roadmap was written, and the review did not
know.** The audit found 11 of 76 absence claims false. Four were roadmap
items: W1-2 (FTC), W2-6 (uniform convergence and the interchange theorems),
W2-7 (the weak law of large numbers), W2-20 (the constructive MVT). Seven of
the eleven landed on 2026-08-27, one week before the reviews.

⁽ᵃ⁾ W2-1 is in progress inside the W0-3 lane, which builds the metric carrier
to decide the topology design.

**Wave 0 is complete.** All four decisions were made on 2026-09-04, and three
of the four came with working mathematics attached rather than only a
document.

Round three, dispatched 2026-09-04 after the second push (`a1e6c17ad`): W0-5
(dependent pairs, decided by re-testing the three blocked sites), W2-12's
residue (Hall sufficiency via a subset-search reflection lemma and a named
`Nat.strongInduction`), W1-8 with W2-13, W1-10 with W2-15 and the ℚ↔ℝ
probability bridge, W2-9's residue (the polynomial `CommRing` instance), and
W1-12 with W1-13 (the two measurements the applied reviewer has never seen
quoted).

**A new blocker has surfaced three times in one day and deserves a name:
`Sigma` and `Subtype` are absent from the kernel.** ADR-1595 found the
classical first-isomorphism statement needs a subtype for the image; ADR-1602
found subspaces need `Subtype`; ADR-1612 found L¹ as a completion needs
`Sigma` to bundle an integrability witness into a carrier. Dependent pairs are
an ordinary inductive, not an axiom, and nothing in the setoid discipline
forbids them. This is the next Wave 0-shaped item and it is not on the board.

**The setoid decision has now been tested at scale, and the finding runs
further in its favour than ADR-1595 claimed.** The algebra lane landed 58
declarations over the setoid spine with **one kernel rejection**, a Rust-side
universe slip. And it found that the `Eq` route **cannot state a polynomial
ring at all**: the carrier is a function space, so the `Eq` form of
commutativity is an equality of two lambdas, which needs `funext` and which
`Quot.sound` would not supply. Every construction whose carrier is a function
type is reachable *only* on the setoid spine. Setoids are not the cheap
option here; they are the only option.

**Every decision was settled the same way**, and
the method is now the department's default: do not weigh the arguments, build
the theorem the decision is about and report what it cost. W0-1 cost three
lines; W0-2 cost eleven binders and no obligations. In both cases the
measurement pointed the opposite way from the reviewer's expectation.

**A new W1 item the W1-5 lane's failure identified:** a `CReal` apartness or
witnessed-separation definition, without which `decide` has no decidable
fragment over ℝ at all. Not yet numbered; it is new mathematics, not a
producer change.

**A standing correction to how this roadmap is read — now settled by
measurement.** The audit ([AUDIT-2026-09-04.md](AUDIT-2026-09-04.md)) checked
all 76 absence claims across the twelve files against a freshly rebuilt kernel
index: **11 false, 12 overstated, 51 confirmed absent, 2 unsettled.** Four of
the false ones were roadmap items and are marked *already done* above.

The cause is measured and is bigger than these files. Of 2,493 proved facts,
**1,553 (62.3%) carry no characterisation of their own** — 1,054 with the fact
generator's `[generated]` title, plus a class nobody had counted, 499 titled
only "Mathlib v4.30 source proposition `<Name>`". And the ledger does not
cover the kernel at all for **430 theorems and 762 of 789 definitions**,
including `AlgS.Hom.firstIso`, the headline result of reviewer 04. So the
ledger answers *is X proved?* and cannot answer *what do we have?*
[ADR-1605](../research/09-decisions/adr-1605-the-ledger-cannot-tell-uncharacterised-from-absent.md)
decides the fix — characterisation as a derived, ratcheted measurement rather
than a stored field — and ships `scripts/check-fact-characterisation.py` with
a 17-test control suite. The kernel-versus-ledger coverage gate is sized and
deferred at about half a day.

**Standing rule for anyone using this roadmap:** re-measure before briefing a
lane against an absence, with a positive control that postdates the change you
are asking about. The audit's § E documents how.

Item count is 51 rather than 60 because nine of the sixty Next Five entries are
the same request made by a second or third reviewer; see the convergence table.
Every one of the sixty appears in exactly one wave row — checked, not assumed,
by the count above.

Reviewer verdicts as of the last reconciliation:

| reviewer | verdict | changes when |
|---|---|---|
| 01 number theory | impressed, with a ceiling | W1-7, W2-17, W2-18 land |
| 02 constructive analysis | excited | W1-2 lands |
| 03 classical analysis | unmoved | W0-2, W0-3, W3-1 land |
| 04 algebra | **upgraded 2026-09-04** — the blocker is decided and the first isomorphism theorem is proved | W2-9, W3-2 land |
| 05 geometry | charmed, then bored | W1-8, W2-4 land |
| 06 topology | nothing to review | W0-3 is decided and W2-1 lands |
| 07 combinatorics | week three, good foundations | W1-1, W1-6 land |
| 08 probability | better than first reported | W2-7 lands |
| 09 category theory | absent, opposed; morphism-equality question answered by W0-1 | W1-3 lands (cheap), W3-3 (real) |
| 10 logic & foundations | most interested; W0-4 landed | W1-9 lands |
| 11 applied & computational | most novel object here | W1-1, W1-5 land |
| 12 the chair | would sign the report; W0-1 written, W1-4 landed | W0-2 is written |

## History

| date | commit | change |
|---|---|---|
| 2026-09-04 | `f36120646` | Twelve persona files created; sixty Next Five items recorded. |
| 2026-09-04 | `d73328291` | Roadmap synthesized: 60 Next Five entries → 51 distinct items, 7 convergences, 4 waves. Baseline status: nothing started. |
| 2026-09-04 | `8b4f277d4` | **W0-4 and W1-4 landed.** ADR-1600 (trusted base 5,526 lines, three guards shown firing, a fourth shown inert) and the landmark counter (1,432 of 2,487 proved). |
| 2026-09-04 | `2a640c9b6` | **W0-1 decided and W2-8 landed together.** The first isomorphism theorem over `AlgS.Group`, footprint empty, at a measured cost of three lines versus having `Quot.sound`. ADR-1595 recommends setoid quotients. Suites after: `structures_setoid` 18, `first_iso` 5, `linarith` 99. |
| 2026-09-04 | (see history) | Off-roadmap: the safety-matrix gate had been red on main since 2026-08-31; regenerated, 1,823 rows in and 1,514 out. Found by the W0-4 lane and reported rather than worked around. |
| 2026-09-04 | `a9ef9465d` | **W1-7 landed.** 11 declarations, footprint 0; existence mod a prime stopped at a named obstruction. `int_prelude::` 87 passed. |
| 2026-09-04 | `024830694` | Off-roadmap: gate-hygiene landed. Against a fresh projection, 39 absence claims were retired as *present* (two of them EXPIRED) and 17 confirmed absent; nine stale doc comments claiming no `sqrt` exists corrected. `check-absence-claims.py` is **still red, 150 bare against a budget of 122**, and the lane's finding is that the remainder is dominated by three claim shapes the marker grammar cannot express, so the budget or the grammar needs a decision, not more annotation. Recommendation recorded: do not add it to the push hook. |
| 2026-09-04 | `f0bc8a692` | **W1-13 follow-on: the residue moved.** 46 → 45 cas-internal, 14 → 16 reconstructed. `int_prelude::` 100 passed. |
| 2026-09-04 | `86c7a1065` | **W1-10 and W2-15 landed; Wave 1 is complete** (13 of 13, one of them already done). 29 generic probability declarations, 9+2 of 11 ℚ theorems instances by kernel check. Finding for W3-1's follow-on: `IntSpace` is hard-wired to `CReal` values, so a ℚ-valued integration space cannot be stated; the bridge goes through `ofRat` instead. `rat_prelude::` 287 passed. |
| 2026-09-04 | `c7ddfeca1` | **W1-8 and W2-13 landed.** Trigonometry and geometry now touch, cosine-first; 32 declarations. Off-roadmap finding the lane surfaced: `check-absence-claims.py` is red on main (206 bare claims against a budget of 122, two expired), pre-existing and not in the push hook; a gate-hygiene lane is dispatched. |
| 2026-09-04 | `be87f45ca` | **W2-9 completed**: the polynomial ring is a full `CommRing` instance, twelve declarations with zero rejections and zero setoid cost. The motive, not the representation, was the unblock. |
| 2026-09-04 | `0ba67b82e` | **W1-12 and W1-13 landed.** Two numbers the applied reviewer asked for, both unflattering: `e` at the loosest precision does not normalize in 400 s (unary recursion inside the series), and 76.7% of CAS certificates never reconstruct. Both published; the second is a ratchet. |
| 2026-09-04 | `bc3eb38a5` | **W2-12's choice half closed.** The subset-search reflection primitive and `Nat.strongInduction`; Hall sufficiency's obstruction moved from choice to counting. `nat_prelude::` 532 passed; both new names FOUND by a fresh `shape_search`. |
| 2026-09-04 | `a1e6c17ad` | Second push of the day landed (51 commits, then a 1-commit ledger fix). Round three dispatched: six lanes, seven items plus W0-5. Item count 51 → 52. |
| 2026-09-04 | `d00d2a33c` | **W2-4 landed.** ℝⁿ with the dimension in the equivalence, unsquared Cauchy–Schwarz at symbolic dimension generalizing the plane lemma, a `Metric` instance, `CPoint` embedded. A merge defect it exposed: two lanes taught the retrieval tools a new group each, the additive resolver kept both `use` blocks, and main did not compile for one commit until the imports were deduplicated. |
| 2026-09-04 | `5bb30b809` | **W2-2 and W2-3 landed in full.** 44 declarations, 43 first-time admissions. The `CReal` continuity bridge is definitional; the interval EVT and the metric EVT are the same interned term. ADR-1602's bet is paying. |
| 2026-09-04 | `3d5320f68` | **W3-1 decided and opened.** Integral-first, 70 declarations, measure derived, monotone convergence as a graded family. The brief's thesis partially refuted: 1 of 6 interval theorems re-derived, because they are the record's axioms. `Sigma`'s absence blocks a third shelf. `intspace::` 14, `creal::` 236 passed pre-merge. |
| 2026-09-04 | `ecbf403f0` | **W2-9 landed, W3-2 half, W1-11's residue closed.** 58 setoid-spine declarations with one kernel rejection. The finding: function-space carriers are statable ONLY over setoids, since `Eq` on lambdas needs `funext`. Two `Quot`-independent obstructions named: one universe level per record field kind, and `AlgS.Field` needing `Apart`. |
| 2026-09-04 | `e15d807c8` | **W2-14 landed.** A register machine and a precisely-scoped constructive refutation of self-halting decidability. The Cantor call did not land (Π₁ vs Σ₁ case shapes) and the ADR says so. `nat_prelude::` 478 passed pre-merge. |
| 2026-09-04 | `0a499a6d8` | **W1-6, W2-11 landed; W2-12 half.** `Nat.Graph` (39 decls), **`R(3,3) = 6` both directions from search**, Hall necessity. Sufficiency stopped at a named obstruction: computing the critical subfamily without choice. `nat_prelude::` 495 passed. |
| 2026-09-04 | `c64893719` | **W1-3 and W3-13 landed.** ℕ and ℤ named as initial objects from existing theorems; the universal-property template written. |
| 2026-09-04 | `b7df58b7b` | **W0-3 and W2-1 landed; Wave 0 is complete.** A `Metric` carrier with 49 declarations, both instances, completeness generalized off ℝ, and the plane's unsquared triangle inequality — which refutes a doc comment calling that statement inexpressible. Two retrieval tools were found blind to the new prelude and would have reported a confident ABSENT for all 49; both fixed. `metric::` 17, `creal_point::` 66, `creal::` 236 passed. |
| 2026-09-04 | `80aa8e52c` | **W0-2 and W1-9 landed together.** Classical principles stay hypotheses (ADR-1601), decided by carrying one through ten theorems and measuring: 11 binders, zero obligations, no growth with depth. Ten new theorems, empty footprints. A merge-pass defect it exposed: regenerating the creal steps table during conflict resolution moved a pinned test the lane never touched; fixed and the pin rewritten from the generator (`creal::` 236 passed). |
| 2026-09-04 | `fa18f3481` | **The audit landed.** 76 absence claims checked, 11 false, 12 overstated. Four roadmap items were already done. ADR-1605 and `check-fact-characterisation.py` address the cause. Two off-lane findings: `count-landmark-facts.py --check` was already red on main, and one fact carried a curated statement under an "uncurated" title. |
| 2026-09-04 | `de0cd02da` | **W1-1 landed — the flagship.** Schur's `R_2(x = y + z) = 5` proved in-kernel from search in both halves, 17 declarations, footprint 0. The unary-numeral constraint in the brief was measured false: a `Prop` mentioning a numeral never reduces it. |
| 2026-09-04 | `a3f4f528c` | **W1-5 landed.** `ring` reaches `CReal.commRingS` (6 goal shapes, kernel-refused corruptions); `decide` cannot, with the reason measured; zero retirements after a real prelude-build decline was reverted rather than shipped. `ring::` 74, `decide::` 47, `creal::creal_tests` 140 passed. |
| 2026-09-04 | `182d0dd7d` | **W1-2 landed, and the item was based on a false absence.** The FTC was proved 2026-08-27. The `_of_uc` forms landed; W2-20 is not its prerequisite. `creal::` 230 passed. Root cause measured at 38% of the ledger; ADR-1605 proposes the fix and an audit of all twelve files is running. |

## How to update this file

1. **When an item lands**, change its status in its wave table, adjust the
   status board counts, and append a history row naming the commit.
2. **When a verdict changes**, edit the reviewer's own file first — the verdict
   line, the progress log, and any Next Five item that is now done — then
   reflect it in the verdict table here. The persona file is the authority;
   this file is the view.
3. **When a Next Five changes**, re-derive the affected wave rows rather than
   patching them, so the convergence count stays true.
4. **Do not renumber.** W-ids are cited from lane briefs and status files.
   A dropped item becomes `superseded` with a note, never a reused number.
5. **Re-measure before re-verdicting.** Every claim in the persona files names
   the command that produced it; a verdict that improves without a measurement
   behind it is exactly the drift the board exists to prevent.

## Related

- [README.md](README.md) — the board, the shared snapshot, and the rules
- [PLAN.md](../../PLAN.md) — the actual work queue; this file never schedules
- [The curriculum graph](../curriculum/README.md) — teaching order, a different
  ordering of overlapping material
- [The cost model and Pareto position](../formalized-math-2026-08/07-the-cost-model-and-pareto-position.md)
- [Computable knowledge](../research/00-orientation/computable-knowledge-world-graph.md)
  — where this library goes after the mathematics

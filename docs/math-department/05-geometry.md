# 05 — Geometry

Reviewer: a geometer — Euclidean, differential, algebraic
Verdict, 2026-09-06: **upgraded — one seat of three is now satisfied**
Last measured: 2026-09-06 at `1de0edfc6`

> "In two days the plane stopped being a pile of coordinates and became an
> axiomatic subject with two models. The classical seat has nothing left to
> complain about. The other two seats are still empty chairs."

> **AUDITED 2026-09-04.** Every absence claim in this file was re-checked
> against a freshly rebuilt kernel index. See
> [AUDIT-2026-09-04.md](AUDIT-2026-09-04.md) for the evidence, and the
> corrections marked **[AUDIT]** below. Across the twelve files, 11 of 76
> absence claims were false and 12 more overstated the gap; the cause is that
> the ledger characterises only 38% of its proved facts and does not cover 430
> kernel theorems at all (ADR-1605).

> **RE-MEASURED 2026-09-06** at `1de0edfc6`, against a `shape_search` index of
> 4,839 declarations. Every count below was re-run; the verdict, the missing
> list and the blockers were rewritten rather than annotated. The four items
> the 2026-09-04 verdict named as the gap — angles, ℝⁿ, synthetic geometry,
> conics — all landed.

## The persona

Three people in one seat, because the department seats them together and they
would give the same verdict for different reasons. The classical geometer
enjoys the plane and knows every theorem here. The differential geometer wants
manifolds, tangent spaces, curvature, and connections. The algebraic geometer
wants varieties, schemes, sheaves, and would settle for a polynomial ring in
two variables.

## What the library has today

**101 proved plane-geometry facts, zero open, all axiom-free** (`fragment ==
"CPoint"`; was 94 on 2026-09-04). The kernel index carries **204 `CPoint`
declarations, 164 `Geo`, 97 `Metric` and 58 `RN`**. The plane's carrier is
still `CPoint`: a one-constructor inductive over two constructed reals, in
`Type 0`, built entirely from `CRealPrelude`'s public surface.

| layer | what exists |
|---|---|
| carrier | `CPoint.mk`, `.x`, `.y`, `Equiv`, `neg`, `lerp` |
| forms | `dot`, `cross`, `distSq`, `midpoint`, `centroid`, and a `CPoint.Scalar` namespace with `two`, `three`, `inv3`, `midpoint`, `centroid`, `lerp` |
| predicates | `Collinear`, `NonCollinear`, `OnCircle`, `OnPerpBisector` |
| inequalities | Cauchy–Schwarz in squared form, `distSq_double_sum_bound`, `eq_zero_of_dot_self_zero` |
| named theorems | Stewart's theorem (squared parametric form), Ptolemy's inequality (`Complex.ptolemy_inequality_sq`), Ceva (`ceva_ratio_product_of_concurrent`), Menelaus, the Euler line with `nine_point_centre_on_euler_line`, power of a point (`power_of_centre`), the radical axis (`radical_axis_iff_dot`), the Euler quadrilateral identity |
| angle (ADR-1615) | `norm`, `crossV`, the Lagrange identity, the laws of cosines and sines, `cosAngle`/`sinAngle` under a `PosBound`, and `sin² + cos² = 1` for the angle ratios — cosine-first, with **no `arccos` and no trigonometric name in the closure** (`creal_point/angle.rs`) |
| transformations (ADR-1615) | `Isometry` as a `distSq`-preserving map, identity and composition (a **monoid** — inverses need a surjectivity the predicate does not carry), `translate`, `rotate`, `reflect` under `c² + s² ~ 1`, and the doubling map refused by a checked refutation (`creal_point/isometry.rs`) |
| conics (ADR-1641) | `CPoint.Conic` as a six-coefficient inductive, the discriminant classification with three pairwise exclusions and a named inhabitant per class, circles as an instance, unconditional rotate/reflect/translate invariance, the standard forms, and the focus–directrix property of the parabola (`creal_point/conic.rs`) |
| ℝⁿ (ADR-1606) | `RN` at symbolic dimension — a vector is a coefficient function and the dimension lives in the equivalence; unsquared Cauchy–Schwarz, Minkowski, a `Metric` instance, and `CPoint` embedded as a setoid map agreeing on `dot`, `distSq` and the metric distance |
| synthetic (ADR-1635, 1652, 1659) | `Geo.Incidence` as a setoid record carrying Hilbert I.1–I.3, five derived theorems, and **both** coordinate planes as full models (`Geo.qplane`, `Geo.rplane`); `Geo.Affine` over it with a **positive** parallelism, Playfair's existence and uniqueness, `parallel_trans` derived once, and both planes as affine instances (`Geo.qaffine`, `Geo.raffine`) |

Five ledger facts carry the synthetic layer, and every one of them is a
`kernel-term`: `F:geo-incidence-model-rational-plane`,
`F:geo-incidence-model-real-plane`, `F:geo-affine-model-rational-plane`,
`F:geo-affine-model-real-plane`, `F:geo-distinct-lines-meet-once`. Each names a
`Definition` admitted at the record's type, so *every* field — all 21 for
`Incidence`, all 7 for `Affine` — was supplied and checked.

Alongside it, a CAS-certified rational-coordinate track:
**15 committed certificates** in `artifacts/geometry-certificates/`, produced
by `axeyum-cas`'s `geometry_certify`/`geometry_check` pair and replayed by a
checker that shares no code with the search. Ten of the fifteen have a ledger
fact (`F-geometry-*`, `witness-replay`); of the 19 `F-geometry-*` facts, **9
carry kernel-term evidence and 10 do not**. Medians, centroids, the
orthocentre, the parallelogram and rhombus identities, and Thales additionally
reconstruct into kernel terms as multivariate cofactor identities over six
universally quantified `Rat` coordinates (`rat_prelude/cas_geometry_*`).

`NonCollinear` is carried as a positive apartness witness, not as the negation
of `Collinear`, which is the constructively correct choice and matches the
treatment of apartness on the line. The synthetic layer repeats that choice
twice more: distinctness and nondegeneracy in `Geo.rplane` are `PosBound`
witnesses, and `Geo.Affine`'s parallelism is positive (same direction plus a
witnessed distinctness) because the negative "no common point" ends Playfair's
uniqueness half at tightness, which this kernel refuses by design.

## Their verdict

**The classical geometer has run out of reservations.** The 2026-09-04
complaint was "it is all coordinates — no synthetic development, no incidence
axioms, so the library cannot say anything about geometry as an axiomatic
subject." That is now false. `Geo.Incidence` states Hilbert's incidence axioms
over an abstract setoid record; `Geo.Affine` adds Playfair; `parallel_trans` is
proved once for *every* affine plane and inherited by both models. The
rational plane and the real plane are each proved to satisfy the whole record,
which is the consistency argument they asked for, done twice. The olympiad
corpus is still there and still good — Stewart, Ceva, Menelaus, Ptolemy, the
Euler line, the nine-point circle — and it now sits under an angle measure and
an isometry group rather than beside them.

Their one remaining note is about *strength*, not about kind: incidence plus
Playfair is a long way short of Hilbert or Tarski. There is no betweenness, no
order, no segment or angle congruence: the only `Parallel` is the incidence
one, and every occurrence of "congruence" in the `geo` shelf is the *setoid*
congruence of an operation, not the geometric relation. So the axiomatic
subject the library can now discuss is affine incidence geometry, not
Euclidean geometry.

**The differential geometer still finds nothing, but the floor moved.** ℝⁿ
exists (`RN`, 58 declarations) as a metric space at *symbolic* dimension, with
Cauchy–Schwarz and Minkowski proved once for all n and `CPoint` embedded as
the n = 2 instance. That was their prerequisite and it landed. What is on top
of it is nothing: `rn.rs` contains no derivative, no partial derivative, no
gradient. No manifolds, no charts, no tangent spaces, no differential forms,
no curvature, no geodesics — the words "manifold", "sheaf", "tangent space"
do not occur anywhere in the kernel source.

**The algebraic geometer still finds nothing, and the reason has changed.**
No affine varieties, no ideals — the word `ideal` occurs **zero times in the
whole kernel source**, not merely in the algebra shelf — no Nullstellensatz
theorem, no projective space, no schemes. But the
2026-09-04 blocker was quotients, and quotients landed: `AlgS.Hom.quotient`
and `AlgS.Hom.firstIso` are proved over setoids
([04-algebra.md](04-algebra.md)). The gate is now commutative algebra itself,
not the thing that gated it. They would also note two things that cut across
the trust boundary: `Complex.polyEval`/`polyMul`/`factorQuotient` are a
one-variable polynomial theory, and multivariate polynomial identities over ℚ
*do* reach the kernel — six of them, as CAS cofactor certificates
reconstructed into `Check.geometry_*_cofactor_identity`. What is missing is
the ring, not the arithmetic.

## What they would say is missing

- **Order and congruence axioms.** Incidence plus Playfair is affine geometry.
  Betweenness and segment/angle congruence on top of `Geo.Incidence`, with
  both planes still models, is what turns it into Hilbert- or
  Tarski-strength. Neither primitive exists in `geo.rs` today.
- **Multivariate calculus on `RN`.** The carrier landed; the derivative did
  not. This is the gate on differential geometry and on most of classical
  analysis, and it is ordinary work in
  [02-constructive-analysis.md](02-constructive-analysis.md).
- **Manifolds.** Beyond calculus, they need function spaces, hence `funext` or
  a setoid discipline for maps.
- **Commutative algebra with ideals.** Rings, ideals, prime and maximal
  ideals, R/I. Zero occurrences of `ideal` anywhere in the kernel source; the
  quotient machinery to build them now exists.
- **The isometry classification.** "Every isometry is a rotation-or-reflection
  after a translation" is not proved. `isometry.rs` sizes it honestly at 25–40
  declarations across four sub-shelves, dominated by `CPoint.smul`
  bilinearity and a sign decision resolved by `apart_cotrans`. Blocked on
  nothing.
- **The angle as a number.** `sin` and `cos` exist analytically on ℝ and the
  plane has `cosAngle`/`sinAngle`, but the two are still not connected: there
  is no `arccos` and no theorem relating `CReal.cos_fn` to `CPoint.cosAngle`.
  ADR-1615 argues this buys the *name* of the angle and nothing else; it is a
  deliberate gap, not an oversight.
- **Solid and higher-dimensional synthetic geometry.** `RN` gives ℝⁿ as a
  metric space, and the CAS certifies two genuine 3-D results (the tetrahedron
  medians, and the concurrence of the perpendicular bisector planes). Neither
  has a ledger fact, so by [ADR-0601](../research/09-decisions/adr-0601-three-producers-one-trust-anchor.md)
  neither is a proved result of this library. Nothing synthetic above the
  plane.
- **Projective geometry as a subject.** Pascal on a parabola and affine
  Desargues certify in the CAS and are committed as artifacts, but have no
  fact and no kernel term. Pappus and Simson have facts, but with
  `witness-replay` evidence only and no kernel counterpart anywhere.

## The blocker

Different per seat, and none of them is `Quot.sound` any more:

- **Classical/synthetic:** nothing blocks it, and nothing blocked the last
  three slices either. Order and congruence axioms are ordinary kernel work
  and the existing two planes are ready-made models. The one measured
  obstruction the lanes hit was *shape*, not principle: a negatively stated
  parallelism ends at tightness, so the primitive was restated positively
  (ADR-1652 § 5, ADR-1659).
- **Differential:** blocked on multivariate differentiation over the `RN`
  carrier, which is ordinary work in
  [02-constructive-analysis.md](02-constructive-analysis.md) and does not need
  a new axiom. Manifolds themselves need function spaces and therefore
  `funext` or a setoid discipline for maps.
- **Algebraic:** blocked on commutative algebra — rings with ideals — which is
  no longer blocked on quotients, since setoid quotients and the first
  isomorphism theorem are proved ([04-algebra.md](04-algebra.md)).
- **Not a blocker, contrary to the record:** the conic lane left
  line-meets-conic open "because it needs a square root". `CReal.sqrt` exists
  on main (`creal/sqrt.rs`, `declare_sqrt`; the module's own header prose
  still says it does not, and is stale). Whether the argument goes through
  with it is **not measured** — but the stated reason is one route's claim,
  not a standing obstruction.

## Next five, in their priority order

The 2026-09-04 five are now four landed and one part-landed; the current five
are below them.

- [ ] **1. The isometry classification.** Every isometry is a
      rotation-or-reflection after a translation. Carries item 3 of the
      previous list forward: `isometry.rs` sizes it at 25–40 declarations,
      names the four sub-shelves, and says it is blocked on nothing.
- [ ] **2. Multivariate calculus on `RN`.** A derivative over the existing
      symbolic-dimension carrier. The gate on the whole differential seat, and
      shared with [02-constructive-analysis.md](02-constructive-analysis.md).
- [ ] **3. Betweenness and congruence over `Geo.Incidence`.** The step from
      affine incidence geometry to Hilbert/Tarski strength, with both
      coordinate planes still proved to be models. The record spine and the
      two-model discipline already exist; this is more of the same work.
- [ ] **4. A polynomial ring in several variables, with ideals.** The
      algebraic seat's first genuine step. The kernel already admits
      multivariate cofactor identities over ℚ from the CAS; what it lacks is
      the ring object and `ideal`.
- [ ] **5. Facts for the five orphan certificates, or a written reason.**
      Pascal on a parabola, affine Desargues, the conic polar–tangent
      identity, and the two tetrahedron results are certified, replayed and
      committed — and have no ledger fact, so they are `cas-internal`. Two of
      them are the only solid geometry anywhere in the system.

### The 2026-09-04 five, at 2026-09-06

- [x] **1. Angle measure, and the laws of sines and cosines.** *Landed
      `c7ddfeca1` (ADR-1615), cosine-first.* `norm`, `crossV`, the Lagrange
      identity, both laws, and `sin² + cos² = 1` for the angle ratios, with no
      trigonometric name in the closure. The analytic `sin_fn`/`cos_fn` are
      still not connected to the angle, deliberately.
- [x] **2. ℝⁿ as a carrier.** *Landed `d00d2a33c` (ADR-1606), 58
      declarations.* The dimension lives in the equivalence; `CPoint` embeds
      as the n = 2 instance; `RN` is 58 declarations in the index today.
- [~] **3. Isometries of the plane.** *Monoid, translations, rotations,
      reflections and the doubling non-example landed `c7ddfeca1`; the
      classification is still not started* — sized in `isometry.rs` at 25–40
      declarations and carried forward as item 1 above.
- [x] **4. A synthetic incidence development with the coordinate plane as a
      model.** *Landed in three slices: the record and the ℚ model
      `992de4c54` (ADR-1635), the ℝ model `ef30df0e4` (ADR-1652), Playfair and
      both affine instances `6842d3773` (ADR-1659).* 164 `Geo` declarations,
      five facts, every one kernel-term. Hilbert I.1–I.3 plus Playfair — not
      Tarski, which is item 3 above.
- [x] **5. Conics as a family.** *Landed `31cda11c7` (ADR-1641), 56
      declarations.* Classification, isometry invariance and standard forms
      with no square root anywhere; the circle case recovers `OnCircle` as an
      `Iff`.

## Progress log

| date | change | evidence |
|---|---|---|
| 2026-09-04 | File created. Baseline: 94 proved plane facts over `CPoint`. Stewart, Ceva, Menelaus, Ptolemy, Euler line, nine-point centre, power of a point, radical axis. No ℝⁿ, no manifolds, no varieties, no angle measure. | ledger snapshot at `1856cdb3c` |
| 2026-09-04 | **Next Five item 2 landed** (roadmap W2-4): ℝⁿ as a coefficient function with the dimension carried by the equivalence rather than the type, 58 declarations, footprint 0. **Unsquared Cauchy–Schwarz at symbolic dimension**, whose induction step is exactly the plane's `dotLeSqrtMul` at the points `(‖u‖ₙ, uₙ)` and `(‖v‖ₙ, vₙ)` — the plane lemma became the engine of the general one, and no case split on whether the norm vanishes was needed, which is fortunate because `CReal` has no `le_total`. Minkowski, a `Metric` instance, and `CPoint` embedded as a setoid map with agreement on `dot`, `distSq` and the metric distance. Not landed: the inverse of the embedding, since two `Metric` values with different carriers admit no equality without a transport this kernel lacks. (ADR-1606.) | `d00d2a33c`; `rn::` 24 passed |
| 2026-09-04 | **Next Five items 1 and 3 landed** (roadmap W1-8, W2-13; ADR-1615): the seam this reviewer called the most conspicuous in the shelf is closed, cosine-first. `norm`, `crossV`, the Lagrange identity, the laws of cosines and sines, and `sin² + cos² = 1` for the angle ratios, proved with no trigonometric name in the closure. The analytic `sin_fn`/`cos_fn` are still not connected to the angle; the brief's assumption that the analytic Pythagorean identity existed was false; `arccos` is sized at three analytic results deep. Isometries as a monoid with translations, rotations and reflections, the doubling map refused; the classification sized at 25–40 declarations, blocked on nothing. Five doc comments in `creal_point.rs` still claim `sqrt` does not exist. | `c7ddfeca1`; `creal_point::` 69 passed |

| 2026-09-05 | **Item 4, first slice** (roadmap W3-8, ADR-1635): `Geo.Incidence` as a setoid record with Hilbert's incidence axioms, five derived theorems, and the rational coordinate plane as a full model — 75 axiom-free declarations. Distinctness is a field because only the uniqueness axiom consumes it. The real plane did not land: its uniqueness axiom needs the cancellation route through `PosBound` and `CReal.inv`. Along the way the rational ring producer gained the cancellation pass it lacked. | `992de4c54` |
| 2026-09-05 | **Item 5 landed** (roadmap W3-9, ADR-1641): conics as a six-coefficient family with the discriminant classification (exclusions and inhabitants), circles as an instance, unconditional invariance under the existing isometries with every ring identity discharged by the producer, the standard forms with their signs, and the focus–directrix property of the parabola; 56 axiom-free declarations. Left open: a line meets a conic in at most two points (needs a square root), the reflective property (needs tangents), the circle converse (needs `inv`). The Next Five for this reviewer is now four of five done, with the real-plane incidence model the remaining half of item 4. | `31cda11c7`; `creal_point::` 82 passed in the lane |
| 2026-09-06 | **Item 4, second slice** (roadmap W3-8, ADR-1652): the real plane as a full model of the incidence axioms, with distinctness and nondegeneracy as apartness witnesses and the uniqueness axiom through one pivot identity whose leading factor is the squared distance itself; 44 axiom-free declarations, shorter than the rational model. Playfair's axiom did not land, and the reason is the shape of 'parallel': the negative form needs tightness, which this kernel refuses by design; the positive form is three ring identities already verified numerically. | `ef30df0e4`; `geo::` 20 passed in the lane |
| 2026-09-06 | **Playfair's axiom** (roadmap W3-8, ADR-1659): the affine plane as a record over the incidence record with parallelism stated positively, Playfair's existence and uniqueness, transitivity of parallelism derived once for every affine plane, and both the rational and the real plane proved affine; 45 axiom-free declarations. The real plane's existence half needs no division. A latent double-negation defect in the shared rational ring producer was found by the kernel and recorded. | `6842d3773`; `geo::` 27 passed in the lane |
| 2026-09-06 | **Re-measured against main and rewritten.** Verdict **upgraded**: the classical seat's 2026-09-04 objection ("no synthetic development, no incidence axioms") is measurably false — `Geo` is 164 declarations with five kernel-term facts, and both coordinate planes are proved models of incidence + Playfair. Plane facts 94 → **101 proved, 0 open**; index totals `CPoint` 204, `Geo` 164, `Metric` 97, `RN` 58 at `declarations=4839`. Corrections to this file's own claims: the algebraic seat's blocker is no longer quotients (`AlgS.Hom.quotient`/`firstIso` are proved) but commutative algebra itself; "everything is the plane" is now qualified — `RN` is ℝⁿ at symbolic dimension and the CAS certifies two tetrahedron results. Two findings the ledger does not show: **five of the fifteen committed geometry certificates have no fact at all** (Pascal, affine Desargues, the conic polar–tangent identity, and both tetrahedron results), so they are `cas-internal` under ADR-0601, and of 19 `F-geometry-*` facts only 9 carry kernel-term evidence — Pappus and Simson have none. Also stale on main and not fixed here: `creal/sqrt.rs`'s module header still says `CReal.sqrt` does not exist, which is why the conic lane's "needs a square root" reads as a blocker. No geometry work is waiting in any lane worktree. | measured at `1de0edfc6`; `shape_search --include-constructed --list-namespaces` and `--ns Geo` (`FOUND 164`) |

## How to re-measure

```sh
python3 - <<'PY'
import json, glob, collections
c = collections.Counter()
for f in glob.glob('artifacts/facts/*.json'):
    d = json.load(open(f))
    if (d.get('formal') or {}).get('fragment') == 'CPoint': c[d.get('epistemic_status')] += 1
print(c)
PY

# the kernel index: CPoint, Geo, Metric and RN in one pass. `--include-constructed`
# is REQUIRED -- without it none of these four namespaces is built at all.
target/release/examples/shape_search --include-constructed --list-namespaces \
  | grep -E 'NAMESPACE  (CPoint|Geo|Metric|RN) '

# the synthetic shelf on its own (2026-09-06: FOUND 164)
target/release/examples/shape_search --include-constructed --ns Geo | tail -1

# the CAS half: certificates committed vs certificates with a ledger fact
ls artifacts/geometry-certificates/*.json | wc -l
ls artifacts/facts/F-geometry-*.json | wc -l
```

## Related

- [02-constructive-analysis.md](02-constructive-analysis.md) — ℝⁿ and
  multivariate calculus, the gate on differential geometry
- [04-algebra.md](04-algebra.md) — the gate on algebraic geometry
- [06-topology.md](06-topology.md)
- [13-computer-algebra.md](13-computer-algebra.md) — the producer behind the
  geometry certificates, and the trust boundary they sit on

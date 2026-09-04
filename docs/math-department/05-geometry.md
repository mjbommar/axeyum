# 05 — Geometry

Reviewer: a geometer — Euclidean, differential, algebraic
Verdict, 2026-09-04: **charmed, then bored**
Last measured: 2026-09-04 at `1856cdb3c`

> "The nine-point centre on the Euler line, machine-checked over constructive
> reals. That is a lovely thing to find. Now show me a manifold."

> **AUDITED 2026-09-04.** Every absence claim in this file was re-checked
> against a freshly rebuilt kernel index. See
> [AUDIT-2026-09-04.md](AUDIT-2026-09-04.md) for the evidence, and the
> corrections marked **[AUDIT]** below. Across the twelve files, 11 of 76
> absence claims were false and 12 more overstated the gap; the cause is that
> the ledger characterises only 38% of its proved facts and does not cover 430
> kernel theorems at all (ADR-1605).

## The persona

Three people in one seat, because the department seats them together and they
would give the same verdict for different reasons. The classical geometer
enjoys the plane and knows every theorem here. The differential geometer wants
manifolds, tangent spaces, curvature, and connections. The algebraic geometer
wants varieties, schemes, sheaves, and would settle for a polynomial ring in
two variables.

## What the library has today

**94 proved plane-geometry facts, zero open, all axiom-free.** The carrier is
`CPoint`: a one-constructor inductive over two constructed reals, in `Type 0`,
built entirely from `CRealPrelude`'s public surface.

| layer | what exists |
|---|---|
| carrier | `CPoint.mk`, `.x`, `.y`, `Equiv`, `neg`, `lerp` |
| forms | `dot`, `cross`, `distSq`, `midpoint`, `centroid`, and a `CPoint.Scalar` namespace with `two`, `three`, `inv3`, `midpoint`, `centroid`, `lerp` |
| predicates | `Collinear`, `NonCollinear`, `OnCircle`, `OnPerpBisector` |
| inequalities | Cauchy–Schwarz in squared form, `distSq_double_sum_bound`, `eq_zero_of_dot_self_zero` |
| named theorems | Stewart's theorem (squared parametric form), Ptolemy's inequality (`Complex.ptolemy_inequality_sq`), Ceva (`ceva_ratio_product_of_concurrent`), Menelaus, the Euler line with `nine_point_centre_on_euler_line`, power of a point (`power_of_centre`), the radical axis (`radical_axis_iff_dot`), the Euler quadrilateral identity |

Alongside it, a CAS-certified rational-coordinate track: medians, centroids
and rhombus identities reconstructed from computer-algebra certificates into
kernel terms (`rat_prelude/cas_geometry_*`).

`NonCollinear` is carried as a positive apartness witness, not as the negation
of `Collinear`, which is the constructively correct choice and matches the
treatment of apartness on the line.

## Their verdict

**The classical geometer is genuinely pleased.** This is a well-chosen
olympiad-to-classical corpus: Stewart, Ceva, Menelaus, Ptolemy, the Euler line
and the nine-point circle are the results a strong contest student meets and
they are not trivial to formalize. Doing them over *constructive* reals, with
`NonCollinear` as data, is more careful than the classical treatment needs to
be. Their reservation is that it is all coordinates. There is no synthetic
development, no incidence axioms, no Hilbert or Tarski axiomatization, so the
library cannot say anything about geometry as an axiomatic subject — only
about the specific coordinatized plane it built.

**The differential geometer finds nothing.** No manifolds, no charts, no
tangent spaces, no differential forms, no curvature, no geodesics. The
prerequisite is multivariate calculus over ℝⁿ, which does not exist either;
`CPoint` is the plane as a pair of reals with no calculus on it at all.

**The algebraic geometer finds nothing.** No affine varieties, no ideals, no
Nullstellensatz, no projective space, no schemes. The prerequisite is
commutative algebra, which is blocked on quotients
([04-algebra.md](04-algebra.md)). They would note that
`Complex.polyEval`/`polyMul` and `factorQuotient` are the beginnings of a
polynomial theory and that a polynomial ring in one variable is within reach —
but a variety needs several variables and an ideal.

## What they would say is missing

- **Synthetic geometry.** An incidence-axiom development (Hilbert or Tarski)
  with the coordinatized plane as a *model*, which would let the library say
  something about geometry rather than only about ℝ².
- **ℝⁿ and multivariate calculus.** The gate on differential geometry and on
  most of classical analysis too.
- **Transformations as a group.** Isometries, similarities, the Euclidean
  group acting on the plane — which needs group actions, hence
  [04-algebra.md](04-algebra.md).
- **Trigonometry as geometry.** `sin` and `cos` exist analytically on ℝ; they
  are not connected to angles in `CPoint`, so there is no angle measure, no
  law of sines or cosines as geometry, no inscribed-angle theorem.
- **Conics beyond circles.** `OnCircle` exists; ellipse, parabola, hyperbola
  do not.
- **Solid and higher-dimensional geometry.** Everything is the plane.

## The blocker

Different per seat, and none of them is `Quot.sound` in the first instance:

- **Classical/synthetic:** nothing blocks it. An incidence structure and a
  Tarski-style axiom set are ordinary kernel work, and the existing plane is a
  ready-made model to prove them consistent against.
- **Differential:** blocked on ℝⁿ and multivariate differentiation, which is
  ordinary work in [02-constructive-analysis.md](02-constructive-analysis.md)
  and does not need a new axiom. Manifolds themselves need function spaces
  and therefore `funext` or a setoid discipline for maps.
- **Algebraic:** blocked on commutative algebra, hence on the quotient
  decision in [04-algebra.md](04-algebra.md).

## Next five, in their priority order

- [ ] **1. Angle measure, and the laws of sines and cosines.** Connect the
      analytic `sin`/`cos` to `CPoint`'s `dot` and `cross`. Their view: the
      library has trigonometry and it has geometry and they do not touch,
      which is the most conspicuous seam in the shelf.
- [ ] **2. ℝⁿ as a carrier**, with the existing `CPoint` as the n = 2
      instance, and the inner product and norm proved once. Prerequisite for
      almost everything else here and for classical analysis.
- [ ] **3. Isometries of the plane**, as maps preserving `distSq`, with
      composition and the classification into translations, rotations and
      reflections. Reachable now, and the first real use of transformations.
- [ ] **4. A synthetic incidence development with the coordinate plane as a
      model.** Tarski's axioms are finitely many first-order sentences; proving
      the constructed plane satisfies them is a genuine result and exactly the
      kind of thing this kernel is good at.
- [ ] **5. Conics as a family**, defined by a quadratic form over `CPoint`,
      with the circle case recovering the existing `OnCircle`. Uses the
      polynomial machinery already built over ℚ and ℂ.

## Progress log

| date | change | evidence |
|---|---|---|
| 2026-09-04 | File created. Baseline: 94 proved plane facts over `CPoint`. Stewart, Ceva, Menelaus, Ptolemy, Euler line, nine-point centre, power of a point, radical axis. No ℝⁿ, no manifolds, no varieties, no angle measure. | ledger snapshot at `1856cdb3c` |

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

grep -rhoE '"CPoint\.[A-Za-z][A-Za-z0-9_.]*"' crates/axeyum-lean-kernel/src/ \
  | tr -d '"' | sort -u
```

## Related

- [02-constructive-analysis.md](02-constructive-analysis.md) — ℝⁿ and
  multivariate calculus, the gate on differential geometry
- [04-algebra.md](04-algebra.md) — the gate on algebraic geometry
- [06-topology.md](06-topology.md)

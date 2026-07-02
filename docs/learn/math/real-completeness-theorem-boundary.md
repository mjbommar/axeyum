# Real Completeness Theorem Boundary

This page is the concrete boundary for the recurring real-analysis question:

```text
When does a finite rational shadow become a theorem about the real numbers?
```

Today, Axeyum checks bounded rational intervals, finite epsilon-tail rows,
finite monotone prefixes, finite Cauchy-tail samples, finite compactness
tables, and algebraic real shadows. Those are useful executable examples. They
are not proofs of least-upper-bound completeness, Cauchy completeness,
monotone convergence, Bolzano-Weierstrass, Heine-Borel, or uniform
continuity.

The trust split stays the same:

```text
untrusted fast search -> candidate bound, tail, cover, root, or counterexample
trusted small checking -> exact rational replay, finite enumeration, or certificate checking
theorem horizon -> quantified real theorem with a no-sorry Lean route
```

## Concept Rows

- `curriculum_reals`
- `curriculum_sequences_and_limits`
- `curriculum_calculus`
- `field_real_analysis`
- `field_topology`
- `bridge_rational_interval_replay`
- `bridge_sequence_tail_shadow`
- `bridge_cauchy_tail_shadow`
- `bridge_bounded_epsilon_delta_shadow`
- `bridge_metric_ball`
- `bridge_compactness_shadow`
- `bridge_continuity_preimage`
- `bridge_lean_horizon`

These rows live in the
[Foundational Concept Atlas](../../../artifacts/ontology/foundational-concepts.json).

## Existing Finite Shadows

| Theorem Target | Current Packs | What Axeyum Checks Today | What This Does Not Prove |
|---|---|---|---|
| Least-upper-bound completeness | [real-analysis-rational-v0](../../../artifacts/examples/math/real-analysis-rational-v0/), [bounded-monotone-sequence-v0](../../../artifacts/examples/math/bounded-monotone-sequence-v0/) | exact rational interval containment, finite upper-bound checks, finite prefix supremum replay, separate checked bad upper-bound Farkas proof row | every nonempty bounded real set has a supremum |
| Cauchy completeness | [sequence-limit-shadow-v0](../../../artifacts/examples/math/sequence-limit-shadow-v0/), [bounded-monotone-sequence-v0](../../../artifacts/examples/math/bounded-monotone-sequence-v0/) | finite pairwise tail-distance enumeration, finite tail-gap replay, checked bad reciprocal-tail row and separate checked bad tail-gap proof row | every real Cauchy sequence converges |
| Monotone convergence | [bounded-monotone-sequence-v0](../../../artifacts/examples/math/bounded-monotone-sequence-v0/) | adjacent finite-prefix monotonicity, fixed upper bound replay, finite prefix supremum, one finite tail gap | every bounded monotone real sequence converges to its supremum |
| Ordered-field and real-closed-field shadows | [reals-rcf-shadow-v0](../../../artifacts/examples/math/reals-rcf-shadow-v0/) | ordered-field replay, nonlinear product replay, quadratic-root witness replay, checked negative-discriminant conflict | completeness of the real numbers or arbitrary real-closed-field theorem coverage |
| Metric continuity and uniform-continuity prerequisites | [metric-continuity-v0](../../../artifacts/examples/math/metric-continuity-v0/), [real-analysis-rational-v0](../../../artifacts/examples/math/real-analysis-rational-v0/) | fixed finite metric balls, finite epsilon-delta samples, finite open-ball preimage replay, checked bad-delta and bad-preimage Farkas rows | quantified epsilon-delta continuity or uniform continuity on compact sets |
| Compactness prerequisites | [finite-compactness-v0](../../../artifacts/examples/math/finite-compactness-v0/), [finite-topology-v0](../../../artifacts/examples/math/finite-topology-v0/) | finite open-cover and subcover enumeration, finite topology axiom replay, checked bad-cover Boolean evidence | Heine-Borel, Bolzano-Weierstrass, arbitrary compactness, or continuous-image compactness |

## Lean Horizon Dependency Ledger

A theorem route for real completeness should make these dependencies explicit
before any finite shadow is allowed to graduate:

| Dependency | Needed For | Current Axeyum Status |
|---|---|---|
| Ordered-field structure and order laws | stating rational and real inequalities, intervals, and algebraic side conditions | finite exact-rational and RCF-shadow replay exists |
| Supremum and infimum definitions | least-upper-bound completeness and monotone convergence | horizon only |
| Cauchy sequence and sequence convergence definitions | Cauchy completeness and limit theorems | finite tail shadows only |
| Archimedean and density facts | epsilon/N arguments and rational approximations | rational witnesses only |
| Metric and topological definitions | metric balls, open preimages, compactness, connectedness | finite metric/topology replay only |
| Compactness theorem family | Heine-Borel, Bolzano-Weierstrass, uniform continuity on compact sets | finite open-cover and finite tail shadows only |
| No-sorry theorem artifact and axiom audit | trusting the general theorem rather than the finite sample | not built |

The desired Lean artifact is not just a comment that says "completeness." It
must state the theorem, all hypotheses, the exact conclusion, imported lemmas,
and the axiom boundary. It must fail rather than silently use `sorry`.

## Query The Current Boundary

From the repository root, inspect the current real-analysis shadows:

```sh
python3 scripts/query-foundational-resources.py concepts \
  --field real_analysis \
  --text completeness \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack real-analysis-rational-v0 \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack sequence-limit-shadow-v0 \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack bounded-monotone-sequence-v0 \
  --route Farkas \
  --proof-status checked \
  --text qf-lra-bad-tail-gap \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack metric-continuity-v0 \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack reals-rcf-shadow-v0 \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-compactness-v0 \
  --route Boolean \
  --proof-status checked \
  --require-any
```

The first query is deliberately broad: it surfaces real-analysis concepts that
mention completeness-adjacent packs. The remaining queries show concrete
checked rows that should be treated as examples, not theorem proof.

## Replay The Example Packs

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/real-analysis-rational-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/sequence-limit-shadow-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/bounded-monotone-sequence-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/metric-continuity-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/reals-rcf-shadow-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-compactness-v0
```

Expected shape for each command:

```text
validated 1 foundational example pack(s)
```

## Graduation Criteria

Real completeness moves out of this boundary page only when all of the
following are true:

1. A theorem stub states least-upper-bound completeness, Cauchy completeness,
   and monotone convergence as separate theorem targets.
2. Each theorem target links the finite packs above as examples only.
3. The Lean route records the imported order, metric, sequence, and topology
   dependencies needed to state the theorem.
4. The artifact has no `sorry` fallback and carries an axiom audit.
5. The resource metadata still distinguishes checked finite rows from
   theorem-level proof rows.

Until then, the right claim is narrower and stronger: Axeyum can search for
finite rational witnesses quickly, then replay or check the small evidence
independently. The real theorem is a proof-assistant target, not an inference
from finite samples.

## Related Pages

- [Analysis And Calculus Theorem Horizon Map](analysis-calculus-theorem-horizon-map.md)
- [Monotone Convergence Theorem Boundary](monotone-convergence-theorem-boundary.md)
- [Metric Balls And Epsilon-Delta Index](metric-ball-epsilon-delta-index.md)
- [Analysis And Topology Proof Horizons](analysis-topology-proof-horizons.md)
- [Bounded Rational Real Analysis](real-analysis-rational-end-to-end.md)
- [Sequence And Limit Shadows](sequence-limit-shadow-end-to-end.md)
- [Bounded Monotone Sequence](bounded-monotone-sequence-end-to-end.md)
- [Metric Continuity](metric-continuity-end-to-end.md)
- [Real Algebra RCF Shadow](reals-rcf-shadow-end-to-end.md)

## Validation

This page is a learner/planning layer over existing validated packs. It should
not change resource counts.

```sh
./scripts/check-links.sh
python3 scripts/query-foundational-resources.py summary
```

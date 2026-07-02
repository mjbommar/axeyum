# Metric Balls And Epsilon-Delta Index

This index ties the bounded real-analysis and finite-topology resources into
one path. It is for the recurring question: how does a metric-ball or
epsilon-delta claim become something Axeyum can check without pretending it has
proved the general theorem?

The answer is always the same:

```text
untrusted fast search -> candidate radius, delta, cover, preimage, or counterexample
trusted small checking -> exact rational or finite-set replay plus checked certificates
remaining horizon -> quantified continuity, compactness, connectedness, and convergence theorems
```

## Concept Rows

- `bridge_metric_ball`
- `bridge_bounded_epsilon_delta_shadow`
- `bridge_continuity_preimage`
- `bridge_compactness_shadow`
- `bridge_connectedness_shadow`
- `field_real_analysis`
- `field_topology`
- `curriculum_reals`
- `curriculum_sequences_and_limits`
- `curriculum_calculus`

These rows live in the
[Foundational Concept Atlas](../../../artifacts/ontology/foundational-concepts.json).

## Resource Map

| Question | Packs | Trusted Check | Horizon |
|---|---|---|---|
| Which points are in a ball? | `finite-topology-v0`, `real-analysis-rational-v0`, `metric-continuity-v0` | strict rational distance comparison over a finite carrier | general metric-space topology |
| Does one fixed delta work? | `real-analysis-rational-v0`, `metric-continuity-v0` | exact rational replay of listed samples; QF_LRA/Farkas for bad deltas | forall-epsilon exists-delta continuity |
| Does a finite tail satisfy an epsilon bound? | `sequence-limit-shadow-v0`, `bounded-monotone-sequence-v0` | exact finite prefix/tail replay; separate QF_LRA/Farkas proof rows for bad bounds | convergence and completeness theorems |
| Does a cover or separation work? | `finite-compactness-v0`, `finite-connectedness-v0` | finite set-family enumeration; Bool/CNF evidence for bad rows | compactness and connectedness theorems |
| Is continuity visible topologically? | `metric-continuity-v0`, `finite-continuous-maps-v0` | finite open-ball or open-set preimage replay | arbitrary continuous-map theorems |

## Checkable Shapes

Metric-ball rows are finite membership checks:

```text
B(c, r) = { x | d(x, c) < r }
```

The checker needs a finite carrier, an exact rational distance table, a center,
and a rational radius. It recomputes membership with strict inequality and no
floating-point tolerance.

Bounded epsilon-delta rows fix the quantifiers instead of proving the theorem:

```text
epsilon = 1
delta = 1/2
center = p0
sample = {p0, p1, p2, p3}
```

The checker recomputes all listed distances and output bounds. A bad row is
promoted only when the final rational contradiction is small enough for checked
QF_LRA/Farkas evidence, such as `output_distance = 1` together with
`output_distance < 1`.

Topology rows use the same idea with finite set families. Compactness becomes
cover and subcover enumeration. Connectedness becomes clopen or open-separation
enumeration. Continuity becomes preimage enumeration.

## How The Pieces Fit

Start with exact rational balls in
[Bounded Rational Real Analysis](real-analysis-rational-end-to-end.md). That
page shows nested intervals, finite rational ball membership, one bounded
linear epsilon-delta witness, and a checked bad-delta certificate.

Move to [Metric Continuity](metric-continuity-end-to-end.md) when the same
shape is represented as a finite metric table. The finite domain ball around
`p0` must map into the finite output ball around `f(p0)`, and bad deltas become
source-linked QF_LRA/Farkas regressions. The same pack also checks a malformed
open-ball preimage row by replaying the output-ball membership table before
checking the final strict-bound contradiction.

Use [Sequence And Limit Shadows](sequence-limit-shadow-end-to-end.md) for the
epsilon-N version of the same boundary. The pack checks only listed tails,
prefixes, and pairwise distances; it does not prove convergence in complete
metric spaces.

Use [Finite Topology](finite-topology-end-to-end.md),
[Finite Compactness](finite-compactness-end-to-end.md), and
[Finite Connectedness](finite-connectedness-end-to-end.md) when the metric
story is replaced by open-set families. The trusted object is still finite
enumeration, not a general theorem.

Use [Finite Continuous Maps](finite-continuous-maps-end-to-end.md) when the
continuity claim is phrased as open preimages. This is the topological version
of the metric-continuity sample: recompute the preimage and check it is open in
the finite domain topology.

## Query It

From the repository root:

```sh
python3 scripts/query-foundational-resources.py concepts --field topology --text metric --require-any
python3 scripts/query-foundational-resources.py concepts --field real_analysis --text epsilon --require-any
python3 scripts/query-foundational-resources.py packs --concept bridge_metric_ball --route Farkas --require-any
python3 scripts/query-foundational-resources.py packs --concept bridge_bounded_epsilon_delta_shadow --route Farkas --require-any
python3 scripts/query-foundational-resources.py checks --concept bridge_bounded_epsilon_delta_shadow --route Farkas --proof-status checked --require-any
```

## Replay It

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/real-analysis-rational-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/metric-continuity-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/sequence-limit-shadow-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-topology-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-compactness-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-connectedness-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-continuous-maps-v0
```

Expected shape:

```text
validated 1 foundational example pack(s)
```

for each command.

## Trust Boundary

The resources here are useful because they separate three claims that are easy
to blur:

- A listed finite ball, cover, separation, or preimage can be replayed exactly.
- A listed false linear bound can be rejected with checked Farkas evidence.
- The general theorem with quantified neighborhoods, arbitrary spaces, or
  infinite covers remains a Lean/theorem horizon.

Read this index before
[Analysis And Topology Proof Horizons](analysis-topology-proof-horizons.md)
when you want the shortest path from delta-epsilon intuition to Axeyum's
current finite and bounded evidence.

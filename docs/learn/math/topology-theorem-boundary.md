# Topology Theorem Boundary

This page separates Axeyum's finite topology, compactness, connectedness,
continuous-map, quotient-topology, and specialization-order resources from
general topology theorems.

Primary packs:

- [finite-topology-v0](../../../artifacts/examples/math/finite-topology-v0/)
- [finite-compactness-v0](../../../artifacts/examples/math/finite-compactness-v0/)
- [finite-connectedness-v0](../../../artifacts/examples/math/finite-connectedness-v0/)
- [finite-continuous-maps-v0](../../../artifacts/examples/math/finite-continuous-maps-v0/)
- [finite-quotient-topology-v0](../../../artifacts/examples/math/finite-quotient-topology-v0/)
- [finite-specialization-order-v0](../../../artifacts/examples/math/finite-specialization-order-v0/)

Companion lessons and maps:

- [Analysis And Topology Proof Horizons](analysis-topology-proof-horizons.md)
- [Metric Balls And Epsilon-Delta Index](metric-ball-epsilon-delta-index.md)
- [End To End: Finite Topology](finite-topology-end-to-end.md)
- [End To End: Finite Compactness](finite-compactness-end-to-end.md)
- [End To End: Finite Connectedness](finite-connectedness-end-to-end.md)
- [End To End: Finite Continuous Maps](finite-continuous-maps-end-to-end.md)
- [End To End: Finite Quotient Topology](finite-quotient-topology-end-to-end.md)
- [End To End: Finite Specialization Order](finite-specialization-order-end-to-end.md)
- [Theorem Horizon Queries](../../foundational-resources/THEOREM-HORIZON-QUERIES.md)

## Current Finite Resources

The finite topology resources work by enumerating small sets, listed open
families, finite maps, finite preimages, quotient fibers, and finite
neighborhood relations. They are useful because every accepted row can be
replayed directly against the original finite object.

The checked rows are still scoped:

```text
finite topology axioms:       finite set-family replay plus one Bool/CNF bad row
compactness shadows:          listed finite covers and subcovers
connectedness shadows:        clopen-subset and open-separation enumeration
continuous maps:              finite function tables and open-preimage replay
quotient topology:            finite fibers and preimage-open enumeration
specialization order:         finite open-neighborhood preorder replay
general theorem layer:        arbitrary spaces, preservation, invariance, and universal properties
```

Those rows prove bounded facts about displayed finite topological data. They
do not prove compactness theorems, connectedness theorems, continuous-image
theorems, homeomorphism invariance, quotient universal properties,
specialization-order theorems, metrization, Tychonoff, or Heine-Borel.

## Claim And Evidence Rows

| Check | Expected | Evidence Status | What It Means |
|---|---|---|---|
| `finite-topology-axioms` | `sat` | replay-only finite table | The listed open-set family satisfies the finite topology axioms. |
| `closure-interior-witness` | `sat` | replay-only finite table | Interior and closure are recomputed from listed opens. |
| `metric-ball-witness` | `sat` | replay-only finite metric | A displayed finite metric ball has the listed points. |
| `bad-empty-open-rejected` | `unsat` | checked Bool/CNF DRAT/LRAT | A malformed open family omits the empty set. |
| `finite-open-cover-subcover` | `sat` | replay-only finite table | A displayed finite open cover has the listed finite subcover. |
| `minimal-subcover-size-witness` | `sat` | checked finite enumeration | No one-set subcover exists for the displayed cover. |
| `finite-intersection-family-witness` | `sat` | replay-only finite table | A listed closed family has the finite-intersection property. |
| `bad-open-cover-rejected` | `unsat` | checked Bool/CNF DRAT/LRAT | The displayed family misses a point and is not an open cover. |
| `general-compactness-lean-horizon` | `not-run` | Lean horizon | General compactness and finite-intersection-property theorems remain future proof work. |
| `finite-connected-space-witness` | `sat` | replay-only finite table | A finite Sierpinski space has only trivial clopen subsets. |
| `finite-disconnected-separation-witness` | `sat` | replay-only finite table | A discrete two-point space has an open separation. |
| `clopen-subset-disconnection-witness` | `sat` | replay-only finite table | A nontrivial clopen subset witnesses finite disconnection. |
| `bad-connected-claim-rejected` | `unsat` | checked Bool/CNF DRAT/LRAT | A false connectedness claim is rejected for a finite discrete space. |
| `general-connectedness-lean-horizon` | `not-run` | Lean horizon | General connectedness and preservation theorems remain future proof work. |
| `finite-continuous-map-witness` | `sat` | replay-only finite table | A finite map is continuous by open-preimage enumeration. |
| `open-preimage-witness` | `sat` | replay-only finite table | One codomain open set has the listed open preimage. |
| `finite-homeomorphism-witness` | `sat` | replay-only finite table | A finite bijection and its inverse are continuous by enumeration. |
| `bad-continuous-map-rejected` | `unsat` | checked finite replay | A proposed continuous map has a non-open preimage. |
| `qf-uf-bad-preimage-membership` | `unsat` | checked QF_UF/Alethe | A malformed preimage-membership table contradicts function membership. |
| `bad-homeomorphism-claim-rejected` | `unsat` | checked finite replay | A bijection is rejected because continuity fails. |
| `general-continuous-map-lean-horizon` | `not-run` | Lean horizon | Arbitrary-space continuity and homeomorphism theorems remain future proof work. |
| `quotient-map-fiber-witness` | `sat` | replay-only finite table | A quotient map is surjective and has the listed fibers. |
| `quotient-topology-witness` | `sat` | replay-only finite table | Quotient opens are recomputed by source preimages. |
| `saturated-open-image-witness` | `sat` | replay-only finite table | A saturated open source set maps to a quotient-open set. |
| `bad-fiber-representative-rejected` | `unsat` | checked QF_UF/Alethe | Two same-fiber representatives cannot have distinct quotient images. |
| `bad-quotient-open-rejected` | `unsat` | checked QF_UF/Alethe | A false quotient-open claim is rejected by finite preimage replay. |
| `general-quotient-topology-lean-horizon` | `not-run` | Lean horizon | General quotient-space and universal-property theorems remain future proof work. |
| `specialization-preorder-witness` | `sat` | replay-only finite table | A finite topology induces the listed specialization preorder. |
| `closure-characterization-witness` | `sat` | replay-only finite table | The preorder agrees with singleton closure in this finite space. |
| `t0-poset-witness` | `sat` | replay-only finite table | The finite `T0` space has an antisymmetric specialization order. |
| `bad-t0-antisymmetry-rejected` | `unsat` | checked QF_UF/Alethe | A false `T0`/antisymmetry claim is rejected for an indiscrete finite space. |
| `general-specialization-order-lean-horizon` | `not-run` | Lean horizon | General specialization-order, sobriety, and domain-theory results remain future proof work. |

The boundary is:

```text
untrusted fast search -> candidate finite topology, map, cover, quotient, or order row
trusted small checking -> finite replay plus Bool/CNF or QF_UF/Alethe evidence
theorem horizon       -> arbitrary-space theorems, preservation, invariance, universality
```

## What Is Not Proved Yet

The current packs do not prove:

- arbitrary topological-space theorem schemas;
- compactness theorems such as Heine-Borel, Tychonoff, compactness
  preservation under continuous images, or finite-intersection-property
  equivalences beyond displayed finite covers;
- connectedness preservation, path-connectedness theorems, component theory,
  or local connectedness results;
- homeomorphism invariance of arbitrary topological or algebraic-topological
  invariants;
- quotient topology universal properties or arbitrary quotient-map
  preservation theorems;
- T0 quotient theorems, sobriety, Alexandroff-space/domain-theory results, or
  specialization-order theorem schemas;
- metrization, separation axioms, compact-open topology, product topology, or
  sheaf/topos-level topology;
- homology or cohomology invariance, exact-sequence theory, or universal
  coefficient theorems.

Those claims need theorem statements, hypotheses, and no-`sorry` proof
artifacts before they can graduate from horizon metadata to theorem coverage.

## Query The Boundary

Validate the finite packs:

```sh
python3 scripts/validate-foundational-example-pack.py \
  artifacts/examples/math/finite-topology-v0 \
  artifacts/examples/math/finite-compactness-v0 \
  artifacts/examples/math/finite-connectedness-v0 \
  artifacts/examples/math/finite-continuous-maps-v0 \
  artifacts/examples/math/finite-quotient-topology-v0 \
  artifacts/examples/math/finite-specialization-order-v0
```

Find the checked finite topology rows:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack finite-topology-v0 \
  --route boolean \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-compactness-v0 \
  --route boolean \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-connectedness-v0 \
  --route boolean \
  --proof-status checked \
  --require-any
```

Find checked finite-map, quotient, and specialization rows:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack finite-continuous-maps-v0 \
  --route Alethe \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-quotient-topology-v0 \
  --route Alethe \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-specialization-order-v0 \
  --route Alethe \
  --proof-status checked \
  --require-any
```

Find the theorem horizons:

```sh
python3 scripts/query-foundational-resources.py horizon-frontier \
  --pack finite-compactness-v0 \
  --require-any

python3 scripts/query-foundational-resources.py horizon-frontier \
  --pack finite-connectedness-v0 \
  --require-any

python3 scripts/query-foundational-resources.py horizon-frontier \
  --pack finite-continuous-maps-v0 \
  --require-any

python3 scripts/query-foundational-resources.py horizon-frontier \
  --pack finite-quotient-topology-v0 \
  --require-any

python3 scripts/query-foundational-resources.py horizon-frontier \
  --pack finite-specialization-order-v0 \
  --require-any
```

Find the bridge concepts:

```sh
python3 scripts/query-foundational-resources.py concepts \
  --field topology \
  --text compactness \
  --require-any

python3 scripts/query-foundational-resources.py concepts \
  --field topology \
  --text homeomorphism \
  --require-any

python3 scripts/query-foundational-resources.py concepts \
  --field topology \
  --text quotient \
  --require-any

python3 scripts/query-foundational-resources.py concepts \
  --field topology \
  --text specialization \
  --require-any
```

## Graduation Criteria

Topology resources graduate only when they add:

1. precise theorem statements for the compactness, connectedness,
   continuity, quotient, specialization-order, or invariance claim;
2. explicit hypotheses, including separation axioms, finite/infinite domain,
   topology kind, continuity assumptions, quotient-map assumptions,
   compactness/connectedness assumptions, and codomain conditions;
3. no-`sorry` proof artifacts for each theorem claim before display labels
   change from finite replay to theorem coverage;
4. a kernel-checked route that connects a finite example to a theorem
   instantiation only where that instantiation is actually proved;
5. display labels that keep finite replay, Bool/CNF evidence, QF_UF/Alethe
   evidence, and theorem horizons separate.

Until then, these packs remain finite checked resources and compact bridges to
future topology proof resources.

## Validate

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-topology-v0 artifacts/examples/math/finite-compactness-v0 artifacts/examples/math/finite-connectedness-v0 artifacts/examples/math/finite-continuous-maps-v0 artifacts/examples/math/finite-quotient-topology-v0 artifacts/examples/math/finite-specialization-order-v0
python3 scripts/query-foundational-resources.py checks --pack finite-topology-v0 --route boolean --proof-status checked --require-any
python3 scripts/query-foundational-resources.py checks --pack finite-compactness-v0 --route boolean --proof-status checked --require-any
python3 scripts/query-foundational-resources.py checks --pack finite-connectedness-v0 --route boolean --proof-status checked --require-any
python3 scripts/query-foundational-resources.py checks --pack finite-continuous-maps-v0 --route Alethe --proof-status checked --require-any
python3 scripts/query-foundational-resources.py checks --pack finite-quotient-topology-v0 --route Alethe --proof-status checked --require-any
python3 scripts/query-foundational-resources.py checks --pack finite-specialization-order-v0 --route Alethe --proof-status checked --require-any
python3 scripts/query-foundational-resources.py horizon-frontier --pack finite-compactness-v0 --require-any
python3 scripts/query-foundational-resources.py horizon-frontier --pack finite-connectedness-v0 --require-any
python3 scripts/query-foundational-resources.py horizon-frontier --pack finite-continuous-maps-v0 --require-any
python3 scripts/query-foundational-resources.py horizon-frontier --pack finite-quotient-topology-v0 --require-any
python3 scripts/query-foundational-resources.py horizon-frontier --pack finite-specialization-order-v0 --require-any
```

Expected resource boundary: finite topological tables, covers, maps,
preimages, quotient fibers, and specialization orders validate; scoped
Bool/CNF and QF_UF/Alethe contradictions stay checked evidence; arbitrary
topology theorems remain explicit Lean/theorem horizons.

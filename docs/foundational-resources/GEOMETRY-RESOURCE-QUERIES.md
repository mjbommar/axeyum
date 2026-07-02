# Geometry Resource Consumer Queries

This guide turns the finite geometry rows in the foundational-resource JSON
contract into copyable downstream queries. It is a consumer-discovery layer,
not a new proof route and not a synthetic-geometry theorem claim.

Use it when a learner page, catalog, solver contributor, or sibling resource
wants to ask:

```text
Which checked geometry packs match this finite geometry family and proof route?
```

The current geometry surface is intentionally finite and exact-rational:
coordinate arithmetic, midpoint/distance replay, line incidence, rigid
configuration distances, affine/orientation arithmetic, circle rows, inversion
rows, and cyclic-quadrilateral shadows. General synthetic, projective,
differential, global, and higher-degree algebraic geometry theorems remain in
the proof-horizon lane.

## Query Shape

Start with the field summary:

```sh
python3 scripts/query-foundational-resources.py fields \
  --field geometry \
  --route Farkas \
  --require-any
```

Then drill into bridge concepts or checked rows:

```sh
python3 scripts/query-foundational-resources.py packs \
  --concept <bridge_concept_id> \
  --route Farkas \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --concept <bridge_concept_id> \
  --route Farkas \
  --proof-status checked \
  --require-any
```

Use `packs` for a catalog row or pack path. Use `checks` when the consumer
needs concrete checked rows to display.

## Geometry Query Families

| Geometry Family | Concept Filter | Route Filter | Start Query |
|---|---|---|---|
| Coordinate, incidence, rigid, affine, and orientation replay | `bridge_coordinate_orientation_geometry` | `Farkas` | `checks --concept bridge_coordinate_orientation_geometry --route Farkas --proof-status checked` |
| Circle, inversion, and cyclic-configuration replay | `bridge_finite_circle_inversion_cyclic_replay` | `Farkas` | `checks --concept bridge_finite_circle_inversion_cyclic_replay --route Farkas --proof-status checked` |
| All finite geometry checks | field `geometry` | `Farkas` | `checks --field geometry --route Farkas --proof-status checked` |
| Circle-specific display rows | pack `finite-circle-geometry-v0` | `Farkas` | `checks --pack finite-circle-geometry-v0 --route Farkas --proof-status checked`; `horizon-frontier --text "circle geometry"` |
| Inversion-specific display rows | pack `finite-inversion-geometry-v0` | `Farkas` | `checks --pack finite-inversion-geometry-v0 --route Farkas --proof-status checked` |
| Cyclic/Ptolemy display rows | pack `finite-cyclic-geometry-v0` | `Farkas` | `checks --pack finite-cyclic-geometry-v0 --route Farkas --proof-status checked` |

## Copyable Examples

List all promoted finite geometry packs:

```sh
python3 scripts/query-foundational-resources.py packs \
  --field geometry \
  --route Farkas \
  --require-any
```

Display all checked finite geometry rows:

```sh
python3 scripts/query-foundational-resources.py checks \
  --field geometry \
  --route Farkas \
  --proof-status checked \
  --require-any
```

List coordinate, incidence, rigid, affine, and orientation packs through their
shared bridge concept:

```sh
python3 scripts/query-foundational-resources.py packs \
  --concept bridge_coordinate_orientation_geometry \
  --route Farkas \
  --require-any
```

Display their checked rows:

```sh
python3 scripts/query-foundational-resources.py checks \
  --concept bridge_coordinate_orientation_geometry \
  --route Farkas \
  --proof-status checked \
  --require-any
```

List circle, inversion, and cyclic-configuration packs:

```sh
python3 scripts/query-foundational-resources.py packs \
  --concept bridge_finite_circle_inversion_cyclic_replay \
  --route Farkas \
  --require-any
```

Display checked circle, inversion, and cyclic rows:

```sh
python3 scripts/query-foundational-resources.py checks \
  --concept bridge_finite_circle_inversion_cyclic_replay \
  --route Farkas \
  --proof-status checked \
  --require-any
```

For focused UI cards, query individual packs:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack finite-circle-geometry-v0 \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py horizon-frontier \
  --text "circle geometry" \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-circle-geometry-v0 \
  --proof-status lean-horizon \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-circle-geometry-v0 \
  --route Farkas \
  --proof-status checked \
  --text radius \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-circle-geometry-v0 \
  --route Farkas \
  --proof-status checked \
  --text intersection \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-inversion-geometry-v0 \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-cyclic-geometry-v0 \
  --route Farkas \
  --proof-status checked \
  --require-any
```

## Current Boundary

These queries prove discoverability of finite checked geometry rows, not
theorem coverage. They can support a catalog, a learner page, a route-specific
regression search, or a sibling resource that wants geometry examples by
finite object family.

They do not prove:

- synthetic or projective geometry theorem schemas;
- arbitrary circle, inversion, cyclic-quadrilateral, angle, or Ptolemy
  theorems;
- differential, global, algebraic, or higher-dimensional geometry;
- numerical robustness or floating-point geometric predicates;
- benchmark performance, PAR-2, or Z3/cvc5 parity.

Those claims need new proof-horizon rows, theorem-prover reconstruction, or
benchmark artifacts before they can graduate.

# Finite Quotient Topology Checks

Audience: learners, educators, topology contributors, set-theory contributors,
and solver contributors who need a tiny quotient-space resource.

This pack checks the finite definition of a quotient topology:

```text
V is open in X/~  iff  q^{-1}(V) is open in X
```

The checked slice is finite replay plus source-linked QF_UF/Alethe
contradictions for a false fiber-representative claim and a false
quotient-open claim.

## Rows

- `quotient-map-fiber-witness`: recompute quotient-map fibers and the
  same-fiber equivalence relation.
- `quotient-topology-witness`: enumerate all quotient subsets and keep exactly
  those whose preimages are open.
- `saturated-open-image-witness`: replay one saturated open subset and its
  quotient-open image.
- `bad-fiber-representative-rejected`: reject the false claim that two source
  representatives in the same quotient fiber have distinct quotient images
  using checked QF_UF/Alethe evidence.
- `bad-quotient-open-rejected`: reject the false claim that `{r}` is open in
  the quotient topology using checked QF_UF/Alethe evidence.
- `general-quotient-topology-lean-horizon`: keep arbitrary quotient-space
  theorems under Lean horizon.

## Trust Boundary

The finite validator recomputes source topology axioms, quotient-map
surjectivity, fibers, same-fiber equivalence pairs, quotient-open subsets,
image/preimage tables, and saturation from the source data. The promoted bad
rows are accepted only because the fixed quotient-representative and
open-status contradictions have checked Alethe proofs. This pack does not
prove the quotient topology universal property, quotient-map theorem schemas,
compactness/connectedness preservation, or arbitrary quotient-space invariance
results.

## Validate

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-quotient-topology-v0
cargo test -p axeyum-solver --test math_resource_uf_routes finite_quotient_topology_bad_fiber_representative_emits_checked_alethe
cargo test -p axeyum-solver --test math_resource_uf_routes finite_quotient_topology_bad_open_emits_checked_alethe
```

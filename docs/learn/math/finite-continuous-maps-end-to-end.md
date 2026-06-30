# End To End: Finite Continuous Maps

This lesson follows one finite continuous-map resource from explicit topology
and function tables to continuity and homeomorphism replay. It uses
[finite-continuous-maps-v0](../../../artifacts/examples/math/finite-continuous-maps-v0/).

Concept rows:

- `curriculum_sets`, `curriculum_reals`, and
  `curriculum_sequences_and_limits` in the
  [math coverage dashboard](../../foundational-resources/generated/math-coverage.md)
- `field_topology`, `field_set_theory_and_foundations`, and
  `field_real_analysis` in the
  [Foundational Concept Atlas](../../../artifacts/ontology/foundational-concepts.json)
- `bridge_continuity_preimage` and
  `bridge_finite_topology_operator_homeomorphism` in the atlas bridge
  vocabulary.

## Claim Shape

| Check | Expected | Evidence Status |
|---|---|---|
| `finite-continuous-map-witness` | `sat` | replay-only |
| `open-preimage-witness` | `sat` | replay-only |
| `finite-homeomorphism-witness` | `sat` | replay-only |
| `bad-continuous-map-rejected` | `unsat` | checked |
| `bad-homeomorphism-claim-rejected` | `unsat` | checked |
| `general-continuous-map-lean-horizon` | `not-run` | lean-horizon |

Every checked row is finite function-table and open-set enumeration. The pack
does not prove continuous-image theorems, homeomorphism invariance, compactness
preservation, or connectedness preservation for arbitrary spaces.

## Encode Two Finite Topologies

The positive witness uses a two-point Sierpinski domain:

```text
X = {0,1}
open_X = {}, {1}, {0,1}
```

and a renamed two-point Sierpinski codomain:

```text
Y = {u,v}
open_Y = {}, {v}, {u,v}
```

The map is:

```text
f(0) = u
f(1) = v
```

The validator checks that both open-set families are valid finite topologies
and that the map is total on the domain.

## Replay Continuity By Open Preimages

Continuity is checked by recomputing the preimage of every codomain open set:

```text
preimage({}) = {}
preimage({v}) = {1}
preimage({u,v}) = {0,1}
```

Each preimage is open in the domain topology, so the finite map is continuous.

The named open-preimage row focuses on:

```text
preimage({v}) = {1}
```

and verifies that `{1}` is a domain-open set.

## Replay A Finite Homeomorphism

The same map is bijective:

```text
0 -> u
1 -> v
```

The inverse map is:

```text
u -> 0
v -> 1
```

The validator checks the forward map is continuous, then checks inverse
continuity by recomputing preimages in the opposite direction. For example,
the inverse preimage of the domain-open set `{1}` is:

```text
{v}
```

which is open in the codomain. This is a finite homeomorphism replay, not a
general theorem that homeomorphisms preserve topological invariants.

## Reject A False Continuity Claim

The negative continuity row keeps the same domain topology but changes the
codomain to the discrete topology:

```text
open_Y = {}, {u}, {v}, {u,v}
```

The same identity-shaped map is:

```text
0 -> u
1 -> v
```

The checker finds the failing open set:

```text
{u}
```

with preimage:

```text
preimage({u}) = {0}
```

Since `{0}` is not open in the Sierpinski domain, the continuity claim is
rejected.

## Reject A False Homeomorphism Claim

The false homeomorphism row uses the same Sierpinski-to-discrete data. Even
though the map is bijective, the validator rejects the homeomorphism claim
because the forward map is not continuous:

```text
preimage({u}) = {0}
{0} is not domain-open
```

This is the useful trust pattern: a bijection is not automatically a
homeomorphism; the finite checker still has to validate continuity in both
directions.

## Name The Lean Horizon

The finite pack checks:

```text
finite topology axioms
total finite function table
open-set preimage enumeration
finite continuity
finite bijectivity
inverse continuity
bad continuity/homeomorphism refutations
```

The following remain proof-assistant targets:

```text
continuous images of compact spaces are compact
continuous images of connected spaces are connected
homeomorphisms preserve topological invariants
arbitrary-space continuity theorems
```

Those stay Lean-horizon until no-sorry artifacts or a dedicated certificate
route exist.

## Run It

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-continuous-maps-v0
```

Expected output:

```text
validated 1 foundational example pack(s)
```

## Trust Boundary

This lesson shows Axeyum's current finite continuous-map resource pattern:

```text
untrusted fast search -> map, open-preimage, homeomorphism, or counterexample row
trusted small checking -> finite function tables and open-set preimage lookup
remaining horizon -> arbitrary continuous-map and homeomorphism theorems
```

The graduation target is to encode finite topological continuity as
deterministic preimage-of-open-set enumeration, replay finite continuous-map
and homeomorphism witnesses through Axeyum model evaluation, and emit checked
counterexample evidence for rejected continuity and homeomorphism claims.

# End To End: Finite Connectedness

This lesson follows one finite connectedness resource from explicit topological
spaces to clopen-subset and open-separation replay. It uses
[finite-connectedness-v0](../../../artifacts/examples/math/finite-connectedness-v0/).

Concept rows:

- `curriculum_sets`, `curriculum_reals`, and
  `curriculum_sequences_and_limits` in the
  [math coverage dashboard](../../foundational-resources/generated/math-coverage.md)
- `field_topology`, `field_set_theory_and_foundations`, and
  `field_real_analysis` in the
  [Foundational Concept Atlas](../../../artifacts/ontology/foundational-concepts.json)

## Claim Shape

| Check | Expected | Evidence Status |
|---|---|---|
| `finite-connected-space-witness` | `sat` | replay-only |
| `finite-disconnected-separation-witness` | `sat` | replay-only |
| `clopen-subset-disconnection-witness` | `sat` | replay-only |
| `bad-connected-claim-rejected` | `unsat` | checked Bool/CNF DRAT/LRAT |
| `general-connectedness-lean-horizon` | `not-run` | lean-horizon |

Every checked row starts from finite enumeration over explicit open-set
families. The bad-connectedness row additionally isolates the final Boolean
contradiction in a DIMACS artifact and checks emitted DRAT/LRAT proof objects.
The pack does not prove connected-image theorems, interval connectedness,
path-connectedness, or general topological connectedness.

## Replay A Connected Finite Space

The connected witness uses the two-point Sierpinski topology:

```text
universe = {0,1}
open_sets = {}, {1}, {0,1}
```

The validator enumerates every finite subset:

```text
{}, {0}, {1}, {0,1}
```

and checks which subsets are both open and closed. The only clopen subsets are:

```text
{}, {0,1}
```

Since there is no non-trivial clopen subset, the row accepts the finite
connectedness witness.

## Replay An Open Separation

The disconnected witness uses the two-point discrete topology:

```text
universe = {a,b}
open_sets = {}, {a}, {b}, {a,b}
```

The listed open separation is:

```text
left = {a}
right = {b}
```

The checker confirms:

```text
left is nonempty
right is nonempty
left and right are open
left intersect right = {}
left union right = {a,b}
```

That is a concrete finite disconnection witness.

## Replay A Clopen Disconnection

The same discrete topology also has a non-trivial clopen subset:

```text
{a}
```

The checker verifies:

```text
{a} is open
complement({a}) = {b}
{b} is open
```

so `{a}` is closed as well as open. This clopen subset is another finite
witness of disconnection.

## Reject A False Connectedness Claim

The negative row claims that the two-point discrete topology is connected. The
checker rejects it by recomputing the counterexample:

```text
counterexample_clopen = {a}
```

Because `{a}` is nonempty, not the whole universe, and clopen, it refutes the
connectedness claim by finite enumeration.

The source-linked CNF artifact then checks the final Boolean contradiction:

```text
variable 1 = no non-trivial clopen subset exists
topology facts: not 1
false connectedness claim: 1
```

Axeyum emits a DRAT refutation, elaborates it to LRAT, and independently checks
both proof objects. The topology enumeration is still the source-level check;
the CNF proof checks the isolated Boolean contradiction.

## Name The Lean Horizon

The finite pack checks:

```text
finite topology axioms
all finite subset enumeration
clopen-subset replay
open-separation replay
bad connectedness refutation
```

The following remain proof-assistant targets:

```text
continuous images of connected spaces
intervals in R are connected
path-connected spaces are connected
connected components in arbitrary spaces
```

Those stay Lean-horizon until no-sorry artifacts or a dedicated certificate
route exist.

## Run It

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-connectedness-v0
cargo test -p axeyum-cnf --test math_resource_boolean_routes finite_connectedness_bad_connected_claim_emits_checked_drat_and_lrat
```

Expected output:

```text
validated 1 foundational example pack(s)
```

## Trust Boundary

This lesson shows Axeyum's current finite connectedness resource pattern:

```text
untrusted fast search -> connectedness, separation, clopen-subset, or CNF row
trusted small checking -> finite subset enumeration, open-set lookup, DRAT/LRAT checks
remaining horizon -> general connectedness theorems
```

The graduation target is to encode finite connectedness as deterministic
clopen-subset and open-separation checks, replay finite witnesses through
Axeyum model evaluation, and emit checked Bool/CNF evidence for source-level
obvious rejected connectedness claims.

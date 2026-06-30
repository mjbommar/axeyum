# End To End: Finite Compactness

This lesson follows one finite compactness resource from explicit set-family
data to open-cover and finite-intersection replay. It uses
[finite-compactness-v0](../../../artifacts/examples/math/finite-compactness-v0/).

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
| `finite-open-cover-subcover` | `sat` | replay-only |
| `minimal-subcover-size-witness` | `sat` | checked |
| `finite-intersection-family-witness` | `sat` | replay-only |
| `bad-open-cover-rejected` | `unsat` | checked |
| `general-compactness-lean-horizon` | `not-run` | lean-horizon |

Every checked row is finite set enumeration over an explicit topology. The pack
also checks the bad-cover row with a DRAT/LRAT certificate for the final
missing-point Boolean contradiction. It does not prove arbitrary topological
compactness, Heine-Borel, or the general finite-intersection-property theorem.

## Encode A Finite Topology

The witness uses a three-point universe:

```text
U = {a,b,c}
```

with the discrete topology:

```text
{}, {a}, {b}, {c}, {a,b}, {a,c}, {b,c}, {a,b,c}
```

Because every subset is open, the checker can focus on the cover,
minimality, and closed-family rows without hiding any topology side condition.

## Replay An Open Cover And Subcover

The listed open cover is:

```text
{a,b}, {b,c}, {a,c}
```

The validator checks that each set is open and recomputes the union:

```text
{a,b} union {b,c} union {a,c} = {a,b,c}
```

The listed subcover is:

```text
{a,b}, {b,c}
```

and the checker confirms:

```text
{a,b} union {b,c} = {a,b,c}
```

This is the finite witness shape behind "every open cover has a finite
subcover," but it is only a replay for this explicit cover.

## Check Minimal Subcover Size

The minimal-size row claims:

```text
min_size = 2
```

The trusted checker enumerates every one-set subfamily:

```text
{a,b}
{b,c}
{a,c}
```

and confirms that none covers all three points. It then checks that the listed
two-set subcover covers the universe. That gives checked finite enumeration
evidence for the minimality claim.

## Replay A Finite-Intersection Family

The closed-family row lists:

```text
{a,b}, {b,c}, {b}
```

In the discrete topology these sets are closed because their complements are
open. The checker recomputes finite intersections:

```text
{a,b} intersect {b,c} = {b}
{a,b} intersect {b} = {b}
{b,c} intersect {b} = {b}
{a,b} intersect {b,c} intersect {b} = {b}
```

So the family has the finite-intersection property and total intersection:

```text
{b}
```

This is a finite shadow of the compactness/finite-intersection-property
duality, not the general theorem.

## Reject A Bad Open Cover

The negative row claims that:

```text
{a}, {b}
```

is an open cover of `{a,b,c}`. The checker recomputes:

```text
{a} union {b} = {a,b}
```

and rejects the claim because `c` is missing.

The resource regression also checks the final contradiction as `Bool/CNF`:

```text
c_covered = false
c_covered = true
```

That `unsat` result must emit DRAT, elaborate to LRAT, and pass the independent
`check_drat` and `check_lrat` proof checkers.

## Name The Lean Horizon

The finite pack checks:

```text
finite topology axioms
open-cover union replay
subcover replay
minimal-subcover enumeration
closed-family finite intersections
bad-cover refutation
```

The following remain proof-assistant targets:

```text
arbitrary topological compactness
Heine-Borel
finite-intersection-property equivalence in general spaces
continuous image of compact sets
compactness in metric and uniform spaces
```

Those should stay Lean-horizon until there are no-sorry artifacts or an explicit
certificate route.

## Run It

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-compactness-v0
cargo test -p axeyum-cnf --test math_resource_boolean_routes finite_compactness_bad_open_cover_emits_checked_drat_and_lrat
```

Expected output:

```text
validated 1 foundational example pack(s)
```

## Trust Boundary

This lesson shows Axeyum's current finite compactness resource pattern:

```text
untrusted fast search -> cover, subcover, closed family, or bad-cover row
trusted small checking -> finite set unions, intersections, enumeration, and a DRAT/LRAT certificate for the bad-cover CNF
remaining horizon -> general compactness theorems
```

The graduation target is to encode finite open-cover, subcover, and
finite-intersection checks as deterministic finite-set obligations, then
promote only those Boolean refutations whose source-level finite-set meaning is
explicit.

# End To End: Counting And Pigeonhole

This lesson follows one finite counting resource from integer formulas to a
small pigeonhole refutation. It uses
[counting-v0](../../../artifacts/examples/math/counting-v0/).

Concept rows:

- `curriculum_counting` in the
  [math coverage dashboard](../../foundational-resources/generated/math-coverage.md)
- `bridge_finite_counting_replay` in the
  [Foundational Concept Atlas](../../../artifacts/ontology/foundational-concepts.json)
- `field_discrete_math` and `field_probability_theory` in the
  [Foundational Concept Atlas](../../../artifacts/ontology/foundational-concepts.json)

## Claim Shape

| Check | Expected | Evidence Status |
|---|---|---|
| `permutation-count-fixed` | `sat` | checked |
| `pascal-identity-fixed` | `sat` | checked |
| `pigeonhole-3-2-unsat` | `unsat` | checked |

Every row is fixed and finite. The pack does not prove general binomial
identities, recurrence schemas, asymptotic counting, probabilistic limit
theorems, or unbounded pigeonhole principles.

## Replay A Permutation Count

The first row checks a fixed number of length-`3` arrangements from `5`
distinct items:

```text
P(5, 3) = 5! / (5 - 3)!
        = 5! / 2!
        = 5 * 4 * 3
        = 60
```

The witness records:

```text
n = 5
k = 3
expected = 60
```

The validator recomputes the factorial expression exactly. It does not trust
the submitted `expected` field.

## Replay Pascal's Identity At One Point

The second row checks Pascal's identity at a single point:

```text
n = 6
k = 3
C(6, 3) = C(5, 2) + C(5, 3)
```

The exact counts are:

```text
20 = 10 + 10
```

This is a checked finite arithmetic row. It is not a proof of Pascal's identity
for all `n` and `k`.

## Refute A Tiny Pigeonhole Claim

The `unsat` row asks whether there is an injective placement of three pigeons
into two holes:

```text
pigeons = 3
holes = 2
```

A placement is a function from pigeons to holes. With two holes and three
pigeons, there are:

```text
2^3 = 8
```

possible placements. The validator enumerates all eight and confirms that
every placement has a collision, so no injective placement exists.

The same row also has a source DIMACS artifact:

```text
artifacts/examples/math/counting-v0/cnf/pigeonhole-3-2.cnf
```

The Boolean proof-route regression parses that artifact, emits a DRAT
refutation, elaborates it to LRAT, and checks both proof objects:

```sh
cargo test -p axeyum-cnf --test math_resource_boolean_routes counting_pigeonhole_3_2_emits_checked_drat_and_lrat
```

## Why This Matters

Counting is one of the smallest places where Axeyum's trust story splits into
two useful routes:

```text
finite arithmetic rows -> exact replay
finite impossibility rows -> enumeration plus checked CNF/DRAT/LRAT
```

The current pigeonhole evidence includes both checked finite enumeration and a
checked CNF proof-object route. That gives two independent views of the same
finite impossibility: direct replay of all placements, and a smaller
certificate checked against the DIMACS formula.
The shared `bridge_finite_counting_replay` row is the atlas vocabulary for this
pattern across permutation counts, Pascal rows, pigeonhole proofs,
double-counting tables, coefficient extraction, finite orbit counts, and exact
finite statistical tail counts. It deliberately stops at fixed finite
instances; asymptotic counting and unbounded combinatorial theorems remain
proof-horizon work.

## Run It

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/counting-v0
cargo test -p axeyum-cnf --test math_resource_boolean_routes counting_pigeonhole_3_2_emits_checked_drat_and_lrat
```

## Trust Boundary

The validator checks factorial, permutation, and binomial counts using exact
integer arithmetic. For the pigeonhole row, it enumerates the fixed finite
function space and checks injectivity directly. The Boolean route test checks
the generated DRAT and elaborated LRAT certificates for the source CNF.
General combinatorics, asymptotics, and unbounded pigeonhole theorems remain
future Lean-horizon work.

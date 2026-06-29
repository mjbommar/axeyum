# End To End: Counting And Pigeonhole

This lesson follows one finite counting resource from integer formulas to a
small pigeonhole refutation. It uses
[counting-v0](../../../artifacts/examples/math/counting-v0/).

Concept rows:

- `curriculum_counting` in the
  [math coverage dashboard](../../foundational-resources/generated/math-coverage.md)
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
theorems, or a certificate-producing pigeonhole SAT proof yet.

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

## Why This Matters

Counting is one of the smallest places where Axeyum's trust story splits into
two useful routes:

```text
finite arithmetic rows -> exact replay
finite impossibility rows -> enumeration now, CNF/LRAT later
```

The current pigeonhole evidence is checked finite enumeration. The graduation
route is to emit deterministic CNF and check an LRAT or DRAT proof object, so
the impossibility can be verified by a smaller proof checker instead of by
enumerating all placements.

## Run It

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/counting-v0
```

## Trust Boundary

The validator checks factorial, permutation, and binomial counts using exact
integer arithmetic. For the pigeonhole row, it enumerates the fixed finite
function space and checks injectivity directly. General combinatorics and
proof-producing SAT certificates remain future proof-route work.

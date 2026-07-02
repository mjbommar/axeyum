# End To End: Bounded Monotone Sequence

This lesson follows one bounded sequence resource from exact finite-prefix
replay to replay-only bad source rows and separate checked false upper-bound
and tail-gap proof rows. It uses the
[bounded-monotone-sequence-v0](../../../artifacts/examples/math/bounded-monotone-sequence-v0/)
pack.

Concept rows:

- `curriculum_sequences_and_limits` and `curriculum_reals` in the
  [math coverage dashboard](../../foundational-resources/generated/math-coverage.md)
- `field_real_analysis` and `field_topology` in the
  [Foundational Concept Atlas](../../../artifacts/ontology/foundational-concepts.json)
- `bridge_bounded_epsilon_delta_shadow` and `family_exact_rational_farkas` in
  the atlas bridge/example-family vocabulary.

## Claim Shape

| Check | Expected | Evidence Status |
|---|---|---|
| `monotone-upper-bound-prefix` | `sat` | replay-only |
| `finite-prefix-supremum` | `sat` | replay-only |
| `tail-gap-below-epsilon` | `sat` | replay-only |
| `bad-upper-bound-rejected` | `unsat` | replay-only |
| `qf-lra-bad-upper-bound` | `unsat` | checked QF_LRA/Farkas |
| `bad-tail-gap-rejected` | `unsat` | replay-only |
| `qf-lra-bad-tail-gap` | `unsat` | checked QF_LRA/Farkas |
| `monotone-convergence-lean-horizon` | `not-run` | Lean horizon |

The finite rows check only listed sequence values, listed inequalities, and
one finite tail. They do not prove the monotone convergence theorem.

## Encode

The sequence is:

```text
a_n = n / (n + 1)
```

For the prefix `0..6`, encode exact rational values:

```text
0, 1/2, 2/3, 3/4, 4/5, 5/6, 6/7
```

The validator checks monotonicity and the displayed upper bound:

```text
a_i < a_{i+1}
a_i < 1
max(prefix) = 6/7
```

## Replay

For the finite tail `n = 4..8`, the checker recomputes the gap to the proposed
limit `1`:

```text
1 - a_4 = 1/5
1 - a_5 = 1/6
1 - a_6 = 1/7
1 - a_7 = 1/8
1 - a_8 = 1/9
```

Since `1/5 < 1/4`, this finite tail satisfies the listed epsilon check.

## Check The Refutation

The malformed replay row keeps the source prefix fixed but claims:

```text
upper_bound = 5/6
```

Exact replay finds the offending value:

```text
a_6 = 6/7
```

The separate `qf-lra-bad-upper-bound` proof row owns the committed SMT-LIB
artifact
[`bad-upper-bound-farkas-conflict.smt2`](../../../artifacts/examples/math/bounded-monotone-sequence-v0/smt2/bad-upper-bound-farkas-conflict.smt2)
checks only the final exact-rational contradiction:

```text
6/7 <= 5/6
```

The solver search is untrusted. The accepted evidence is rechecked
`UnsatFarkas` arithmetic over the explicit proof row's source artifact.

## Check The Tail-Gap Refutation

The second malformed replay row claims the finite tail starting at `n = 2` is
already within `epsilon = 1/4` of the proposed limit `1`.

Exact replay finds:

```text
a_2 = 2/3
1 - a_2 = 1/3
1/3 - 1/4 = 1/12
```

The separate `qf-lra-bad-tail-gap` proof row owns the committed SMT-LIB
artifact
[`bad-tail-gap-farkas-conflict.smt2`](../../../artifacts/examples/math/bounded-monotone-sequence-v0/smt2/bad-tail-gap-farkas-conflict.smt2)
checks only the final exact-rational contradiction:

```text
tail_excess = 1/12
tail_excess <= 0
```

As before, the solver search is not trusted. The accepted evidence is the
independently rechecked `UnsatFarkas` certificate over the explicit proof row's
source artifact.

## Run It

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/bounded-monotone-sequence-v0
cargo test -p axeyum-solver --test math_resource_lra_routes bounded_monotone_sequence_bad_
```

Expected validator output:

```text
validated 1 foundational example pack(s)
```

## Trust Boundary

```text
untrusted fast search -> candidate prefix, tail, or Farkas certificate
trusted small checking -> exact rational sequence replay and checked QF_LRA proof rows
remaining horizon -> monotone convergence, completeness, compactness, quantified tails
```

Use this page after
[End To End: Sequence And Limit Shadows](sequence-limit-shadow-end-to-end.md)
when the goal is to keep finite monotone-prefix evidence separate from the
general convergence theorem.

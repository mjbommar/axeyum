# Monotone Convergence Theorem Boundary

This page separates the finite bounded-monotone sequence resources Axeyum can
check today from the general monotone convergence theorem over the real
numbers.

The current resource is a concrete finite shadow:

```text
a_n = n / (n + 1)
prefix = 0, 1/2, 2/3, 3/4, 4/5, 5/6, 6/7
finite tail = n = 4..8
candidate limit = 1
epsilon = 1/4
```

It is useful evidence for a small example. It is not a theorem that every
bounded monotone real sequence converges, and it is not a proof that the limit
is the supremum for an arbitrary sequence.

## Current Resource

Primary pack:

- [bounded-monotone-sequence-v0](../../../artifacts/examples/math/bounded-monotone-sequence-v0/)

Concept rows:

- `curriculum_sequences_and_limits`
- `curriculum_reals`
- `field_real_analysis`
- `field_topology`
- `bridge_bounded_epsilon_delta_shadow`

Proof routes:

- exact finite replay for the listed sequence prefix and listed tail;
- QF_LRA/Farkas for the isolated false upper-bound and false tail-gap
  contradictions;
- Lean horizon for the theorem statement.

## What Is Checked Today

| Row | What Axeyum Checks | Evidence Status |
|---|---|---|
| `monotone-upper-bound-prefix` | adjacent strict inequalities and the listed upper bound `1` over the finite prefix | replay-only |
| `finite-prefix-supremum` | the displayed finite prefix maximum is `6/7` at index `6` | replay-only |
| `tail-gap-below-epsilon` | the listed tail `n=4..8` has maximum gap `1/5 < 1/4` to the candidate limit `1` | replay-only |
| `bad-upper-bound-rejected` | exact replay finds `a_6 = 6/7`, contradicting the malformed upper bound `5/6` | replay-only |
| `qf-lra-bad-upper-bound` | the fixed rational conflict `6/7 <= 5/6` is unsatisfiable | checked QF_LRA/Farkas |
| `bad-tail-gap-rejected` | exact replay finds `a_2 = 2/3`, gap `1/3`, and excess `1/12` over `epsilon=1/4` | replay-only |
| `qf-lra-bad-tail-gap` | the fixed rational conflict `tail_excess = 1/12` and `tail_excess <= 0` is unsatisfiable | checked QF_LRA/Farkas |
| `monotone-convergence-lean-horizon` | the general monotone convergence theorem is explicitly outside current finite evidence | Lean horizon |

The checked rows are deliberately small. They trust the fixed rational
contradiction after replay has computed the witness value. They do not trust
solver search as theorem evidence.

## What Is Not Proved Yet

The current pack does not prove:

- every bounded monotone real sequence converges;
- convergence to the least upper bound or greatest lower bound;
- least-upper-bound completeness of the real numbers;
- Cauchy completeness or equivalence between completeness principles;
- a quantified epsilon-N tail statement for arbitrary monotone sequences;
- Bolzano-Weierstrass, Heine-Borel, compactness, or limit-point theorems;
- floating-point or numerical convergence claims.

Those are proof-assistant targets. The finite pack can be cited as an example
inside a theorem page, but not as evidence that the theorem has been proved.

## Query The Boundary

From the repository root, find the theorem boundary and its finite shadow:

```sh
python3 scripts/query-foundational-resources.py horizon-frontier \
  --text monotone \
  --require-any
```

Find the explicit Lean-horizon row:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack bounded-monotone-sequence-v0 \
  --proof-status lean-horizon \
  --require-any
```

Find the checked rational contradictions:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack bounded-monotone-sequence-v0 \
  --route Farkas \
  --proof-status checked \
  --require-any
```

Or drill into the two concrete bad rows:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack bounded-monotone-sequence-v0 \
  --route Farkas \
  --proof-status checked \
  --text qf-lra-bad-upper-bound \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack bounded-monotone-sequence-v0 \
  --route Farkas \
  --proof-status checked \
  --text qf-lra-bad-tail-gap \
  --require-any
```

## Graduation Criteria

A monotone convergence theorem resource should graduate only after these
artifacts exist:

1. A Lean theorem statement for bounded monotone real sequences, including the
   ordered-field, supremum, sequence, and convergence hypotheses.
2. A proof that checks without `sorry` and records the imported axioms.
3. A clear link from the finite pack to the theorem as an example, not as proof
   of the theorem.
4. Separate labels for finite replay, checked QF_LRA/Farkas contradictions,
   and theorem-level proof rows.
5. Consumer queries that keep the theorem row out of SMT, benchmark, and
   solver-parity summaries.

## Trust Boundary

```text
untrusted fast search -> candidate prefix, finite tail, or certificate
trusted small checking -> exact rational replay and checked QF_LRA/Farkas rows
remaining horizon -> quantified monotone convergence and real completeness
```

Read this after
[End To End: Bounded Monotone Sequence](bounded-monotone-sequence-end-to-end.md)
for the focused pack trace, and with
[Real Completeness Theorem Boundary](real-completeness-theorem-boundary.md) for
the broader least-upper-bound and Cauchy-completeness dependencies.

## Validation

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/bounded-monotone-sequence-v0
python3 scripts/query-foundational-resources.py horizon-frontier --text monotone --require-any
python3 scripts/query-foundational-resources.py checks --pack bounded-monotone-sequence-v0 --proof-status lean-horizon --require-any
python3 scripts/query-foundational-resources.py checks --pack bounded-monotone-sequence-v0 --route Farkas --proof-status checked --require-any
```

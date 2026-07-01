# Finite SDP Checks

This lesson follows
[finite-sdp-v0](../../../artifacts/examples/math/finite-sdp-v0/) from a tiny
two-by-two SDP witness through exact matrix replay and checked Farkas evidence.
It is a finite primal/dual certificate story, not a general SDP duality theorem.

## Concept

A semidefinite program optimizes a linear objective over symmetric matrices
subject to linear constraints and a positive-semidefinite constraint. The
theorem-level story includes weak duality, strong duality, Slater conditions,
and KKT-style complementary slackness.

The resource starts smaller. It fixes:

```text
C = [[1, 0],
     [0, 2]]

minimize <C, X>
subject to <I, X> = 1
           X is positive semidefinite
```

The primal witness is:

```text
X = [[1, 0],
     [0, 0]]
```

## What Gets Checked

The pack has seven rows:

| Row | Result | Evidence |
|---|---|---|
| `finite-sdp-primal-psd-replay` | `sat` | replay-only |
| `finite-sdp-objective-replay` | `sat` | replay-only |
| `finite-sdp-dual-slack-replay` | `sat` | replay-only |
| `bad-sdp-objective-rejected` | `unsat` | checked QF_LRA/Farkas |
| `bad-sdp-duality-gap-rejected` | `unsat` | checked QF_LRA/Farkas |
| `bad-sdp-slack-entry-rejected` | `unsat` | checked QF_LRA/Farkas |
| `general-sdp-duality-lean-horizon` | `not-run` | Lean horizon |

The replay rows use exact rational arithmetic and two-by-two matrix arithmetic.
They do not use floating-point eigenvalue approximations.

## PSD Replay

For a symmetric two-by-two matrix

```text
[[a, b],
 [b, c]]
```

the validator checks positive semidefiniteness by principal minors:

```text
a >= 0
c >= 0
ac - b^2 >= 0
```

For the listed primal matrix, those minors are:

```text
1, 0, 0
```

So the exact finite row accepts the listed `X`.

## Objective Replay

The validator recomputes the trace constraint and objective:

```text
<I, X> = 1
<C, X> = 1
```

This is the small trusted part. A search procedure can propose the matrix; the
resource validator independently checks the matrix arithmetic.

## Dual Slack Replay

The dual witness is `y = 1`. The validator recomputes:

```text
S = C - yI
  = [[0, 0],
     [0, 1]]
```

The slack principal minors are:

```text
0, 1, 0
```

The dual objective is `y = 1`, so the primal-dual gap is:

```text
<C, X> - y = 1 - 1 = 0
```

## Bad Objective Row

The malformed row changes only the claimed objective:

```text
claimed objective = 0
replayed objective = 1
objective error = 1
```

The source SMT-LIB artifact fixes the objective error as `1` and also claims it
is zero:

```smt2
(set-logic QF_LRA)
(declare-const objective_error Real)
(assert (= objective_error 1))
(assert (= objective_error 0))
(check-sat)
```

Axeyum parses that source row, emits `UnsatFarkas` evidence, and independently
checks the certificate.

## Bad Duality-Gap Row

The dual replay computes:

```text
primal objective = 1
dual objective = 1
duality gap = 0
```

The malformed row claims the same witness has gap `1/2`, leaving exact error
`1/2`.

The source SMT-LIB artifact fixes that gap error and also claims it is zero:

```smt2
(set-logic QF_LRA)
(declare-const gap_error Real)
(assert (= gap_error (/ 1 2)))
(assert (= gap_error 0))
(check-sat)
```

The Farkas route checks this final contradiction after the pack validator has
replayed the primal/dual arithmetic.

## Bad Slack-Entry Row

The same dual replay computes:

```text
S = [[0, 0],
     [0, 1]]
```

The malformed row claims the bottom-right entry is `1/2`. The source SMT-LIB
artifact fixes the replayed entry as `1` and the claimed entry as `1/2`, and
the Farkas route checks that exact equality conflict.

## What This Does Not Prove

The pack does not prove general SDP weak duality, strong duality, Slater
conditions, constraint qualifications, KKT sufficiency, or convergence of SDP
algorithms.

Those are named in the Lean-horizon row so the boundary is visible:

```text
finite two-by-two SDP replay: checked now
general SDP theory: future Lean reconstruction
```

## Run It

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-sdp-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_sdp_bad_
```

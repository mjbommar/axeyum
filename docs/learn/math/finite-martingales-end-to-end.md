# End To End: Finite Martingales

This lesson follows one finite martingale resource from atom probabilities and
filtration partitions to martingale equalities, square-submartingale replay, and
bounded stopping. It uses
[finite-martingales-v0](../../../artifacts/examples/math/finite-martingales-v0/).

Concept rows:

- `curriculum_sets`, `curriculum_relations_and_functions`,
  `curriculum_rationals`, and `curriculum_counting` in the
  [math coverage dashboard](../../foundational-resources/generated/math-coverage.md)
- `field_probability_theory`, `field_measure_theory`, `field_statistics`,
  `field_real_analysis`, and `field_set_theory_and_foundations` in the
  [Foundational Concept Atlas](../../../artifacts/ontology/foundational-concepts.json)

## Claim Shape

| Check | Expected | Evidence Status |
|---|---|---|
| `finite-martingale-witness` | `sat` | replay-only |
| `square-submartingale-witness` | `sat` | replay-only |
| `bounded-stopping-replay` | `sat` | replay-only |
| `bad-stopped-expectation-rejected` | `unsat` | replay-only |
| `qf-lra-bad-stopped-expectation` | `unsat` | checked |
| `bad-martingale-rejected` | `unsat` | replay-only |
| `qf-lra-bad-martingale` | `unsat` | checked |
| `general-martingale-lean-horizon` | `not-run` | lean-horizon |

Every replay row is exact finite rational arithmetic over normalized atom
tables and time-indexed partitions. The checked `qf-lra-*` rows isolate the
final scalar contradictions and require Farkas evidence. The pack does not
prove general martingale convergence, optional stopping, Doob inequalities,
stochastic integration, or continuous-time process theory.

## Replay The Finite Walk

The probability space is the two-step fair walk:

```text
P(uu) = 1/4
P(ud) = 1/4
P(du) = 1/4
P(dd) = 1/4
```

The filtration is a time-indexed sequence of partitions:

```text
F0 = {uu, ud, du, dd}
F1 = {uu, ud}, {du, dd}
F2 = {uu}, {ud}, {du}, {dd}
```

The process values are:

```text
M0 = 0

M1(uu) = 1
M1(ud) = 1
M1(du) = -1
M1(dd) = -1

M2(uu) = 2
M2(ud) = 0
M2(du) = 0
M2(dd) = -2
```

The validator first checks that each filtration level is a partition and that
the process is adapted: `M0` is constant on the `F0` block, `M1` is constant on
each `F1` block, and `M2` is constant on each singleton `F2` block.

## Replay Martingale Equalities

The first martingale check averages the time-1 values over the single time-0
block:

```text
CE_F0_M1 = (1 + 1 - 1 - 1) / 4
         = 0
         = M0
```

The next check averages time-2 values over each time-1 information block:

```text
CE_F1_M2(up) = (2 + 0) / 2
             = 1
             = M1 on {uu, ud}

CE_F1_M2(down) = (0 - 2) / 2
               = -1
               = M1 on {du, dd}
```

Those finite conditional-expectation equalities are the martingale witness.

## Replay The Square Submartingale

The square process has values:

```text
M0^2 = 0
M1^2 = 1 on all atoms
M2^2(uu) = 4
M2^2(ud) = 0
M2^2(du) = 0
M2^2(dd) = 4
```

The checker recomputes conditional square expectations:

```text
CE_F0_M1_squared = 1 >= M0^2
CE_F1_M2_squared(up) = (4 + 0) / 2 = 2 >= 1
CE_F1_M2_squared(down) = (0 + 4) / 2 = 2 >= 1
```

That is replay-only evidence that `M_t^2` is a finite submartingale for this
walk.

## Replay Bounded Stopping

The stopping time is first hit of `+1`, capped at time `2`:

```text
tau(uu) = 1
tau(ud) = 1
tau(du) = 2
tau(dd) = 2
```

The checker verifies stopping-time measurability against the filtration:

```text
{tau <= 1} = {uu, ud}, an F1 block
{tau <= 2} = {uu, ud, du, dd}, the whole space
```

The stopped values are:

```text
M_tau(uu) = 1
M_tau(ud) = 1
M_tau(du) = 0
M_tau(dd) = -2
```

The stopped expectation is:

```text
E[M_tau] = 1*(1/4) + 1*(1/4) + 0*(1/4) - 2*(1/4)
         = 0
         = E[M0]
```

This is a bounded finite replay row, not a proof of general optional stopping.

## Reject A False Stopped Expectation

The negative stopped-expectation row keeps the same bounded stopping replay but
claims:

```text
E[M_tau] = 1/2
```

The checker recomputes:

```text
E[M_tau] = 0
```

That replay row is not the proof object. The separate checked row
`qf-lra-bad-stopped-expectation` checks the final contradiction as `QF_LRA`:

```text
4*stopped_expectation = 0
stopped_expectation = 1/2
```

That `unsat` result must carry `Evidence::UnsatFarkas` and pass the
independent certificate check.

## Reject A False Martingale Claim

The negative row changes the terminal up-up value:

```text
bad M2(uu) = 3
bad M2(ud) = 0
```

The checker recomputes the up-block conditional expectation:

```text
bad CE_F1_M2(up) = (3 + 0) / 2
                 = 3/2
```

and rejects the martingale claim because:

```text
3/2 != 1
```

The candidate martingale table is untrusted; the small checker rebuilds the
conditional expectation from the atom table, filtration block, and terminal
values. The separate checked row `qf-lra-bad-martingale` isolates the scalar
contradiction:

```text
up_block_conditional_expectation = 3/2
up_block_conditional_expectation = 1
```

That second row, not the replay row, owns the Farkas proof-object check.

## Name The Lean Horizon

The finite pack checks:

```text
normalized finite atom probabilities
time-indexed filtration partitions
adapted process tables
finite martingale conditional-expectation equalities
finite square-submartingale inequalities
bounded stopping-time replay
bad stopped-expectation and martingale-table replay refutations
separate QF_LRA/Farkas proof rows for the isolated scalar conflicts
```

The following remain proof-assistant targets:

```text
general martingale convergence
optional stopping
Doob inequalities
stochastic integration
continuous-time martingales
```

Those stay Lean-horizon until no-sorry probability and stochastic-process
artifacts exist.

## Run It

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-martingales-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_martingales_bad_stopped_expectation_artifact_emits_checked_farkas
cargo test -p axeyum-solver --test math_resource_lra_routes finite_martingales_bad_conditional_expectation_emits_checked_farkas
```

Expected output:

```text
validated 1 foundational example pack(s)
```

## Trust Boundary

This lesson shows Axeyum's current finite martingale resource pattern:

```text
untrusted fast search -> filtration, process, stopping time, or counterexample row
trusted small checking -> exact partitions, rational conditional averages, and stopped sums
remaining horizon -> general martingale and stopping-time theory
```

The graduation target is to encode finite filtrations as time-indexed
partitions of probability atoms, replay finite adaptedness, martingale,
submartingale, and bounded stopping-time witnesses by exact rational model
evaluation, and emit checked counterexample evidence for rejected stopped-
expectation and martingale claims.

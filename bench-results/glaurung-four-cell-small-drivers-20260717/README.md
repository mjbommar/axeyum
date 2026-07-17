# Glaurung small-driver four-cell regime map

- Date: 2026-07-17
- Glaurung revision: `403a5c5c1f6c5152fef6cefd0d78c3eb90d3888f`
  (clean detached worktree)
- Axeyum revision: `4464dae2`
- Measurement schema: `glaurung-ordered-check-measurement-v2`
- Repetitions: five sequential fresh processes per driver
- Worker count: one

This artifact extends ADR-0215's topology-equivalent four-cell control from
DptfDevGen to the three small-formula drivers named by the reviewer follow-up.
Every authoritative occurrence times `{Z3, Axeyum} x {cold, warm}` in rotating
order. The warm cells share the same source ownership, serial sibling lease,
exact source-prefix LCP, and temporary-assumption partition.

All 44,825 ordered occurrences decide in all four cells, comprising 179,300
measured cell executions: five repetitions of 4,742 checks for vwififlt,
1,672 for IntcSST, and 2,551 for SurfacePen. There are zero nondecisions,
operational results, decided disagreements, replay failures, or one-shot
fallbacks. Work identity is fixed within each driver across all repetitions.

Ratios below are Z3 latency divided by Axeyum latency, so values greater than
one favor Axeyum. The scalar is the geometric mean of paired per-occurrence
ratios after collapsing each occurrence across five repetitions; it is not a
ratio of summed times.

| Driver | Checks/run | Warm created/retained | Z3/Axeyum cold (95% CI) | Run CV | Z3/Axeyum warm (95% CI) | Run CV | Result |
|---|---:|---:|---:|---:|---:|---:|---|
| vwififlt | 4,742 | 14 / 4,728 | 0.6185x [0.6061, 0.6313] | 0.3001% | 1.0030x [0.9731, 1.0350] | 0.6625% | warm parity; cold favors Z3 |
| IntcSST | 1,672 | 24 / 1,648 | 2.3703x [2.2719, 2.4744] | 0.5428% | 1.5315x [1.4512, 1.6167] | 1.3273% | cold and warm favor Axeyum |
| SurfacePen | 2,551 | 43 / 2,508 | 2.4901x [2.4073, 2.5763] | 0.7240% | 1.5584x [1.5069, 1.6096] | 1.6082% | cold and warm favor Axeyum |

Together with the committed DptfDevGen control, the fair warm map now contains
two Axeyum wins, one statistical tie, and one Z3 win:

| Driver | Z3/Axeyum warm (95% CI) | Result |
|---|---:|---|
| DptfDevGen | 0.7875x [0.6893, 0.8977] | favors Z3 |
| vwififlt | 1.0030x [0.9731, 1.0350] | parity |
| IntcSST | 1.5315x [1.4512, 1.6167] | favors Axeyum |
| SurfacePen | 1.5584x [1.5069, 1.6096] | favors Axeyum |

The data establish a real workload-dependent winning regime, but do not yet
identify its cause. In particular, the cold results split in the same sample:
IntcSST and SurfacePen favor Axeyum cold as well as warm, while vwififlt favors
Z3 cold. It would therefore be premature to name the boundary merely
"small-formula FFI cost" or "hard-formula solver cost." The next experiment
must join these paired timings to formula size, operator mix, CNF/AIG size,
SAT share, and reuse distribution before selecting a causal publication claim.

Each driver directory contains the machine-readable `report.json` and both
the explicit four-cell and compatibility two-cell CDF CSV/PNG outputs. The
reports contain exact driver hashes, configuration identity, trace paths,
outcome populations, confidence intervals, quantiles, and process variance.

Report SHA-256 values:

- `vwififlt/report.json`:
  `9ffa0d04cecfa2c4967a0034fff6c914e23e55846e1a45aa5e68a2d6e272dead`
- `intcsst/report.json`:
  `18b507dce33e3423e970f5e9951d4b2750487ca7a0c35f79b4f1814f29491657`
- `surfacepen/report.json`:
  `731f9c527c35469aff7af6c9e8356c18bb7a081c062ff2a6beb95c1e4084582a`

The 1.4 GiB raw restricted-driver traces are retained outside git at
`/nas4/data/workspace-infosec/.axeyum-fair-small-20260717.8SkLHB`. Glaurung's
independent structural validator accepted every trace before analysis.

This artifact supports a delimited performance result, not a blanket solver
speed claim. Neutral solvers, formula-feature attribution, a timeout-sensitive
marked workload, and authoritative finding parity remain publication gates.

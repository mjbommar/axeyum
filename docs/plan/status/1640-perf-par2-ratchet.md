# Lane: perf-par2-ratchet — make a solve-time regression fail a gate

<!-- plan-section: lane-status -->

**Landed** (`WIP`, perf-par2-ratchet, 2026-09-05). Recommendation 1 of the
[2026-09-05 SAT/SMT performance review](../../research/11-design-review/2026-09-05-sat-smt-performance-and-architecture-review.md),
first slice: **a timing regression is now RED.** Section 2.2 item 1 of that
review measured the hole — nothing in any gate failed when solve time regressed.
`progress_frontier.rs` ratcheted capability at a fixed budget, the parity ledger
ratchets decide count, the corpus sweep ratchets soundness, and
`summary.par2_mean_s` in the 72 `bench-results/baselines/` files was compared to
nothing.

The ratchet lives inside the existing frontier sweep: each family carries a
`TimingBaseline` (a few `N` pinned deep inside its frontier, a calibrated total,
a measured ceiling), read out of the curve the capability sweep already
produces, so it costs **zero extra solving** and is registered wherever
`progress_frontier` already is — the `frontier` step in `scripts/check.sh` and
the `frontier` recipe in the `justfile`, both now documented as running two
ratchets.

**It fires.** Demonstrated in a private snapshot (`scripts/lane-snapshot.sh`) by
putting a 25 ms stall in `nra_even_power_refutation` — every verdict correct,
`FRONTIER nra_degree = 40 (baseline 40)` still green — and the timing ratchet
failed with `TIMING REGRESSION [nra_degree]: pinned N=[10, 20, 30, 40] took
98.2 ms calibrated, over the committed ceiling of 23.0 ms`, suite exit 101. The
same snapshot with the stall removed: `TIMING nra_degree = 10.9 ms`, exit 0 —
and it passed at 1-minute load 25.1 having failed at load 13.8, so the verdict
tracks the code, not the box.

**It stays quiet under load.** The check is enforced only when
`machine.comparable` is true — the same flag the capability ratchet uses, and
mirrored as `timing.enforced` in each artifact. The committed regeneration sweep
demonstrates it: `nia_unsat` drifted 37 % mid-sweep, so its row reads
`"comparable": false`, `"enforced": false`, and its `TIMING` line says
`ADVISORY, not enforced on this run`, while the other four families asserted.

**Band, measured not guessed** (calibrated ms, `solve_ms / scale`), over eight
sweeps on s4 at 1-minute load 17.9-37.8 (`scale` 1.10x-2.03x, a 16-core box at
1-2.4x oversubscription):

| family | pins | sweeps | min / median / max | ceiling |
|---|---|---:|---|---:|
| `bv_reduction` | 12, 15, 18 | 8 | 959.9 / 1293.1 / 1509.5 | 2264.3 |
| `lia_cuts` | 3, 19, 20 | 8 | 238.6 / 341.9 / 393.1 | 589.6 |
| `string_bound` | 13, 25, 33 | 8 | 387.6 / 423.5 / 646.0 | 969.1 |
| `nra_degree` | 10, 20, 30, 40 | 8 | 6.5 / 11.2 / 15.3 | 23.0 |
| `nia_unsat` | 1, 2, 3, 4, 5 | 7 | 30.4 / 44.3 / 77.1 | 115.6 |

**What the next lane should know.**

- **Five sweeps were not enough on this box.** Sweeps six and seven each landed
  above the five-run maximum on the two cheap families. The band is now eight
  sweeps, and `TIMING_BASELINE_MIN_RUNS = 5` is a floor a test enforces rather
  than a count anyone may re-derive downward.
- **The band is wide because s4 was never idle.** Calibrated totals still spread
  1.6x-2.4x between the quietest and busiest sweep — the residual the proxy
  kernel does not compensate. **Re-measuring on an idle machine would tighten
  every ceiling** and is the cheapest available improvement to this gate's
  resolution; the recipe is in the methodology note.
- **`nia_unsat` and `nra_degree` have the least resolution**, because neither
  family has mid-priced instances (`nra_degree` is 1-4 ms per point;
  `nia_unsat` jumps from tens of ms at `N<=5` to ~2.7 s at `N>=6`). They still
  catch the order-of-magnitude failure their fast paths would cause.
- **A pre-existing flake was observed, not introduced.** In one sweep
  `nia_unsat` `N=1` — normally ~2 ms — did not return inside `budget + 1 s`, and
  the CAPABILITY ratchet failed with `frontier 0` against a baseline of 40. The
  two nonlinear families use `smtlib_unsat_sweep`, which has **no retry loop**,
  unlike `sweep`. Giving them the same `ATTEMPTS` retry is a small, separate fix.
- **Still not covered:** the 72 PAR-2 means under `bench-results/baselines/`.
  Extending the same calibrated-band scheme to `par2_mean_s` is the next slice.

<!-- plan-section: landed-changes -->

| 2026-09-05 | perf-par2-ratchet | Timing ratchet in `progress_frontier.rs`: pinned-`N` calibrated solve time per family against a measured ceiling, enforced on the `comparable` flag, registered in `check.sh` and the `justfile`; five baselines regenerated with a `"timing"` block. |

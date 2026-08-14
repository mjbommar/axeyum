# Lane: gates — the gates themselves, and what they can prove they examined

<!-- plan-section: lane-status -->

**Gate scope and the wall-clock reference frame (`WIP`, gates, 2026-08-14).**
Landed: cargo's mtime-based freshness could let `cargo clippy` **and**
`cargo test` pass over source they never compiled (measured: `cargo test` printed
"1 passed" for a test that must fail), so both now run through wrappers that
touch content whose hash changed and then report how many targets/tests they
actually examined; the divergence between `just check` (145 steps) and
`./scripts/check.sh` (89) is pinned in
`scripts/check-aggregate-scope.expected` and fails when it grows; and the
`progress_frontier` ratchets now calibrate the machine before and after each
sweep, scale the budget, and refuse to enforce (`NOT COMPARABLE`) or to raise a
baseline (`ADVISORY ONLY`) outside their bands — the stock fixed-budget gate
reported `bv_reduction = 29` against a baseline of 30 on this box's efficiency
cores, four runs out of five, a REGRESSION that never happened.

Next, in priority order: (1) `MAX_N = 40` has turned `nra_degree`, `nia_unsat`
and now `string_bound` into constants — three of five ratchets can no longer show
progress; (2) apply `scripts/check-source-freshness.sh` to the remaining cargo
entry points (`scripts/check-scope.sh`, the `bench-*` recipes) and to the
snapshot instruction lanes are given; (3) one authoritative step manifest for the
aggregate gate, with a wrapper column, so the 66 recorded differences can shrink
instead of only being prevented from growing.

<!-- plan-section: landed-changes -->

| 2026-08-14 | `fb1066709` | The workspace test gate's zero-test list capped and phrased as information (parser validated at 1191 tests / 34 binaries). |
| 2026-08-14 | `23bd018be` | `check.sh` stops claiming to mirror a recipe it does not; the claim was false for the life of the file. |
| 2026-08-14 | `585d4ac23` | Control 6: the step floor itself is exercised (20 controls). |
| 2026-08-14 | `fc1090126` | Frontier curves re-recorded with the machine, load, calibration and comparability that produced them. |
| 2026-08-14 | `4be94e45c` | Controls for the aggregate gate's own scope (18 checks). |
| 2026-08-14 | `952a3ae2b` | Calibration kernel corrected to track the workload (it under-reported the core-class slowdown by 60 %). |
| 2026-08-14 | `1bc24b326` | `progress_frontier` gains a measured reference frame: per-family calibration, scaled budget, `NOT COMPARABLE` / `ADVISORY ONLY`. |
| 2026-08-14 | `ec72fdf66` | `just check` vs `check.sh` divergence measured and pinned; the Lean axiom ledger now runs in both. |
| 2026-08-14 | `fa4676e33` | Clippy and the workspace test sweep prove what they examined; content-addressed source freshness; 14 negative controls. |

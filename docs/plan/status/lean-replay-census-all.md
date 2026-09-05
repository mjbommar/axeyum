# Replay census — every carrier the kernel builds

<!-- plan-section: lane-status -->

Lane: `lean-replay-census-all`. Item 2 of the Next Ten in
[`docs/math-department/14-lean-lang.md`](../../math-department/14-lean-lang.md):
*replay every proved theorem in pinned Lean, or name the reason*. Decision:
[ADR-1661](../../research/09-decisions/adr-1661-the-replay-census-covers-every-carrier-and-type-valued-theorems-are-a-named-class.md).
Predecessor: [ADR-0760](../../research/09-decisions/adr-0760-independent-replay-is-graded-per-declaration-by-name.md)
(lane `l0-s4-independent-replay`), which built the same census over `creal`
alone.

## Status

Done. Every carrier the kernel builds runs ADR-0760's per-declaration replay
census against the cross-check pin, `missing=0` enforced per carrier, and the
two non-representable classes are named member by member rather than counted.

## The measurement

Published as
[`artifacts/measurements/lean-replay-census-2026-09-05.md`](../../../artifacts/measurements/lean-replay-census-2026-09-05.md).
Measured 2026-09-05 at `3328d2a80` on `leanprover/lean4:v4.34.0-rc1`.
`real_lean_replay_census_all`: `20 passed; 0 failed` in 738.79 s, 17 Lean
invocations. `real_lean_replay_census`: `5 passed; 0 failed` in 104.18 s.
**No carrier was skipped and none is reported as "did not run".**

The sentence the chair asked for, read from the `everything` row and from no
other (the per-carrier rows NEST and cannot be summed):

> Of **4,478** proved declarations, pinned Lean's kernel accepts **4,394**;
> **50** are `Type`-valued theorems it refuses as theorems, and **34** are
> blocked behind one of those.

| carrier | population | representable | replayed | `Type`-valued | blocked | missing |
|---|---:|---:|---:|---:|---:|---:|
| `logic` | 99 | 99 | 99 | 0 | 0 | 0 |
| `axreal` | 129 | 129 | 129 | 0 | 0 | 0 |
| `nat` | 1,990 | 1,990 | 1,990 | 0 | 0 | 0 |
| `ipc_eval` | 2,003 | 2,003 | 2,003 | 0 | 0 | 0 |
| `list` | 2,021 | 2,021 | 2,021 | 0 | 0 | 0 |
| `ipc` | 2,040 | 2,040 | 2,040 | 0 | 0 | 0 |
| `string` | 2,086 | 2,086 | 2,086 | 0 | 0 | 0 |
| `int` | 2,391 | 2,391 | 2,391 | 0 | 0 | 0 |
| `characterization` | 2,427 | 2,427 | 2,427 | 0 | 0 | 0 |
| `rat` | 2,997 | 2,997 | 2,997 | 0 | 0 | 0 |
| `creal` | 3,617 | 3,542 | 3,542 | 49 | 26 | 0 |
| `arith_models` | 3,713 | 3,638 | 3,638 | 49 | 26 | 0 |
| `cpoint` | 3,766 | 3,691 | 3,691 | 49 | 26 | 0 |
| `complex` | 3,767 | 3,692 | 3,692 | 49 | 26 | 0 |
| `metric` | 3,863 | 3,788 | 3,788 | 49 | 26 | 0 |
| `rn` | 3,921 | 3,846 | 3,846 | 49 | 26 | 0 |
| `intspace` | 3,961 | 3,877 | 3,877 | 50 | 34 | 0 |
| **`everything`** | **4,478** | **4,394** | **4,394** | **50** | **34** | **0** |

## Findings

**1. Every `Prop`-valued theorem the kernel has proved is independently
admitted by Lean, under its own name.** Not by family, not by carrier count —
by membership of its own name in the constant set Lean's own kernel ended
holding.

**2. The 84 that are not are named, and 34 of them hang off five
declarations.** `CReal.hasDerivative_add`, `CReal.hasDerivative_neg`,
`CReal.uniformlyContinuousOn_restrict`, `CReal.uniformly_continuous_const`
and `CReal.uniformly_continuous_add` block 26 of the 34 between them. That
is what turns "publish the constructive analysis as a Lean library" (Next Ten
item 3) from an open-ended job into a scoped one.

**3. The `creal` floor had stopped ratcheting.** It was set at 1,900 on
2026-08-30 against a carrier of 2,045 declarations; the carrier holds 3,617
today, so the floor could have absorbed the silent loss of nearly half of it.
Raised to 3,350 — the ratchet working, not a lowering.

**4. The `missing` guard is sensitive to the losses that matter, and one
mutant showed exactly where its edge is.** Dropping a *leaf* export root is
killed (`missing=1`, naming `Subtype.mk_eta`); dropping a *non-leaf* root
survives, because the exporter emits the dependency closure and Lean still
ends up holding the name. Recorded in ADR-1661 as a limitation, not fixed:
the census claims "Lean's environment holds a constant of this name", and
that claim stays true in the surviving case.

**5. Not this lane's work, but re-measured on the way past:** the three Lean
gates `14-lean-lang.md` recorded as red on 2026-09-05 all exit 0 on a clean
tree at `3328d2a80`, fixed the same day by lane `lean-pin-gates`
([ADR-1660](../../research/09-decisions/adr-1660-there-are-two-lean-pins-and-every-claim-names-which-one-it-means.md)).
The row was updated to say so. `check-parity-freshness.py`'s Z3-ledger
failure was NOT re-measured and is not claimed either way.

## What did NOT run

**The suite's cost in DEBUG was not measured.** `scripts/check-lean-gate.sh`
runs registered suites as `cargo test -q -p … --test …`, i.e. unoptimized, and
every number in this file is from `--release`. A debug build of
`real_lean_replay_census_all` was queued on 2026-09-05 and sat 45 minutes in
the host-wide `cargo-serialized.sh` flock without starting (45 queued cargo
jobs at the time); it was cancelled rather than left to orphan. So this is
reported as **did not run**, not as "fine".

What is known rather than guessed: the already-registered
`real_lean_replay_census` runs ONE `creal` carrier in debug and was measured
at 240 s by ADR-0760, on a carrier that then held 2,045 declarations and now
holds 3,617. This suite has seven `creal`-superset carriers and ten cheap
ones. So the gate's runtime is expected to grow by tens of minutes, and that
is an **extrapolation from one debug data point**, not a measurement. Whoever
next runs `scripts/check-lean-gate.sh` end to end should read the real number
off it; if the cost is unacceptable, the lever is to `#[ignore]` the seven
constructive carriers and lower `CHECK_FLOOR` by exactly seven, which trades
gate time for exactly the carriers most worth checking.

`scripts/check-lean-gate.sh` itself was **not run end to end** by this lane
for the same reason. `CHECK_FLOOR` was raised by exactly the seventeen
invocations this suite makes, each of which was observed
(`AXEYUM-LEAN-CHECKED replay-census-all checked=1`, seventeen times, in one
run).

`gen-plan.py` was **not run**: this lane was told not to. `gen-plan.py
--check` exits 1 solely because of this new status file — verified by moving
it aside (exit 0) and putting it back.

## Where the census lives

- `crates/axeyum-lean-kernel/tests/support/replay_census.rs` — the classifier,
  the exporter call, the Lean invocation, `grade`, and `census_carrier`.
  Included by `#[path]` into both suites so they cannot drift.
- `crates/axeyum-lean-kernel/tests/real_lean_replay_census_all.rs` — one
  `#[test]` per carrier, the `BUILDERS` coverage table, and the two
  classifier controls that need no Lean.
- `crates/axeyum-lean-kernel/tests/real_lean_replay_census.rs` — the `creal`
  carrier, its flagship coverage pin, and the three mutation controls
  (wrong proof, wrong goal, no inheritance).
- `scripts/check-lean-gate.sh` — both suites registered; `CHECK_FLOOR`
  261 → 278.

<!-- plan-section: landed-changes -->

| 2026-09-05 | `defe0d742` | lane opened: status file |
| 2026-09-05 | `f3d8b3d95` | the census over every carrier: shared harness `tests/support/replay_census.rs`, new suite `real_lean_replay_census_all` (17 carriers, one `#[test]` each), carrier list derived from `src/lib.rs`'s re-export block, `creal` floor raised 1,900 -> 3,350, `check-lean-gate.sh` `CHECK_FLOOR` 261 -> 278 with the new suite registered |
| 2026-09-05 | (this commit) | `artifacts/measurements/lean-replay-census-2026-09-05.md`, ADR-1661, ADR index regenerated, and the four rows in `docs/math-department/14-lean-lang.md` this run moved |

# Lane: capability-assurance — the strand's own metric was unmeasurable

<!-- plan-section: lane-status -->

**Open queue, in the order I intend to clear it** (`WIP`,
capability-assurance, 2026-08-19). Detail per item in
[the lane note](../notes/99-capability-assurance.md).

1. **`hooks/pre-push` now runs real-Lean suites on every push.** It invokes
   `cargo test -p axeyum-lean-kernel` wholesale, and that package gained
   `real_lean_creal_carrier_kernel_replay` (~62 s) and
   `real_lean_wellfounded_elaborator_divergence` (~115 s, four Lean
   invocations). `scripts/check-lean-gate.sh` already owns those. Every push in
   the repository pays twice; the step was documented at 206-248 s.
2. **`docs/plan/status/103-creal-lean-divergence.md` is 3,029 bytes**, over the
   per-lane ceiling (ADR-0478). Its lane has finished, so
   `scripts/archive-plan-status.py --apply` can take it once it is clean.
3. **`PLAN.md` and `101-expect-axioms.md` publish 11 ledger guards where there
   are 10.** The eleventh sabotaged its own fixture, printed `Ran 0 tests`, and
   the old mutation classifier scored that as a kill — on the control over the
   axiom ledger, i.e. the axiom-freedom claim. The count is wrong in a
   generated view.
Items 4-6 (an uncovered guard in the transcription binder, the 404 GB
target-dir relocation, and registering a heavy-cargo suite with the mutation
harness) are in [the lane note](../notes/99-capability-assurance.md).

Cleared today: the axiom-freedom measurements are gated (nothing ran them),
`local-ci` has a PASS record with its freshness gate enforcing, ADR numbers are
checked against `origin/main`, and `lane-commit.sh` checks a pathspec both ways.

<!-- plan-section: landed-changes -->

| 2026-08-18 | `pending` | `scripts/cargo-serialized.sh`: heavy cargo now takes an flock and a memory ceiling, because "serialize" was prose and prose does not hold a lock (two dev boxes downed, one agent session OOM-killed). **`MemoryMax` alone does not bite** — it *is* applied (`memory.max` = 67108864) and a 400 MB allocation still succeeds by swapping, on a box whose 7 G of swap is 6 G full. With `MemorySwapMax=0` the same allocation is SIGKILLed by the cgroup (137), host untouched. `--self-check` proves it per host and discriminates: `AXEYUM_CARGO_SWAP=1G` flips it to `SURVIVED`, exit 1. |
| 2026-08-18 | `pending` | `local-ci.sh`, the declared authoritative gate for `main`, cannot run on any fleet host and never has (`cargo nextest` 101, `rustup run 1.88.0` 1, on s4/s5/s7). Now refuses to start rather than limp, `--record` leaves a tracked per-(sha,host) JSON, and `provision-fleet-host.sh` installs the prerequisites (`1.88.0` needs `--profile minimal`, else rustup fails on `miri`/`cranelift` inherited from the nightly profile). The record carries per-step TEST COUNTS and marks a step that exited 0 having run zero tests as `vacuous`. |

# Notes: gate-throughput

Detail moved out of [`../status/gate-throughput.md`](../status/gate-throughput.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

Two structural facts, both contradicting what every document said.
`scripts/cargo-serialized.sh` stopped being a serializer on 2026-08-18 — it is a
counting semaphore of `clamp(RAM/MEM, 1, 6)` slots, **5** here, bounding memory
with nothing bounding CPU. And **`hooks/pre-push`, `scripts/check.sh`, the
`justfile` and `scripts/local-ci.sh` called it zero times between them**; the
only callers in `scripts/` were `check-kernel-stack-envelope.sh` and the
mutation harness. Admitted concurrency was not 5, it was unbounded, and the
authoritative pre-merge gate was one more equal consumer.

**The obvious fix measured as doing nothing, which is the finding worth
keeping.** `nice 10` on lane work verified as applied all the way down to forked
grandchildren, and a controlled A/B with 27 competitors in both arms scored
**1.85x vs 1.82x — 1.01x**. Cause: `sched_autogroup_enabled=1` schedules per
session, so `nice` barely crosses a lane boundary. The cgroup `cpu` controller
does, and it was then applied at the **wrong level twice** — once under
`app.slice`, once under an implicit `axeyum.slice` created by the dash in
`axeyum-lane` — each time reading `cpu.weight = 10` back correctly while
ordering lane jobs against each other and nothing else.

Lane work now runs in `axeyumlane.slice` (no dash, a true sibling of a session
scope) at `CPUWeight=10`; the battery runs unweighted. Measured, identical
offered load, subject width 16: **1.89x → 1.11x inflation, 1.69x speedup**.

No step was dropped anywhere. The gating was examined and found already as tight
as it soundly can be — `axeyum-solver` depends on `axeyum-lean-kernel` under
`--features full`, so a kernel-only push is inside the build closure of both
always-on solver steps. The one filter that was too **loose** was widened:
`Cargo.lock` is not `*.toml`, so a dependency bump skipped the whole battery.

Decision: [ADR-0606](../../research/09-decisions/adr-0606-lane-work-yields-to-the-push-battery.md).
Measurement: [`../../research/11-design-review/2026-08-27-gate-throughput.md`](../../research/11-design-review/2026-08-27-gate-throughput.md).

Open, deliberately not done here: the `justfile`'s ~90 `check` recipes still
take no slot (only `check.sh` is wired); `sccache` is the sound version of
shared build artifacts and needs its own evaluation; and gating the always-on
solver steps on a derived reverse-dependency closure is a real but narrow win.

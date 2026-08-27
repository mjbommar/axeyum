# Lane: gate-throughput — the cargo semaphore was unwired, and `nice` measured as nothing

<!-- plan-section: lane-status -->

**Verification throughput was the binding constraint, and the cause was
scheduling rather than any gate** (`landed`, gate-throughput, 2026-08-27). The
`hooks/pre-push` battery went from ~250 s uncontended to **2,152 s / 2,654 s**
under 4-5 lanes, inflated 4.0-6.8x roughly uniformly across kernel suites,
corpus sweep, solver unit sweep and golden pins. Uniform inflation across
unrelated steps is starvation, not a regression.

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

<!-- plan-section: landed-changes -->

| 2026-08-27 | `1006ea4f1` | `nice` does not cross a session boundary; `CPUWeight` on a sibling slice does. Three instances of one failure shape in this wrapper now — `MemoryMax` without `MemorySwapMax`, `nice` under autogrouping, and `CPUWeight` at the wrong cgroup level twice. Each was genuinely applied, each read back correctly, each worth nothing. The rule: a control for a resource policy must assert the **relation** (sibling level, swap ceiling, scheduling domain), never only the value — the value check is the comfortable check that cannot fail. |
| 2026-08-27 | `3684f24aa` | Controls, mutation-verified. The case that carries the suite is a real deadlock probe: every slot held, the re-entrant job must complete **and** the non-re-entrant one must report 75 — without the second half the first passes on any host where slots were never contended. The harness mutates a four-file scratch copy, never the checkout: these are shell scripts read fresh on every invocation, so an in-place mutant is executed by any lane running a gate during the window. |
| 2026-08-27 | `82f411fa6` | The semaphore wired into `check.sh` (one slot per run, re-entrant, no memory scope on the supervisor), the battery at nice 0 with an advisory fail-open slot, and `Cargo.lock` added to the change filter. `check.sh`'s step list verified byte-identical, so `check-aggregate-scope.sh` is unaffected. |
| 2026-08-27 | `afa659d62` | First diagnosis commit — and its "positive control" was wrong in the way this repository keeps documenting: `grep -c cargo-serialized scripts/local-ci.sh -> 1` matched a **comment**, not a call, so a control certified a query that was measuring nothing. Corrected in the same document rather than quietly fixed. |

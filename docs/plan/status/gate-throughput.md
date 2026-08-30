# Lane: gate-throughput — the cargo semaphore was unwired, and `nice` measured as nothing

<!-- plan-section: lane-status -->

**Verification throughput was the binding constraint, and the cause was
scheduling rather than any gate** (`landed`, gate-throughput, 2026-08-27). The
`hooks/pre-push` battery went from ~250 s uncontended to **2,152 s / 2,654 s**
under 4-5 lanes, inflated 4.0-6.8x roughly uniformly across kernel suites,
corpus sweep, solver unit sweep and golden pins. Uniform inflation across
unrelated steps is starvation, not a regression.

Detail moved to [`../notes/gate-throughput.md`](../notes/gate-throughput.md).

<!-- plan-section: landed-changes -->

| 2026-08-27 | `1006ea4f1` | `nice` does not cross a session boundary; `CPUWeight` on a sibling slice does. Three instances of one failure shape in this wrapper now — `MemoryMax` without `MemorySwapMax`, `nice` under autogrouping, and `CPUWeight` at the wrong cgroup level twice. Each was genuinely applied, each read back correctly, each worth nothing. The rule: a control for a resource policy must assert the **relation** (sibling level, swap ceiling, scheduling domain), never only the value — the value check is the comfortable check that cannot fail. |
| 2026-08-27 | `3684f24aa` | Controls, mutation-verified. The case that carries the suite is a real deadlock probe: every slot held, the re-entrant job must complete **and** the non-re-entrant one must report 75 — without the second half the first passes on any host where slots were never contended. The harness mutates a four-file scratch copy, never the checkout: these are shell scripts read fresh on every invocation, so an in-place mutant is executed by any lane running a gate during the window. |
| 2026-08-27 | `82f411fa6` | The semaphore wired into `check.sh` (one slot per run, re-entrant, no memory scope on the supervisor), the battery at nice 0 with an advisory fail-open slot, and `Cargo.lock` added to the change filter. `check.sh`'s step list verified byte-identical, so `check-aggregate-scope.sh` is unaffected. |
| 2026-08-27 | `afa659d62` | First diagnosis commit — and its "positive control" was wrong in the way this repository keeps documenting: `grep -c cargo-serialized scripts/local-ci.sh -> 1` matched a **comment**, not a call, so a control certified a query that was measuring nothing. Corrected in the same document rather than quietly fixed. |

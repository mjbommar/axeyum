# Lane: inprocessing-proof-path — inprocessing inside the proof-producing core

<!-- plan-section: lane-status -->

**`WIP`, inprocessing-proof-path, 2026-09-07.** Testing the one hypothesis the
[boolean-core lane](bench-boolean-core.md) left standing for the measured
propagation-volume gap: `solve_with_drat_proof` runs none of `axeyum-cnf`'s own
`vivify` / `simplify` / `bve`, so its propagation runs over a formula Kissat's
`probe` umbrella would already have shrunk. Measured deficit to beat: a median
**2.56x more propagations per conflict** (up to 7.72x) over eight p4dfa
instances on one idle host.

The half of the task that is not a schedule change: **every clause an
inprocessing pass adds, strengthens or deletes has to appear in the DRAT stream
in the right order**, or the certificate silently stops being checkable. Working
record, including the entries where the expectation was wrong:
[`docs/research/12-performance/inprocessing-proof-path-2026-09-07.md`](../../research/12-performance/inprocessing-proof-path-2026-09-07.md).

**Next.** Proof-carrying preprocessing wired into the core's entry points, a
soundness-negative test per pass, then the before/after on
propagations-per-conflict.

<!-- plan-section: landed-changes -->

| 2026-09-07 | (pending) | Lane opened: diary, expectations recorded before any measurement. |

# Notes: agent-resource-guards

Detail moved out of [`../status/agent-resource-guards.md`](../status/agent-resource-guards.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

**`bv_nego` was a wrong `sat`, not a wrong term.** The audit called
`1u128 << (w - 1)` a "silently wrong term" in release. Measured with overflow
checks off, the shipped `SatBvBackend` returns **`sat`** for
`(bvnego x) ∧ (x = 1)` at 129 bits — unsatisfiable, since negating 1 at 129 bits
does not overflow. The pre-fix term is `WideBvConst(limbs [1, 0, 0])`, i.e.
`x == 1` where `x == 2^128` was meant, so the query becomes trivially
satisfiable. Debug panicked instead, which is why it read as a build-profile
hazard rather than a soundness one.

**The reachability question it marked UNVERIFIED has an answer: no.** `bvnego`
occurs in **0 of 1430** tracked `.smt2` files; positive control in the same
command, `bvadd` in 106. It is reachable only from the parser on user input.
That lowers the severity — we did not ship a wrong answer on our own corpus —
and it explains why no sweep could have caught it. The asymmetry that hid it is
in the tests: the exhaustive overflow-predicate sweep loops `for w in 1..=4`,
and the one wide test in that suite covers `bv_umulo`, whose wide branch has
existed since it was written.

**`memory_limit_mb` is no longer inert, but a faithful bound is still an ADR.**
Two mechanisms now: a portable pre-allocation clause ceiling at a measured
384 B/clause (zero hot-path cost — it changes a comparison that was already
there), and a `/proc/self/status` probe at three BV phase boundaries plus the
`solve`/`check_auto` front doors. `unknown` with `UnknownKind::MemoryLimit`,
never an abort. **Allocation between two probes is still unbounded**, which is
the 125 GB shape of the 2026-08-17 OOM exactly; closing that needs a
`#[global_allocator]` hook, which is process-global, `unsafe impl` against a
workspace-wide deny, and needs thread-local attribution to mean anything
per-query. Opened as a research question rather than left unspoken.

**Costs measured against a tree without the module**, release, `taskset -c 0-7`:
the default path is 182.8–183.4 µs/check against a 184.0–185.3 baseline — not
distinguishable. A configured limit costs **~32 µs per check, fixed**: 0.00013 %
of a 24 s budget, 17 % of these deliberately tiny checks. The baseline's own
"limit set" and "no limit" columns being identical *is* the defect.

**Every guard in this lane survived its first mutation run.** All five memory
guards: each was shadowed by another that rejected the same query — the probes
are a chain where only the first over the limit can fire, and both clause
ceilings reject the same oversized encoding. Nothing was wrong with the guards;
nothing depended on any one of them. Fixed with a `#[cfg(test)]` seam that
scripts the resident-set reading and by reaching the post-encoding gate
directly, so each test can only be satisfied by one guard — and the isolation is
*asserted*, not assumed (the projected-ceiling test fails if the estimate ever
stops over-approximating rather than quietly stopping isolating). All seven
guards across both defects now kill exactly one test each, registered as
`solver-memory-budget` and `ir-bv-nego-width`.

Next on this axis, in cost order: the allocator-hook ADR (the only thing that
closes the between-probes gap); then a probe on the SAT search itself, where
`axeyum-cnf`'s `DeadlineCallbacks::stop` is an existing periodic hook and the
learnt-clause database is the one long-running allocator this lane did not
bound.

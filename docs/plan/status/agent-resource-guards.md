# Lane: resource-guards — two guards that did not guard

<!-- plan-section: lane-status -->

**Both gap-analysis §7 defects closed, and both were worse than the audit
recorded them** (`DONE`, agent-resource-guards, 2026-08-21).

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

<!-- plan-section: landed-changes -->

| 2026-08-21 | `9333f779d` | **`bv_nego` returned a wrong `sat` above 128 bits.** `1u128 << (w - 1)` with legal widths to 65536: Rust masks the shift mod 128, so at `w = 129` the term became `x == 1` instead of `x == 2^128` and the shipped `SatBvBackend` answered **`sat`** to an unsatisfiable query (measured with overflow checks off; debug panicked instead). Fixed by following `bv_umulo`'s existing wide branch. Corpus reachability, which the gap analysis marked UNVERIFIED: **0 of 1430** tracked `.smt2` files use `bvnego` (control: `bvadd` in 106), so it is reachable only from the parser on user input. Three tests close the width asymmetry that hid it — widths 129/130/191/192/193/256/4096 by value *and* by the constant's structure, the 128-bit boundary staying narrow, and the end-to-end backend verdict. Two guards, each mutation-verified to kill exactly one test, registered as `ir-bv-nego-width`. |
| 2026-08-21 | `d4ffe2a54` | **`SolverConfig::memory_limit_mb` was set but never read on the shipped build** — its only read was under `#[cfg(feature = "z3")]`, and `axeyum-verify`'s `tock_log2_external` had been setting a 2 GB cap on a non-z3 build where it bounded nothing. Now two mechanisms: a portable pre-allocation clause ceiling at a **measured** 384 B/clause (peak-RSS, fresh process per width; a plain `VmRSS` delta under-reports 3–7x and `VmHWM` is monotone, so both obvious methods fail toward *under*-charging), and a `/proc/self/status` probe (**9.4 µs**, 276x an `Instant::now()`, which is why it may only sit at a phase boundary) at three BV boundaries and both front doors. Measured against a tree without it: default path indistinguishable (182.8–183.4 vs 184.0–185.3 µs/check), a configured limit **+32 µs/check fixed**. All five guards **SURVIVED** the first mutation run because they shadowed each other; a scripted-RSS test seam plus direct reach to the post-encoding gate now has each killing exactly one test. A *faithful* bound still needs a `#[global_allocator]` hook — process-global, `unsafe impl`, needs per-query attribution — recorded as an open research question rather than an unspoken gap. |

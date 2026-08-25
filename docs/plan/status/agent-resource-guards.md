# Lane: resource-guards — two guards that did not guard

<!-- plan-section: lane-status -->

**Both gap-analysis §7 defects closed, and both were worse than the audit
recorded them** (`DONE`, agent-resource-guards, 2026-08-21).

Detail moved to [`../notes/agent-resource-guards.md`](../notes/agent-resource-guards.md).

<!-- plan-section: landed-changes -->

| 2026-08-21 | `9333f779d` | **`bv_nego` returned a wrong `sat` above 128 bits.** `1u128 << (w - 1)` with legal widths to 65536: Rust masks the shift mod 128, so at `w = 129` the term became `x == 1` instead of `x == 2^128` and the shipped `SatBvBackend` answered **`sat`** to an unsatisfiable query (measured with overflow checks off; debug panicked instead). Fixed by following `bv_umulo`'s existing wide branch. Corpus reachability, which the gap analysis marked UNVERIFIED: **0 of 1430** tracked `.smt2` files use `bvnego` (control: `bvadd` in 106), so it is reachable only from the parser on user input. Three tests close the width asymmetry that hid it — widths 129/130/191/192/193/256/4096 by value *and* by the constant's structure, the 128-bit boundary staying narrow, and the end-to-end backend verdict. Two guards, each mutation-verified to kill exactly one test, registered as `ir-bv-nego-width`. |
| 2026-08-21 | `d4ffe2a54` | **`SolverConfig::memory_limit_mb` was set but never read on the shipped build** — its only read was under `#[cfg(feature = "z3")]`, and `axeyum-verify`'s `tock_log2_external` had been setting a 2 GB cap on a non-z3 build where it bounded nothing. Now two mechanisms: a portable pre-allocation clause ceiling at a **measured** 384 B/clause (peak-RSS, fresh process per width; a plain `VmRSS` delta under-reports 3–7x and `VmHWM` is monotone, so both obvious methods fail toward *under*-charging), and a `/proc/self/status` probe (**9.4 µs**, 276x an `Instant::now()`, which is why it may only sit at a phase boundary) at three BV boundaries and both front doors. Measured against a tree without it: default path indistinguishable (182.8–183.4 vs 184.0–185.3 µs/check), a configured limit **+32 µs/check fixed**. All five guards **SURVIVED** the first mutation run because they shadowed each other; a scripted-RSS test seam plus direct reach to the post-encoding gate now has each killing exactly one test. A *faithful* bound still needs a `#[global_allocator]` hook — process-global, `unsafe impl`, needs per-query attribution — recorded as an open research question rather than an unspoken gap. |

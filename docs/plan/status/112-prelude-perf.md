# Lane: prelude-perf — why the constructed-real prelude got 3.9x slower

<!-- plan-section: lane-status -->

**`build_creal_prelude` went 8.7 s → 33.0 s across `502184d3f`, and the kernel
was missing the second of Lean's two reduction caches. Adding it takes it back
to 13.0 s** (`DONE`, agent-prelude-perf, 2026-08-20).

The bisected commit aligns the native `Bool` with official Lean order and is
correct. What nobody noticed is what that *switched on*.
`Kernel::build_nat_binop_table` admits the literal-`Nat` acceleration only in an
environment whose `Bool` has constructors `[false, true]` **in that order**
(ADR-0459). While `Bool` was `[true, false]` the table was `None` and every
probe returned immediately — the whole rule had been dead since it landed.
Aligning `Bool` turned it on, and in this workload it fires **1,192,536 times
and produces a literal 575 times** (0.05%). Every one of the 1,191,961 failures
δ-normalises *both* arguments, from inside the δ-**free** normaliser, so the work
lazy-delta exists to avoid is done eagerly and speculatively. 99.98% of the
probes are on terms that mention a free variable.

Measured by disabling the rule at HEAD: 33.6 s → 10.0 s. The regression is that
rule, not the constructor order.

The fix is a memo, not a change to any reduction rule: `Kernel::whnf_core` (the
δ-performing normaliser) had no cache at all, only its δ-free inner step did.
The pinned reference carries **both** — `type_checker.h:31-32` declares
`m_whnf_core` *and* `m_whnf` — so this is convergence on Lean, not a local
trick. The whole δ chain is memoised, not just its head, because every δ step
mints a fresh expression that no cache has ever seen.

Detail moved to [`../notes/112-prelude-perf.md`](../notes/112-prelude-perf.md).

<!-- plan-section: landed-changes -->

| 2026-08-20 | (pending) | `Kernel::whnf_core` is memoised — the second of Lean's two reduction caches (`m_whnf` beside `m_whnf_core`), which this kernel never had. `build_creal_prelude` 33.0 s → 13.0 s, template reuse 0.41 s → 0.15 s. Pure memoisation: same key discipline as the δ-free memo, split on `has_fvars`, cleared by `push`/`pop` and by environment revision, closed half covered by the `reduction_ctx_reads` tripwire. Six guards mutation-checked, each killing at least one test and four killing exactly one; a seventh looked unreachable and a `debug_assert_eq!` proved it is not, which is what the comment on it now records instead of the argument that was wrong. Root cause recorded: `502184d3f` did not slow the kernel down, it switched the literal-`Nat` acceleration ON for the first time, because `build_nat_binop_table` gates on `Bool`'s constructor order. |

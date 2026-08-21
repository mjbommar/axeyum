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

Acceptance is unchanged by construction: the memo returns exactly what the walk
would have returned, the key is complete (revision + expression, split on
`has_fvars` exactly as the δ-free memo is split, with the same `push`/`pop`
scoping), and the closed half is covered by the existing `reduction_ctx_reads`
tripwire.

Verified: `prelude_build_timing` creal 33.0 s → **12.98 s** and template reuse
0.41 s → 0.15 s; `axeyum-lean-kernel --lib` **398 passed**;
`axeyum-solver --features full --lib reconstruct::` **300 passed** in 186 s
against the ~294 s this suite normally takes, because it builds preludes;
`gen-lean-axiom-ledger.py --check` exit 0 with `axreal=30` and every other
prelude 0, unmoved; clippy `--workspace --all-targets --all-features -D
warnings` clean. Peak RSS of a full uncached prelude sweep is 512 MB against
368 MB before — the debug unit sweep's multi-GB profile is pre-existing and was
measured on a clean HEAD snapshot to rule the memo out.

Next on this axis, and the remaining 6.7 s: **our nat rules are in the wrong
loop.** Lean calls `reduce_nat` from `whnf` — after `whnf_core`, before δ
(`type_checker.cpp:765`) — and in `lazy_delta_reduction` guards it with
`!has_fvar(t_n) && !has_fvar(s_n)` (`type_checker.cpp:1093`). Ours is called
from inside `whnf_no_unfolding_uncached`, which *is* Lean's `whnf_core`, with no
`has_fvar` guard anywhere. ADR-0459 already describes the intended placement as
"tried after `whnf_core` and before δ", so the code does not match its own ADR.
Moving it changes what the kernel identifies, so it needs an ADR and differential
evidence, not a perf commit — but the prize is measured: with the rule off and
this memo on, the same build is **6.56 s**, better than the pre-regression 8.7 s.

<!-- plan-section: landed-changes -->

| 2026-08-20 | (pending) | `Kernel::whnf_core` is memoised — the second of Lean's two reduction caches (`m_whnf` beside `m_whnf_core`), which this kernel never had. `build_creal_prelude` 33.0 s → 13.0 s, template reuse 0.41 s → 0.15 s. Pure memoisation: same key discipline as the δ-free memo, split on `has_fvars`, cleared by `push`/`pop` and by environment revision, closed half covered by the `reduction_ctx_reads` tripwire. Six guards mutation-checked, each killing at least one test and four killing exactly one; a seventh looked unreachable and a `debug_assert_eq!` proved it is not, which is what the comment on it now records instead of the argument that was wrong. Root cause recorded: `502184d3f` did not slow the kernel down, it switched the literal-`Nat` acceleration ON for the first time, because `build_nat_binop_table` gates on `Bool`'s constructor order. |

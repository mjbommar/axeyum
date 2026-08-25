# Notes: 112-prelude-perf

Detail moved out of [`../status/112-prelude-perf.md`](../status/112-prelude-perf.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

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

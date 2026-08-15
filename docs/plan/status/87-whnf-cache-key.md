# Lane: whnf-cache-key — the WHNF cache key, and K-like reduction

<!-- plan-section: lane-status -->

**The latent cache-key unsoundness is defused and K-like reduction landed; the
40-stream import census is 40/40 clean with zero root blockers (`WIP`,
whnf-cache-key, 2026-08-15).** Taking over the landmine
[`import-brecon`](86-import-brecon.md) stopped in front of. Full write-up:
[`docs/formalized-math-2026-08/diary-whnf-cache-key.md`](../../formalized-math-2026-08/diary-whnf-cache-key.md).

**Was it real?** Yes, and it now runs as a test rather than an argument.
`tc_tests::whnf_cache_key_collision_is_constructible` builds two
`LocalContext`s that both mint fvar **0** — one recording it as `True`, one as
`False` — with no declaration admitted in between, so the environment revision
does not move either. The same `ExprId` (`True.rec … h`, `True` being K-like)
has two different correct normal forms in them. The pre-fix algorithm is kept
verbatim as `#[cfg(test)] whnf_core_context_free_cached` and the test runs it:
it answers the **first** context's normal form in the second. It was **latent,
not live** — nothing in reduction consulted a context before this commit — so no
fact and no ADR are owed; the fix ships in the same commit as the rule that
would have made it reachable.

**The key.** Split on `has_fvars`, because that boundary has a *structural*
argument rather than a disciplinary one. Closed expressions stay in the
kernel-global cache: β/ζ/ι/projection/δ build only from subterms of the input
and from (closed) environment declarations, so a reduction that did not start
with an `FVar` can never reach a context lookup. Open expressions are memoised
by the `LocalContext` itself, beside the `infer_cache`/`def_eq_cache` already
there and already cleared on `push`/`pop` — which is exactly the validity domain
an answer that depended on a local's type should have. The closed half's
argument is enforced, not asserted: `Kernel::reduction_ctx_reads` counts context
reads inside reduction and `whnf_no_unfolding` asserts it does not move while a
closed term is normalized, so a future context-consulting rule trips a check
instead of quietly invalidating the cache.

**Cost: nothing measurable.** `examples/prelude_build_timing.rs` (new) over the
two heavy preludes, release, both behaviours built from one tree — old key
22.3/22.9 ms `nat` and 39.5/40.8 ms `integer`; shipped split 22.5/22.8 and
39.6/40.0. Dropping open-term memoisation altogether would have cost 8–9%.
(My first "baseline" was a stale binary and made the split look like a speed-up;
an A/B has to be two builds of one tree.)

**`pub fn whnf` did not change.** It is now `whnf` in the empty local context,
delegating to `pub(crate) whnf_core(e, ctx)` — a restriction, never a widening,
since without a context K cannot fire on an open term. The threading stopped at
seven functions, not the ~55 call sites the handover estimated.

**K-like reduction** (`k_like_major`, Lean's `to_cnstr_when_K`) consults the
predicate we already computed and used only for the wire `k` flag. Guard is
Lean's, and every clause is load-bearing: removing each in turn flips exactly
one test. `eq_of_heq` imports; census **40 of 40 streams clean, 0 declines, 0
root blockers** (was 37/40 with 1). No new fact — a capability, pinned by tests.

The negative-suite controls also caught two of my own tests passing for the
wrong reason: a constructor-with-fields probe is refused by the def-eq guard
before the zero-fields clause is reached, and a mutual `Prop` group's recursor
is small-eliminating so the probe shape *cannot be built* for it
(`UniverseArityMismatch`). Those three clauses are now pinned directly on the
predicate in `inductive_tests::the_k_like_predicate_*`, where the controls do
flip them.

Next: the corpus has stopped measuring at 40/40 — replace it with one that
exercises what we know we lack (`to_cnstr_when_structure`; `cheap_proj`
ordering in `reduce_projection`). Still open across three diaries now: the
toolchain re-pin (4.30.0 → current).

<!-- plan-section: landed-changes -->

| 2026-08-15 | (pending) | WHNF cache key split on `has_fvars` (closed → kernel, open → `LocalContext`) with a `reduction_ctx_reads` tripwire; the collision demonstrated as a test against a kept pre-fix replica; K-like reduction with a guard-by-guard controlled negative suite; import census 37/40 → **40/40**, 1 root blocker → **0**. |

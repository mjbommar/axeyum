# ADR-0193: Bounded shared-memo model replay

Status: accepted
Date: 2026-07-16

## Context

ADR-0192 completes Glaurung's bounded exact-SAT cache admission, but the first
per-check cache-aware warm profile changes the residual attribution. On the
2,551-check SurfacePen lineage, original-term SAT replay consumes 447.046 ms,
or 38.82% of the 1.151 s profiled internal total. The incremental replay loop
calls `axeyum_ir::eval` separately for every active assertion and one-shot
assumption. Each call creates a new evaluator memo, so shared source DAGs are
re-evaluated once per root even though the model assignment is fixed for the
whole replay.

This is not permission to weaken replay. Every SAT result, including a cache
hit, must still be evaluated against every original active root by the trusted
ground evaluator. The question is only whether those evaluations may share
already-computed subterm values under one immutable assignment, and how that
sharing remains memory-bounded.

## Decision

Use one caller-owned `eval_with_memo` map within an incremental SAT replay and
share it across original assertion and assumption roots, with a fixed 4,096-
entry cross-root retention threshold.

The memo is created after the model is converted to one immutable assignment
and is dropped before the replay call returns. It never survives a model,
check, solver, arena, or thread boundary. Before evaluating a new root, the
solver clears the memo when it contains at least 4,096 values. Evaluating one
root may still require more entries, exactly as the former per-root `eval`
call did; the next root then starts empty. This bounds accumulated cross-root
retention to the threshold plus one root's ordinary evaluator working set.

The decision does not change:

- the original assertion, scope, or assumption sequence;
- the evaluator or any Bool/BV semantics;
- rejection of `false` or non-Boolean roots as a backend soundness failure;
- evaluator errors degrading the candidate to `Unknown` rather than SAT;
- mandatory replay on fresh SAT results and exact cache hits; or
- any cache, warm-admission, preprocessing, lowering, CNF, SAT, model-lift, or
  public API policy.

## Evidence

Glaurung `5648257` and the v5 warm-profile schema execute the same SurfacePen
lineage before and after the change. Both profiles contain 2,551 complete
records (2,282 SAT / 269 UNSAT), agree with Z3 on every check, report zero
unknown splits and replay failures, and preserve exact warm/cache traffic,
AIG/CNF structure, and finding behavior.

| Profiled internal measure | Per-root memo | Bounded shared memo | Change |
|---|---:|---:|---:|
| Replay | 447.046 ms | 54.643 ms | -87.78% |
| Total attributed | 1,151.468 ms | 765.651 ms | -33.51% |
| Replay share | 38.82% | 7.14% | -31.69 pp |

The first unbounded shared-memo prototype produced essentially the same replay
win but appeared to raise SurfacePen RSS against ADR-0192's older artifact.
It was rejected before admission. The 4,096-entry version was then compared
causally against clean Axeyum `9cb82f72` using the same current Glaurung client,
toolchain, adaptive/cache-on policy, driver bytes, and three-process work:

| SurfacePen measure | `9cb82f72` | Candidate | Change |
|---|---:|---:|---:|
| Axeyum | 1,070.267 ms | 674.933 ms | -36.94% |
| Axeyum/Z3 | 0.243795 | 0.154875 | -36.47% |
| Median RSS | 78,888 KiB | 77,976 KiB | -1.16% |
| Z3 | 4,390.033 ms | 4,357.933 ms | -0.73% |

The fail-closed comparator accepts this causal pair under the ordinary 3%
Axeyum, 3% ratio, 5% RSS, and 2% Z3-drift alarms. All 15,306 combined checks
agree, with identical work and findings and zero replay failures.

A clean-Axeyum six-process candidate then covers both established drivers:
SurfacePen is 674.700 ms at 0.155105x Z3 with 77,928 KiB median RSS;
NETwtw10 is 17,327.633 ms at 0.333030x Z3 with 256,708 KiB median RSS. All
92,721 checks agree and both Axeyum CVs are below 0.24%. Against ADR-0192's
older cache-on artifact, NETwtw10 clears every alarm (-3.77% Axeyum, -4.00%
ratio, +0.31% RSS, +0.24% Z3). SurfacePen improves Axeyum/ratio by about 37%
and keeps Z3 drift to +0.18%, but its old cross-revision RSS comparison is
+6.52% and therefore correctly fails that artifact's 5% alarm. The
same-current causal control above shows the patch itself reduces RSS by 1.16%;
the publication baseline must be refreshed rather than relabeling that older
client/binary drift as a passing comparison.

The memory-capped all-feature incremental tests, four focused incremental
unit tests, formatting, diff checks, and strict all-target/all-feature
`axeyum-solver` Clippy pass. The implementation is Axeyum commit `d3d95299`.

## Alternatives

Keeping a fresh memo per root preserves semantics but was rejected because it
re-evaluates shared source DAGs enough to dominate the measured client path.
Keeping an unbounded memo for the full replay was rejected because its union
working set is not an acceptable framework memory contract. Persisting a memo
across checks or models was rejected as unsound: `eval_with_memo` deliberately
trusts caller-owned entries, whose values are valid only for the assignment
that produced them. A public threshold knob was rejected because this is an
internal evaluator working-set bound, not a solver policy consumers should
have to tune.

## Consequences

Original-term replay remains the SAT trust anchor, but repeated assertion-DAG
work is no longer the dominant measured SurfacePen phase. On the bounded
candidate profile, model lifting and CNF construction become the two largest
internal stages, followed by SAT, bit blast, translation, and replay.

The next implementation must start with operation-count attribution for model
lifting versus the symbols actually needed for original replay; it may not
drop model values or weaken completion merely because replay is now faster.
CNF work remains the parallel measured GQ5 lane. Before replacing the committed
Glaurung performance artifact, repeat a clean same-current-client two-driver
baseline/candidate pair so the stale SurfacePen RSS control is resolved rather
than waived.

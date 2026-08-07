# QF_NIA A3 model-reconstruction diagnostic v1 result — 2026-08-07

## Verdict

The former 13-case `arith DPLL candidate failed full model replay` bucket was a
lossy secondary symptom, not evidence that the arithmetic theory had produced a
complete model. The bounded conflict probe may decline to refute a selected
literal conjunction; the subsequent model oracle can then return `Unknown` at
the same shared deadline. `theory_model` previously collapsed every non-SAT
outcome—including that `Unknown` and even `Unsat`—to an absent model. The caller
filled all symbols with well-founded defaults, replayed the fabricated
assignment, and overwrote the real cause with one generic replay-failure detail.

Commit `4ff9a82c6` removes that information loss. Empty theory slices, concrete
models, typed declines, and inconsistent reconstruction outcomes are distinct.
Only a concrete model reaches default completion and original-assertion replay.
The verdict boundary is unchanged: every affected result remains `Unknown` and
no unchecked SAT is admitted.

## Diagnostic sequence

The first bounded instrument recorded the first failing assertion, its term ID,
evaluated outcome, and bound/unbound symbol counts. A fresh production-path run
over the exact 13-case cluster completed all rows under 8 GiB and 24,000 ms per
query. Six reproduced replay rejection; seven shifted earlier to ordinary DPLL
or refinement budget declines. All six reproducing rows had every referenced
symbol bound and evaluated an assertion to `false`; none failed evaluation.

A second discriminator replayed every selected arithmetic literal under the
same reconstructed assignment. All six had a selected literal evaluate false:

| Row | Assertion ordinal | Bound symbols | First false selected literal |
|---|---:|---:|---:|
| `From_AProVE_2014__SortCount.jar-obl-10__terminationS_2_0.smt2` | 7 | 746/746 | 12 |
| `SAT14/571.smt2` | 0 | 3,099/3,099 | 3,216 |
| `geo1-u_valuebound2-O0.smt2` | 0 | 1,607/1,607 | 1 |
| `ps2-ll_unwindbound50-O0.smt2` | 0 | 1,311/1,311 | 1 |
| `aproveSMT4687047739446499948.smt2` | 0 | 74/74 | 63 |
| `aproveSMT5048239408100334127.smt2` | 0 | 125/125 | 66 |

That excludes missing-symbol completion and Boolean-abstraction equivalence as
the shared cause. Inspection then found the non-SAT-to-empty-model collapse at
the owning reconstruction boundary.

## Exact post-fix evidence

The release `explain_corpus` binary built from the exact source committed as
`4ff9a82c6` has SHA-256
`9202790f315ef06a945217d3faa70303ef6618a5a5d4bf3ba0cdc04d9c03bc1e`.
The six-row post-fix production capture has SHA-256
`ad6e203a0f9c6ac856a5991541a1a1a47aed1307a9646bdea24487feb7d91cd2`.
It contains six complete schema-1 traces in exact input order:

- five preserve the actual integer reconstruction decline:
  `QF_LIA branch-and-bound undecided: wall-clock deadline passed (node cap
  20000000)`;
- one (`aproveSMT4687047739446499948.smt2`) shifts earlier to the arithmetic
  DPLL's own bounded timeout;
- zero contain `failed full model replay`;
- all six remain `unknown` and no memory ceiling fires.

Focused gates at the exact code boundary are 26/26 full-feature DPLL unit tests
and warning-denied full-feature solver-library Clippy. The new unit control
forces synthetic reconstruction `Unknown` and `Unsat` outcomes and proves
neither becomes an empty/default model.

## Breadth disposition

This is a correctness and observability repair, not an A3 score gain. It closes
the diagnostic-first slice but not A3's exit criterion. The next bounded lever
is to reuse a concrete SAT model already returned by the theory consistency
probe instead of discarding it and rerunning the same conjunctive solve for
reconstruction. Unknown probes must remain unknown; no fresh deadline, cap
increase, or replay bypass is permitted. That experiment requires its own
preregistration and exact A/B controls before implementation.


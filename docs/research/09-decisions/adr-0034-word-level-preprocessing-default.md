# ADR-0034: Word-level preprocessing is opt-in, default-off (for now)

Status: accepted — **default flipped to ON (2026-06-18)**, see the update below
Date: 2026-06-17

> **Update (2026-06-18): the ratification criterion is met; `preprocess` now
> defaults ON.** The full model-sound pipeline (`solve_eqs`/`elim_unconstrained`,
> not just canonicalization) on the public p4dfa slice decides **4/113 @3s and
> 7/113 @20s vs eager 2/3, `DISAGREE=0`, PAR-2 non-worse** — the net-non-negative
> decided-delta criterion below, on the public corpus. `SolverConfig::default()` now
> sets `preprocess: true` (commit `6cb2f1b`), with two safety guards added so it is
> never a correctness dependency: it is **skipped on quantified queries** (a QF
> transform) and is **best-effort** (any reduction-pass error → solve the original
> query). Validated by a full-workspace behaviour check (103 test binaries green).
> The unbounded-`solve_eqs` hazard the original note worried about is fixed by the
> deterministic `solve_eqs_bounded` fuel (ADR-0037).

## Context

Track 1, P1.2 added a denotation-preserving **canonicalizer** to `axeyum-rewrite`
(constant folding, identity rules, and — most recently — commutative-operand
ordering, so `(bvmul a b)` and `(bvmul b a)` hash-cons to the same term). It was
then wired into two solver paths: `check_with_preprocessing` (as its first pass)
and, behind a new `SolverConfig::preprocess` flag, the main `solve()`/`check_auto`
façade.

That raised a real question that should not be decided silently in code: **should
word-level preprocessing run by default** on every `solve()` call, or stay opt-in?
The canonicalizer is *always sound* to run (it preserves denotation and the symbol
set, so the `sat` model is unchanged and still replays against the original
assertions), so this is purely a performance/ergonomics decision, not a soundness
one. It mirrors the existing `cnf_inprocessing` lever, which is also off-by-default.

This closes the open sub-question under the benchmarking-and-performance
methodology: "which preprocessing belongs on the default path, and on what
evidence."

## Decision

**Keep word-level preprocessing opt-in (`SolverConfig::preprocess`, default
`false`); do not flip the default until a broad-corpus measurement shows a net
PAR-2 improvement.** The capability ships now as a knob on both
`check_with_preprocessing` and `solve()`; the default path is unchanged so all
recorded baselines remain comparable.

Concrete ratification criterion for a future ADR that flips the default to `on`:
on the public QF_BV corpus (not just the 43-file curated slice), with a fixed
per-instance budget, `--preprocess` must show a **net non-negative decided-count
delta and a non-worse PAR-2 mean**, with `DISAGREE=0` and zero model-replay
failures throughout. (Denotation-preservation guarantees the last two; the first
two are the empirical question.)

## Evidence

- **Soundness is not at stake.** Canonicalization is exact-denotation and
  symbol-preserving; `check_with_preprocessing` and the `solve()` flag both replay
  the `sat` model against the *original* assertions. A 32-bit
  `(not (= (a*b) (b*a)))` is refuted **instantly with no multiplier bit-blasting**
  (`multiplier_commutativity_is_refuted_by_canonicalization`,
  `preprocess_flag_refutes_multiplier_commutativity_without_blasting`).
- **The measured benefit is real but small so far.** On the committed 43-file
  curated QF_BV slice, enabling the full rewrite raised the decided count
  **32 → 33** (cracking `calypto_problem_9`) and improved PAR-2 **1.062 → 1.010 s**,
  with `DISAGREE=0`. That is not yet enough to justify changing the default for
  every user on every instance.
- **It does not crack the headline targets alone.** The `wienand commute08/16`
  multiplier-commutativity instances stay `unknown`: they are
  associativity+commutativity over multiplier *trees* threaded through intermediate
  `var` bindings, which binary operand-sorting cannot fold (needs AC-tree
  normalization + intermediate-equality inlining — out of scope here).
- **Cost.** Preprocessing spends time rebuilding terms and can change the term
  structure fed to downstream dispatch; off-by-default keeps the baselines clean
  and avoids a blanket regression risk on instances preprocessing does not help.

## Alternatives

- **Default-on now.** Rejected: the curated +1 is too thin to justify a global
  default change, and the broad-corpus effect (especially on instances where
  canonicalization only adds churn) is unmeasured.
- **No façade knob (only `check_with_preprocessing`).** Rejected: users decide via
  `solve()`; a flag there is the natural surface and composes with the existing
  `cnf_inprocessing`/`prove_unsat` levers.
- **Make it a separate pre-pass function callers invoke manually.** Rejected as
  redundant — the canonicalizer is already a public `axeyum-rewrite` entry point;
  the value is making it reachable *through the solver* without manual term surgery.

## Consequences

- `solve(.., with_preprocess(true))` and `check_with_preprocessing` give callers
  word-level preprocessing today; the default path and baselines are unchanged.
- The default-flip is a *measurement* task, not a design one — gated on the public
  QF_BV corpus criterion above. Until then, benchmark comparisons that want the
  preprocessed path must set the flag explicitly.
- Independent of this decision, the genuinely high-leverage remaining levers are
  AC-tree normalization (cracks the commute instances) and the custom CDCL core
  (the measured SAT-solving bottleneck on multipliers); preprocessing is a
  complement to, not a substitute for, those.

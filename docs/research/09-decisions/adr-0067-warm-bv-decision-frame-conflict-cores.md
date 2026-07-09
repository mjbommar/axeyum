# ADR-0067: Warm BV Decision-Frame Conflict Cores

Status: accepted
Date: 2026-07-09

## Context

ADR-0066 made bounded scalar QF_UFBV a canonical `CdclT` combination, but its
first BV adapter reported every active theory literal whenever the warm exact BV
conjunction was unsatisfiable. Those clauses were sound but unnecessarily wide,
discarding final-conflict information that the existing incremental SAT adapter
already computes for frame selectors.

The obvious finest-grained design gives every asserted theory literal its own
selector. That must be measured rather than assumed beneficial: selectors are
also SAT assumptions on every warm check, including satisfiable paths.

## Decision

Map the warm SAT solver's failed **decision-frame** selectors back to active BV
theory literals and return that subset as the `CdclT` theory conflict.

- `IncrementalBvSolver`'s private solve result carries separate one-shot
  assumption and active-frame assertion cores. Existing public results and
  one-shot assumption-core behavior are unchanged.
- Every non-base incremental frame is already guarded by one persistent selector.
  On UNSAT, base-frame assertions plus assertions from failed frame selectors form
  the active assertion core. Mapping iterates frames in insertion order, so output
  remains deterministic.
- The QF_UFBV BV adapter keeps one warm frame per `CdclT` decision level. It maps
  core terms back to tracked theory atom/polarity pairs; missing adapter evidence
  or an empty mapping falls back to the full active core.
- Do **not** allocate one selector per theory literal. This was implemented and
  measured, then reverted because its repeated assumption overhead regressed the
  available corpus.

This amends only ADR-0066's deliberately non-minimal full-core policy. Its
combination architecture, model replay, eager fallback, and evidence route are
unchanged.

## Evidence

- A mechanism test places an irrelevant BV literal in an earlier decision frame
  and contradictory equalities in later frames. The returned conflict is exactly
  the two contradictory equalities, excluding the irrelevant frame.
- A separate push/pop test proves the warm selector frames track theory
  backtracking.
- Existing incremental suites pass 7/7, and the full symbolic-execution suite
  passes 77/77, including the public one-shot assumption-core contracts.
- Three deterministic 512-case QF_UFBV matrices remain clean: direct online vs
  eager pure Rust, front door vs eager pure Rust, and direct online vs Z3 over the
  eager reduction (1,536 agreements, no direct-route `Unknown`).
- The public curated QF_UFBV corpus remains 6/6 decided and Z3-agreeing with zero
  replay failures.

Performance evidence is deliberately narrow. On the same six-row development
run, the original full-core baseline was mean 0.061 s with `bug520` at 0.332 s.
Per-literal selectors regressed to 0.072 s and 0.382 s, so that design was
reverted. Decision-frame cores measured 0.063 s and 0.332 s: neutral within this
small corpus, not a speedup claim.

## Alternatives

- **Keep the full active trail.** Sound but throws away already-available failed
  selector information and learns wider clauses.
- **One selector per theory literal.** Gives finer cores, but the measured SAT
  path regression outweighs the unproven conflict benefit on current evidence.
- **Deletion-minimize after every conflict.** Can produce smaller cores but needs
  repeated BV solves and spends the shared deadline after a sound core is already
  available.
- **Run a second core-only solver.** Avoids persistent selector overhead but
  re-bit-blasts or duplicates the warm state at each conflict.

## Consequences

- Online BV theory clauses can omit entire irrelevant decision levels without a
  second solve, second bit-blast, or new public API.
- Cores remain coarse within one decision level, and all base-level BV literals
  remain present. Literal-level refinement can return only with evidence that
  avoids the measured repeated-assumption cost.
- Failed-core extraction has the same lower-assurance SAT boundary as the warm BV
  UNSAT result itself; proof production still re-runs the established certifying
  eager route.
- BV propagation and relevance-driven interface generation remain the next P1.6
  performance levers.

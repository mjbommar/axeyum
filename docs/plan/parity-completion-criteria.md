# Parity completion criteria — `are_we_done`

Revised 2026-09-08 (evening) after a day of measurement. The morning version
is superseded and its errors are recorded below, because a scoreboard that
rewards the wrong action is worse than no scoreboard.

`are_we_done` prints `yes` only when ALL of the following hold, each verified
by a named command whose exit status depends on the finding.

## The criteria

**1. Every UNSAT is checkable against the ORIGINAL formula.**
Today, with inprocessing enabled, the DRAT proof is checked against the
**reduced** formula — the bounded-variable-elimination link is trusted, not
checked (ADR-1750). This is the project's identity ("untrusted fast search,
trusted small checking"), so it outranks every performance item here. Three
independent lanes converged on it as the real blocker.

**2. The gap closes on the measured divisions.**
Baseline 2026-09-08 morning: 1,565 of 1,892 across 12 divisions, gap 327 against
the true frontier (251 on the narrower board). 85% of the gap is arithmetic, not
bit-vectors — quote the frontier number, and name the reference solver.

Measured today: QF_UFLIA 116 -> 125 decided. QF_LIA losses 26 -> 23. QF_LRA +1.

**3. No wrong sat/unsat, ever.** Zero disagreements against the reference
oracles on every corpus sweep. Non-negotiable and already holding.

**4. Every instrument survives a timeout.**
A watchdog kill must report what accumulated, labelled partial, not discard it.
The files we time out on are the ones we most need data about. Partly landed:
`theory-layer`, engine counters, route attribution, `front-door` and `dl-online`
now survive; `bv-layer` survives only a completed check and `; config` does not
survive at all.

**5. Every admission limit carries a live justification.**
70 of 113 registry entries can refuse work; **52 have no date**, so they can be
called neither stale nor valid, and a sweep found **75 more limits outside the
registry, not one naming a date or commit**. The basis gate exists and fires;
the population is not yet covered.

## What the morning version got wrong

**"`InprocessOptions::default()` is not `OFF`" was the wrong target.** Measured
over the pinned 200-file QF_BV list at 24 s, inprocessing is at parity on files
decided and WORSE on PAR-2 — best arm 186 decided / 960.5 against the baseline's
184 / 926.8. **Turning it on would have satisfied the criterion and made the
solver no better.** The flag stays `false`; the goal was always the wasted work
underneath it, and 71% of BVE's cost and 53% of subsumption's are now recovered.

**"Break-even at 5x the budget" was inherited, not measured.** It is 12-24 s on
the current tree. The 120 s figure had never been re-derived.

**The `sat` model-reconstruction blocker did not exist.** It was a code-reading
propagated as a measured fact; `reconstruct_sat_result` composes correctly and a
bad model returns `Unknown`, never `sat`, across 173 cross-checked files.

## The rule this file exists to enforce

Every criterion above is falsifiable by a command. None is satisfiable by
flipping a flag. If a criterion can be met without the solver getting better,
it is the wrong criterion — that is exactly what happened this morning.

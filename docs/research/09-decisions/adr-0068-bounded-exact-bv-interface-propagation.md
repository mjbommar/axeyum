# ADR-0068: Bounded Exact BV Interface Propagation

Status: accepted
Date: 2026-07-09

## Context

ADR-0066 connected EUF and BV on one canonical `CdclT` trail, and ADR-0067
narrowed BV conflicts by failed decision frame. The BV adapter still emitted no
positive theory propagation: even when exact finite-domain semantics entailed an
interface equality such as `(x + 1) = (y + 1) -> x = y`, the Boolean layer had
to guess that equality before the e-graph could use it for congruence.

The warm SAT adapter does not expose propagation-only state. Probing every atom
with a full solver call would be unbounded and could recreate the selector
overhead rejected by ADR-0067. A useful first route therefore needs explicit
relevance and work bounds plus an implication proof stronger than the current
model's guessed value.

## Decision

Enable bounded exact BV-to-EUF propagation for generated UFBV interface
equalities.

- Mark argument/result interface equalities as propagation candidates while
  building the paired original/abstract atom table. Formula atoms remain normal
  BV constraints, not probe targets.
- After a successful warm BV check, use its model only to choose which polarity
  to test. Ask the same persistent CNF whether the active frame selectors plus
  the opposite polarity are UNSAT. A SAT probe emits nothing; an UNSAT probe
  proves the candidate and maps failed active-frame selectors to its reason.
- The implication probe skips model reconstruction and replay. Its SAT result is
  only a missed-propagation decision; its UNSAT result has the same assurance
  boundary as existing warm BV conflicts.
- Probe one deterministic round-robin candidate per theory-state change. Retain
  discovered propagations while the trail only grows, because entailment is
  monotone; clear and recompute them on backtrack.
- Admit propagation only when the deduplicated interface set has at most 64
  atoms, and stop after 128 probes per theory instance. Deadline exhaustion
  remains first-class `Unknown`; missing/non-UNSAT evidence never fabricates a
  propagation.
- Merge the pending BV propagations with e-graph propagations on the existing
  `TheorySolver::propagate` surface. No second Boolean driver or public API is
  introduced.

## Evidence

- A direct mechanism gate proves `(x + 1) = (y + 1)` propagates `x = y` with the
  shifted equality as its reason.
- A canonical-driver gate proves `CdclT` consumes that interface propagation on
  a satisfiable UF companion instead of deciding the equality.
- The committed `bug520` regression parses to 50 deduplicated interface atoms
  and exercises the bounded route. A diagnostic run performed 93 probes, found
  31 BV implications, and the combined EUF+BV driver recorded 46 successful
  theory propagations.
- Three deterministic 512-case matrices remain clean: online/eager pure Rust,
  front-door/eager, and online/Z3 over eager reduction (1,536 agreements, no
  direct-route `Unknown`). The public QF_UFBV corpus remains 6/6 decided and
  Z3-agreeing with zero replay failures.

An exact same-tree five-run A/B changed only the interface admission constant:

| configuration | corpus mean | `bug520` |
|---|---:|---:|
| propagation enabled (cap 64) | 0.034-0.036 s | 149.96-152.79 ms |
| propagation disabled (cap 0) | 0.065-0.066 s | 347.10-352.39 ms |

Thus this bounded route is a measured performance win on the available public
slice, roughly 2.3x on `bug520`. The corpus is only six rows; this is not a broad
Z3 performance-parity claim.

## Alternatives

- **Keep BV conflict-only.** Sound, but forces search to rediscover exact BV
  consequences before EUF can consume them; the exact A/B is materially slower.
- **Propagate the current model value.** Rejected as unsound: a model choice is
  not an entailment. The opposite-polarity UNSAT check is load-bearing.
- **Probe every unassigned semantic atom.** Rejected as unbounded and mostly
  irrelevant to the cross-theory equality bus.
- **Probe every interface atom after every assignment.** Rejected because it
  multiplies SAT calls and selectors. One round-robin candidate per state plus
  fixed caps preserves predictable cost.
- **Require one selector per atom permanently.** Rejected by ADR-0067's measured
  regression. Ephemeral probe selectors are bounded and used only where the
  interface census admits them.

## Consequences

- Exact BV equalities can now reach congruence closure before a Boolean decision,
  closing the first bidirectional propagation loop on the UFBV equality bus.
- Probe selectors and clauses accumulate in the warm CNF, but at most 128 per
  query; larger interface sets retain conflict-only behavior.
- The enabled row now has a real measured speedup, while Z3 remains faster on
  absolute `bug520` wall time (about 9-11 ms in these runs).
- Relevance-driven interface generation remains the next scale lever: it should
  reduce the 50-atom census before raising either propagation cap.
- QF_AUFBV, mixed BV+LIA, and proof production remain unchanged; eager
  certifying reductions still own evidence.

# ADR-0055: Dispatch policy for the online CDCL(T) routes

Status: accepted
Date: 2026-07-03

## Context

P1.5 slices (a)+(b) landed the generic online CDCL(T) driver
(`CdclT<T: TheorySolver>`, 1-UIP over the mixed implication graph) with two
theories: `EufTheory` (parity-twin of the validated offline `check_qf_uf`,
2500/2500 agreement) and `StringTheory` (the ADR-0053 word core as an online
theory; census disjunctive shapes decide; fuzzes at DISAGREE=0 against both
Z3 and cvc5). The 5th periodic review called the keystone **dark** — built
but opt-in — and demanded a dispatch decision plus the default-on
verification gate. That gate is now paid (`5707563b`): termination under
adversarially non-monotone theories (20,000 mock-theory runs + a 16M-step
budget belt), a real per-assert expansion blow-up in the congruence checker
found and size-budgeted (`MAX_EXPANSION_COMPONENTS = 4096`; doubling chains
declined in ~100µs instead of overflowing the stack at k≥14), and the
closed-universal polarity guard pinned by 400 nested-polarity differential
cases at DISAGREE=0.

## Decision

**The QF_S online CDCL(T) route is default-on at the front door (it already
is — this ADR ratifies the landed ordering); the QF_UF online route stays
opt-in until it has a measured reason to be default.**

- **QF_S (default-on, ratified).** The front-door second-chance stack is:
  bounded pre-check (ADR-0029) → bounded-unsat gate (ADR-0052) → one-shot
  word route (refute + arrangement search, ADR-0053) → **online CDCL(T)
  route over the `word_skeleton` Boolean structure** (`c924fcb0`). Each
  stage only ever adds a verdict to an `unknown`; sat is replay-gated, unsat
  is checked-derivation-gated at every stage; `config.timeout` threads
  through all of them and the driver carries the step-budget belt. Measured:
  QF_S 52→58 across the day with every new verdict oracle-verified — the
  route earns its place in the default path.
- **QF_UF (opt-in, criteria recorded).** The online driver is currently a
  *parity twin* of the validated offline `check_qf_uf` (which already
  handles Boolean structure via its embedded DPLL): flipping the default
  today buys consolidation, not capability, and the measured-first rule
  (destination-2) says architecture swaps ride on measurement. Default-on
  criteria (any one suffices): (1) a measured decide-rate or PAR-2 win on a
  committed division; (2) the embedded-DPLL → `CdclT` migration landing, at
  which point the twin becomes the only loop; (3) a theory-combination
  slice (e.g. strings+LIA over the driver) that requires the shared loop in
  the default path.
- **Future theories arrive online-first.** New `TheorySolver` impls (LIA/LRA
  migration, the len↔LIA string bridge, regex membership per ADR-0054) plug
  into `CdclT` and enter dispatch behind the same discipline: differential
  fuzz both directions, replay/checked-derivation gates, deadline + step
  budget, then a measured default-on decision per route.

## Evidence

- QF_S: the committed baseline moved 52→58 with DISAGREE=0 maintained
  (z3-library+binary compares; cvc5 crosscheck 401/401); the online stage
  decided the census disjunctive class nothing else reaches.
- The default-on verification gate (`5707563b`): non-monotone-theory
  termination property (20k runs, verdicts brute-force-checked), the
  expansion size budget (a real defect fixed, not a hypothetical), polarity
  regressions + 400-case nested fuzz.
- QF_UF: 2500/2500 online-offline agreement and an unchanged 3000-case z3
  fuzz — evidence of parity, and exactly why default-on is not yet earned.

## Alternatives

- **Flip QF_UF default now.** Rejected: no measured benefit; the offline
  route is validated surface with years of accumulated tests; swapping the
  default on parity alone risks perf/behavior drift for zero banked gain.
- **Keep QF_S online opt-in too.** Rejected: it is the only route that
  decides the Boolean-structured word class, it moved the committed
  scoreboard, and its soundness gates are the strongest in the string stack
  (checked derivations + dual oracles + replay).
- **A config flag per route, user-facing.** Deferred: `SolverConfig` already
  carries opt-ins where they exist; a public routing-policy surface is a
  P1.8 (strategy/tactics) concern, not this ADR.

## Consequences

- **Easier:** the keystone is no longer dark — its measured value (QF_S 58)
  is banked and its dispatch position is a recorded decision; new theories
  have a template for entering the default path.
- **Harder / cost:** two loops coexist for EUF until the migration criteria
  fire (accepted: the twin is cheap and the parity fuzz pins drift).
- **Revisited when:** any QF_UF default-on criterion fires; the arithmetic
  theories migrate onto the driver; or theory combination over `CdclT`
  (strings+LIA) lands and forces a broader routing table.

## Foundational-DAG / register updates

- Record the online CDCL(T) loop as the dispatch bus for Boolean-structured
  theory queries (QF_S default; QF_UF opt-in with criteria).

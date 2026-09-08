# config-registry, 2026-09-07 — enumerating, recording and dating the configuration surface

Working diary. Appended as the lane runs; nothing here is retro-fitted.

## The question

The solver's behaviour is governed by numeric constants scattered across the
theory and Boolean engines as private `const`s. Three properties were missing,
and each has cost a lane this week:

1. **Enumerability.** No list. A lane retuning one cap could not see the other
   gate metering the same resource in a different unit.
2. **Recordability.** A run did not emit the configuration it used, so an
   experiment was not reproducible from its output and a surprising result
   could not be traced to a value.
3. **Datability.** A justification carried no date, so it could not be compared
   against the code it protects. `MAX_ONLINE_LRA_ATOMS`' rationale predated the
   bound that capped the very cost it named by three days, and stood for
   thirteen months.

## Scope discipline (fixed at the start)

This lane does not change a single constant's value. Three lanes this week
found that changing one without establishing what it protects produces a
plausible change that makes things worse. A value that looks wrong gets
recorded with evidence and left alone.

## Method

Enumeration was fanned out over three readers with one shared filter, so the
population is defined by a rule rather than by what a search happened to
surface. A **governing value** is a numeric constant or environment override
compared against a runtime-varying quantity — it appears in a `<`, `>`, `<=`,
`>=`, `.min(`, `.max(`, `saturating_sub`, or a loop/iteration budget — such
that changing it could change which route is chosen, whether a query is
admitted, how much work is done before giving up, or whether the verdict is
`unknown`. Structural constants (bit widths, type-tied sizes, indices) and
`#[cfg(test)]` constants are out.

Each row records name, module, current value, **unit**, what it protects, the
behaviour on exceeding, and where the justification lives with its date.

## Log

- Merged local `main` at `9d40c1ec8`. ADR-1751 and ADR-1752 had landed under
  this lane's brief: the brief's description of `MAX_ONLINE_LRA_ATOMS` and the
  NRA cross-product bound is a snapshot of the state *before* those two lanes.
  The registry records what is in the tree now, not what the brief described.
- The recording mechanism follows the four opt-in, off-by-default guards this
  tree already ships (`TheoryLayerStatsGuard`, `BvLayerStatsGuard`,
  `DlOnlineStatsGuard`, `FrontDoorStatsGuard`), all wired to the single
  existing `--trace` / `AXEYUM_TRACE=1` flag in `smtcomp_cli`. No new CLI
  surface.


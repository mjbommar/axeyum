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


## What the tree actually looks like

113 governing values registered across 19 files. The counts, read from the
registry rather than estimated:

| | |
| --- | --- |
| Entries | 113 |
| **Dated justifications** | **24 (21%)** |
| Undated | 89 (79%) |
| Genuinely stale | 0 |
| Crossing with no branch and no signal (`Signal::None`) | 35 |
| Crossing reported to the caller | 51 |
| Crossing is the normal regime | 27 |
| Constants classified as non-governing | 12 |
| Environment overrides | 2 |

The best-justified entry is `memory_budget::ENCODING_BYTES_PER_CLAUSE`: a table
of measured peaks, the host, a date (2026-08-21), **and a re-measurement test**
so the number can be re-taken rather than re-argued. It is the only entry in the
registry that ships a way to check itself, and it is what the other 112 should
look like.

## Three defects in the staleness checker, all found by its own control

`--registry <path>` runs the check against a deliberately backdated copy. Dating
`MAX_ONLINE_LRA_ATOMS` 2026-08-03 — its real original date — must reproduce the
thirteen-month failure. It did not, three times:

1. **`FIELD_RE` without `re.MULTILINE`** over a multi-line blob: the parser
   returned ZERO entries. Caught by the parser's own self-check against the raw
   `ConfigEntry` literal count, which is the only reason it did not silently
   report a clean bill of health.
2. **`SYM_RE` ending in `\s*\)`** while rustfmt breaks `sym(...)` across lines
   AND adds a trailing comma. Every dated entry parsed with an EMPTY `rests_on`,
   so the checker reported "no dated justification is stale" for all 24 — a
   checker that could not fire, printing exactly what a working one prints. Only
   the control distinguished them.
3. **Flagging a constant's own introducing commit.** ADR-0360 is dated
   2026-07-22 and `5b4c5b404` INTRODUCED all three `MAX_MBQI_FREE_INT_*`
   constants on 2026-07-23. The check called those three stale on its first
   honest run; they are not, and the rule was. Recording a decision and then
   landing the code is the healthy order.

The fix to (3) is deliberately narrow — self-dependency only. `96ff85930`
**introduced** `MAX_LRA_CACHED_COEFFICIENTS`, and that introduction is precisely
what falsified the 2026-08-03 measurement, so excluding introductions in general
would have blinded the checker to its own founding example. The control is what
keeps that honest, and it still fires:

```
crates/axeyum-solver/src/lra_theory.rs::MAX_ONLINE_LRA_ATOMS
  measured 2026-08-03 (ADR-1752), rests on lra_online.rs::MAX_LRA_CACHED_COEFFICIENTS
  but that changed 1 time(s) since:
    96ff85930 2026-08-06 Enforce shared arithmetic resource bounds
```

## Two self-reference bugs in the registry's own tests

Both produced confident, plausible, WRONG failure messages that blamed the
table:

- `registry_len_matches_its_own_source` counted its own needle — 114 literals
  against 113 entries, a perfectly believable off-by-one.
- `consulted_keys_are_registered` matched the `note_consulted(` call quoted
  inside its own scanner and reported two fragments of Rust as unregistered
  keys.

A check that reads the file it lives in has to exclude itself, and neither
exclusion was obvious until the check ran.

## The deletion test

Removing `simplex::MAX_PIVOTS`'s entry killed **exactly one** test —
`every_governing_constant_is_registered` — with 10 passed, 1 failed. Restored
and re-verified green at 11 passed.

## No verdict moves

155 files across `corpus/micro` and `corpus/regression`, recording off and on
under an identical 8 s budget: **zero verdict differences**.

That A/B also produced a negative result worth recording: **none of the 155
printed a `consulted=` field**, because those queries are all decided before
reaching an instrumented gate. An instrument nothing has been shown to reach is
indistinguishable from one that does not work, so the wiring is proved by
`an_instrumented_gate_records_through_the_real_path`, which drives a real
`simplex::Incremental::new` under the guard, rather than by the corpus sweep.

The digest does move when the configuration does, which is the property the
line exists for:

```
; config digest=4012a66affb29582 entries=113 dated=24
; config digest=54d44550118f7752 entries=113 dated=24 env:AXEYUM_NRA_ADMISSION=legacy
```

## Findings recorded, not fixed

Per the scope rule, each is registered with evidence and left in place. The
seven are listed in ADR-1762; the two that most resemble the failures this lane
was opened for:

- **`auto::INT_REAL_RELAX_BUDGET_SHARE`** — when the intended one-sixth share
  underflows to zero the code returns the caller's config UNCHANGED, the full
  unshrunk timeout, rather than skipping the refuter or clamping to a floor. The
  sharing policy is bypassed silently at exactly the small-budget end where
  starvation matters most.
- **`dl_online::MAX_DL_ATOMS`** — a size refusal and a structural "not
  difference-shaped" decline share one `None` return, so no trace can attribute
  the route change to the bound. The same class as the unit mismatch ADR-1751
  fixed: a gate whose meaning is lost at the boundary.

## What did not get done

- **Coverage is 19 files, not the workspace.** `axeyum-cnf`'s two CDCL cores
  (~40 further governing values, enumerated but not registered), `axeyum-bv`,
  `axeyum-aig` and most of `axeyum-search` are not claimed, and their absence
  from `GOVERNED_FILES` is the statement of that gap rather than a silence.
- **Only four gates are instrumented.** The `consulted` field describes those;
  `digest`/`entries`/`dated`/`env:` describe the configuration in force, which
  is the part that makes a run reproducible.
- **The staleness check is not wired into an aggregate gate.** It is runnable
  and green; that decision belongs with the lanes that own those gates.
- **`scripts/gen-plan.py` was not run**, per the brief. `gen-plan.py --check`
  passes with this lane's status file removed and fails with it present, so the
  regeneration is owed at merge and is caused by nothing else.

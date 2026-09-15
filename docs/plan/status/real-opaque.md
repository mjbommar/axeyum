# Lane: real-opaque — the real collector can hold a term, and the sat exits close by type

<!-- plan-section: lane-status -->

**Closed** (real-opaque, 2026-09-14). [ADR-2065] builds [ADR-2050]'s cause (A):
`lra.rs::linearize` refused the WHOLE query the moment it met a real subterm it
could not linearize — in `AUFLIRA`, an application of a *declared* `log` /
`divide` or an array read `(select a i)`, all plain opaque reals. The integer
mirror had shipped for months; the real `Collector` was keyed by `SymbolId` and
structurally could not hold a term.

**The `Sat` exits were enumerated FIRST**, as [ADR-2050] required, by
construction site rather than by `?`-scan: **9 production sites** across
`lra.rs` and `dpll_lia.rs`. Two are reachable from an abstracted system and both
close on `has_opaque_vars()` before the model is built; a third closes three
ways; and the conflict oracle returns `LraOpaqueOutcome`, which has **no `Sat`
variant at all**, so no single-hunk mutant of the design yields a wrong `sat`
and the one that would does not compile.

**Shipped ON** with `AXEYUM_LRA_OPAQUE_APPS=0` as the kill switch (INVERTED
polarity, as [ADR-2025]'s is). Measured on the pinned 200-file `AUFLIRA` parity
list, interleaved per file, one binary and two env values: **+14 rows, 0
losses, 0 flips, 0 exit-status regressions**, 14/14 STABLE-GAIN over three
passes per arm, 14/14 agreement with `:status`, z3 AND cvc5 at a comparable
denominator of 14/14 on each, against a same-arm noise floor of **0 of 200** and
a `QF_LRA` control of **0 of 200**.

**[ADR-2050]'s simulated +6 was a FLOOR.** All six of its witnesses convert on
shipped code, plus eight rows the simulation never looked at. This lane's own
pre-registered P3 predicted fewer than six and was wrong in the conservative
direction.

## What a later lane should know

- **`lira-dpll` decides NONE of the converted rows.** The refusal sat upstream
  of several rungs: `q:mbqi-quick` takes 8 and `q:bool-skeleton` takes 6. A
  mechanism column watching the route that refuses reads `absent` in both arms —
  this lane wrote that column first and the preflight caught it.
- **The cost is on the rows that did NOT move: 1.33x.** Admitting an atom stops
  the ladder refusing early, so on a query it still cannot decide it now spends
  more budget before giving up. The converted rows are 0.03x (73.3 s → 2.2 s).
  A verdict count cannot see either, which is what the exit-status channel and
  the wall-clock split are for.
- **[ADR-2050]'s open design question is answered by PLACEMENT, not a guard.**
  Its simulation rewrote the FILE, which is why the abstracted query reached
  `dl-online`. Nothing rewrites the query here; the abstraction lives inside one
  conjunctive oracle's column space.
- **The control's non-vacuity had to be OBSERVED.** `QF_LRA`'s undecided rows
  are bound by `nra` (45) and `NONE` (41), not by an `lra` route, so "the
  changed code runs here" was not an inference this lane was entitled to;
  `control-executes.sh` measures `lra::decide_within` running on 6 of 20 probed
  rows instead.
- **Two method findings.** The first `Sat`-exit enumerator cut each file at its
  FIRST `#[cfg(test)]` line, which in both files marks a helper in the MIDDLE:
  it discarded 2,397 and 3,133 production lines, including a whole
  `CheckResult::Sat` construction, and printed a clean-looking enumeration of
  the accepted subset. And the first guard-deletion run came back FIVE SURVIVORS
  OUT OF FIVE — the guards are NESTED and all produce a non-`sat`, so
  `!matches!(.., Sat)` passes with any one deleted. The fix was to make each
  guard NAME itself and assert the name.
- **Causes (B) SELECTION, (C) SILENT HANG and (D) of [ADR-2050] are untouched.**
  `QF_UFLRA` is reported as far as it got and is a secondary, not a control.

[ADR-2025]: ../../research/09-decisions/adr-2025-the-refutation-was-available-before-instantiating-and-we-dropped-the-assertion-carrying-it.md
[ADR-2050]: ../../research/09-decisions/adr-2050-the-eleven-are-four-causes-and-the-largest-is-one-refused-atom.md
[ADR-2065]: ../../research/09-decisions/adr-2065-the-real-collector-can-hold-a-term-and-the-sat-exits-close-by-type.md

<!-- plan-section: landed-changes -->

| 2026-09-14 | `7df00fd82` | The real `Collector` gains an opaque-column map keyed by `TermId`, a shared column allocator, and both `Decision::Sat` exits closed on `has_opaque_vars()`. The opaque entry point returns `LraOpaqueOutcome`, which has no `Sat` variant. Two latent column-space bugs fixed: `nvars` from `vars.len()` and `simplex_fallback`'s position-keyed model. |
| 2026-09-14 | `7b9713024` | Pre-registration, and the mechanical `Sat`-exit enumeration — plus the correction of the enumerator that was silently measuring the accepted subset. |
| 2026-09-14 | `aceb6c5ac` | The 20-test soundness-negative suite, registered at L0 in `hooks/pre-push`: six witnesses, a non-vacuity control beside each, congruence and read-over-write as the wrong-verdict directions, and a pin test that re-derives the `Sat`-site counts from the source. |
| 2026-09-14 | `6ca42ce09` | The simplex guard returns a NAMED decline instead of `Ok(None)`, so deleting it is observable — and it is strictly cheaper, since the elimination would have decided the same abstracted system feasible and declined again. |
| 2026-09-14 | `edb12ee75` | The collector's fourth `bool` becomes `OpaqueReals::{Refuse, Abstract}`, mirroring `IntCollector::record_touches`. Clippy 888/888, 0 diagnostics. |
| 2026-09-14 | `2de0df23b` | The A/B: `AUFLIRA` +14/0/0, the 3-pass stability table, the three-authority verification at 14/14 each, the same-arm noise floor and the `QF_LRA` control with its measured non-vacuity. |

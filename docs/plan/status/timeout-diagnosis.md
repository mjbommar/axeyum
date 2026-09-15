# Lane: timeout-diagnosis (ADR-2060)

Status: complete — merged-ready
Owner: `AXEYUM_AGENT=timeout-diagnosis`
Branch base: `91c721f8e` (local `main`'s HEAD; `git merge-base main HEAD` equals it)
Decision: [ADR-2060](../../research/09-decisions/adr-2060-the-give-up-variant-could-not-tell-six-gates-apart-and-nothing-asked-it-to.md)

## What this lane was

[ADR-2045] found `lra.rs:159` attaching ONE sentence —
`"lra: Fourier–Motzkin elimination exceeded the wall-clock / size budget"` — to
every `Decision::TimedOut`, measured that **34 of 34** `QF_LRA` rows wearing it
had `cube_matrices=0` (the elimination had never run), and **declined to fix it**
because it is two changes: give the variant a detail, *and* stop routing an
`i128` overflow through a timeout variant.

Both are done. The lane is a **correctness-of-diagnosis** fix on a
soundness-adjacent path and carries **no capability lever**; it is not measured
in files decided.

## What landed

- `Decision::TimedOut` → `Decision::GaveUp(GaveUp)`, five variants, one per
  gate; two of them carry a nested `(FmDecline, SimplexDecline)` pair because
  reaching the simplex means the elimination already declined and the honest
  answer is two facts.
- `ctx.overflow` → `Decision::Incomplete` / `UnknownKind::Incomplete`. The one
  `UnknownKind` this change moves.
- Three cause-erasing chokepoints below it typed: `eliminate`
  (`Result<_, ElimBail>`, was a bare `None` for **eleven** bail points),
  `simplex_fallback` (`Result<Decision, SimplexDecline>`, was one `Ok(None)` for
  five), `collect_constraints` (`Result<Collector, CollectDecline>`, was one
  `Ok(None)` the caller re-read the clock to disambiguate).
- Every false doc comment fixed in the same change, starting with the variant's
  own — the string was only its echo.
- Four pinning tests; the guard deletion the brief asked for goes from **0 tests
  killed to 2**.

## The enumeration

The six sites ADR-2045 named are correct as a count of `Decision::TimedOut`
constructions — the compiler confirms exactly six — and wrong as a count of
producers. The transitive closure over the cause-erasing returns below them is
**28 program points** (27 distinct; one is a funnel) carrying **15 distinct
causes**, of which **one** is the elimination running out of wall clock.
Reproducible with
`bench-results/timeout-diagnosis-20260914/scripts/enumerate-producers.py`.

## Landed changes

| SHA | what |
|---|---|
| `f6303ee7a` | the variant split + the overflow reroute + the doc fixes |
| `0e7057f4f` | the four pinning tests |
| `2d6a78135` | rustfmt rejoined my continued literals and kept the indentation inside them |
| `3f587710a` | pre-registered A/B rules, before the binaries were built |

## Next for whoever picks this up

- `SimplexDecline::ModelDidNotReplay` and
  `SimplexDecline::CertificateFailedSelfCheck` are countable for the first time.
  Either at a rate above zero on a real board is a finding about a **trust
  anchor**, not about a budget.
- `past_deadline` is `stop_requested() || clock_expired`, so "deadline" still
  covers a portfolio cancellation. Separating them doubles the enum and wants
  its own measurement first.

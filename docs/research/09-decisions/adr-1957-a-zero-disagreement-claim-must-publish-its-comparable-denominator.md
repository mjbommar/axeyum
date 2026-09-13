# ADR-1957: a zero-disagreement claim must publish its comparable denominator, and say so when that denominator is zero

Status: accepted
Index-summary: A soundness board's "0 disagreements" is meaningless unless the number of our verdicts anything else could check is published beside it; when that count is zero the artifact must say so in the same line, because a division we decide nothing in and a division checked ten ways print the identical zero.
Index-status: accepted
Date: 2026-09-13

## Context

Every head-to-head board in this repository ends with a soundness claim of the
form "N verdicts, 0 disagreements". The claim is checked three ways: against
the benchmark's declared `:status`, against z3, and against cvc5.

[board-six](../../../bench-results/six-divisions-headtohead-20260912/README.md)
understood the hazard and wrote it down: *"A zero-disagreement figure over
verdicts nothing else checked is worth nothing"*. It then printed the
comparable counts — 692 of 692 by `:status`, 685 by z3, 681 by cvc5 — and the
zero was real. Its six divisions all had dense ground truth, so the rule was
never tested by a case that violates it.

The Tier-1 board hit that case immediately, on three of seven divisions:

| division | we decide | comparable vs `:status` | vs z3 | vs cvc5 | prints |
|---|---:|---:|---:|---:|---|
| AUFLIRA | 10 | 10 | 10 | 10 | `DISAGREEMENTS: 0` |
| ALIA | **0** | 0 | 0 | 0 | `DISAGREEMENTS: 0` |
| ABV | 4 | **0** | **0** | **0** | `DISAGREEMENTS: 0` |

ALIA is the easy case: we produce no verdicts, so there is nothing to check and
the zero is empty by construction.

ABV is the one that matters. We produce four verdicts. The division declares
`:status unknown` on **199 of its 200 sampled files**, and both references
return `unknown` on all four rows we decide — not by timing out, but by
declining in 0.1 s, confirmed by re-running both at a **600 s** budget. So the
number of our ABV verdicts that anything else can speak to is **zero**, and the
board prints exactly the same `DISAGREEMENTS: 0` that AUFLIRA's ten-of-ten
earns.

Three properties make this worse than an ordinary reporting gap:

1. **It is invisible in the strong direction.** A vacuous zero and a real zero
   are the same characters. A reader scanning seven rows sees seven zeros.
2. **It concentrates where the risk is highest.** The divisions with no ground
   truth are the hard ones, and the files we decide there are precisely the
   ones no independent solver has checked. A wrong `sat` would land in this
   bucket and be reported as a clean row.
3. **The comparable counts being printed elsewhere does not fix it.** They were
   printed, on a separate line, and the vacuity still had to be noticed by a
   human reading two lines together. A number that requires a second number to
   not mislead must carry that number.

## Decision

**A board that reports a disagreement count MUST compute the number of its own
verdicts that at least one independent check could compare against, and MUST
mark the count in the same line when that number is zero.**

1. The comparable denominator is per-check (`:status`, each reference) and is
   published per division, not only as a total. A total hides exactly the
   divisions this ADR is about.
2. When the denominator is zero and the disagreement count is zero, the line
   says so — the Tier-1 board prints
   `DISAGREEMENTS: 0  <-- VACUOUS: nothing checked any verdict we produced`.
   The marker is on the disagreement line itself, not in a footnote, a README,
   or an adjacent row.
3. **The marker is a label, so it gets a label's controls**: a fixture in which
   it MUST appear, a fixture in which it MUST NOT, and a mutant for each
   direction. A label applied to everything is worth as little as one applied
   to nothing, and only the second mutant can tell those apart.
4. A verdict that nothing checked at the board budget is **re-run against both
   references at a much larger budget** into a separate artifact, and the
   re-check's EXIT STATUS depends on the finding. Three outcomes are all
   reportable: confirmed (the board budget was the difference), contradicted (a
   wrong answer, the most important thing a board can find), or still
   unconfirmed (which the board must then state rather than count as a zero).
   The board rows keep their own budget; this is a separate artifact.

## Consequences

- One derived count per division and one conditional string. The inputs are
  already in every board TSV, so this needs no new measurement — the same
  property that made ADR-1941 and ADR-1950 cheap.
- A division can now honestly report "we decide 4 files both references
  decline, and nothing has confirmed them". That is a weaker claim than the
  zero it replaces and a much more useful one: it names four specific files as
  the place to point a model-replay check.
- It does not make a vacuous zero go away. It makes it **impossible to quote by
  accident**, which is the whole of what a reporting rule can do.
- The rule is about the DENOMINATOR, not about arrays or about this board.
  Any future division with sparse `:status` and hard references will trip it,
  and those are exactly the divisions worth building for.

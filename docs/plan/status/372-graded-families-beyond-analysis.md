# Lane 372 — graded statement families beyond analysis

<!-- plan-section: lane-status -->

Status: **COMPLETE** (2026-08-30) — design/measurement lane, no kernel
declarations built, no fact edited.

Extended ADR-0603's graded-statement-family treatment from the four Spivak
real-analysis families (MVT, LUB, Taylor remainder, FTA) to **number theory**
(Stein, Shoup) and **linear algebra** (Boyd–Vandenberghe), the curriculum's two
untreated destinations.

## The central finding

`Nat.le_total`, `Int.le_total`, `Rat.le_total` and `Rat.le_or_lt` are **proved,
axiom-free theorems**, while `CReal.le_total`/`lt_total` are absent (controls:
`CReal.lt_cotrans`, `CReal.apart_cotrans`, FOUND). So the decision principle
that every real-analysis row 2 extracts is *already in the environment* for
ℕ/ℤ/ℚ, and no number-theoretic or rational-linear-algebra statement can have a
row 2 of that kind. That is a positive measurement of emptiness, not a failure
to find one — the distinction ADR-0603 Amendment 4 exists to protect.

Two boundaries survive, and one is **stronger** than anything analysis
produces: the unrestricted least-number principle reduces to *full* excluded
middle (analysis's row 2s reach only LLPO). The other is not a decision
boundary at all but an expressiveness one, and gets its own row.

## Landed

| Change | Path |
|---|---|
| The measurement note: families, rows, targets, both subjects | `docs/curriculum/graded-statement-families-number-theory-and-linear-algebra.md` |
| ADR: row 2 of a decidable subject; introduces **row 2′** | `docs/research/09-decisions/adr-0716-row-two-of-a-decidable-subject.md` |
| Corrected — 3 of 4 "Lean-horizon" theorems are landed | `docs/curriculum/03-destinations/number-theory.md` |
| Corrected — the kernel layer was missing entirely | `docs/curriculum/03-destinations/linear-algebra.md` |
| Lens note: the ✅/◐/✗ tags measure row 3 only | `docs/curriculum/foundational-books/source-tocs.md` |
| Comparison table now separates scenario from kernel layer | `docs/curriculum/DEPTH.md` |

`curriculum.toml` was deliberately **not** touched — see "left open" below.

## Verdicts

Detail moved to [`../notes/372-graded-families-beyond-analysis.md`](../notes/372-graded-families-beyond-analysis.md).


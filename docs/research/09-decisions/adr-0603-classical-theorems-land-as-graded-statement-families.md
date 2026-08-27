# ADR-0603: A classical theorem lands as a graded statement family, not a single row

Status: accepted
Date: 2026-08-27
Index-summary: Each classical theorem is represented by the strongest statement true of each function class — constructive general form, refutation certificate for the boundary, exact form on the decidable fragment, labeled import — one fact per statement, multiple evidence rows where routes overlap.
Index-status: accepted

## Context

Constructive strength varies by function class, and the boundary is itself a
theorem. IVT, worked: for arbitrary uniformly continuous `F`, the exact root
is REFUTED (`creal/ivt.rs`, two kernel-computed counterexamples) and
`ivt_approx` (an ε-root at every accuracy) is provably optimal; for
polynomial/algebraic `F`, zero-testing is decidable and the full
classical-strength statement — a root, named, as a real algebraic number — is
reachable, axiom-free, executable (Sturm isolation shipped; arithmetic layer
in flight). EVT stratifies three ways: attainment refuted in general; the
supremum constructively buildable for uniformly continuous `F`; the polynomial
case fully exact via certified differentiation + Sturm on `F'`. Pretending
these are one theorem proved twice would misstate all of them.

## Decision

A classical theorem's library entry is a FAMILY:

1. **The constructive general form** — the strongest statement for the widest
   class (`kernel-lean`), executable.
2. **The boundary certificate** — where the classical form is constructively
   unavailable, that unavailability is recorded as a refuted fact with its
   counterexample, not as an apology. The refutation is what proves row 1
   optimal.
3. **The exact form on the decidable fragment** — full classical strength via
   the CAS route, kernel-reconstructed per ADR-0601 §2, still axiom-free,
   still executable.
4. **The labeled import** — the classical statement in full generality,
   `imported-kernel-lean`, axiom footprint visible, excluded from headline
   counts (ADR-0601 §3).

One fact per DISTINCT statement. Where classes overlap and two routes prove
the SAME statement, that is one fact with multiple evidence rows (the
existing 2+-checker pattern), never duplicate facts.

## Consequences

- The curriculum map and ledger stop forcing a false choice between "weaker
  theorem" and "classical theorem"; both exist, labeled, with the boundary
  proved.
- Row 2 makes the family self-justifying to a referee: the entry explains WHY
  row 1 is the general ceiling, with a machine-checked certificate.
- Row 3 is the Pareto showpiece per topic and inherits ADR-0601's
  reconstruction requirement — a CAS-internal-only row 3 must read as such.

## Postscript: the four rows stated for MVT, LUB, Taylor remainder, FTA

IVT and EVT had their families stated at acceptance. The 2026-08-27
architecture review §4 named four more theorems still owed this treatment;
[`docs/curriculum/graded-statement-families.md`](../../curriculum/graded-statement-families.md)
states all four rows for each, as measured status rather than aspiration —
including that EVT's own row 2 is itself only "in progress"
(`crates/axeyum-cas/src/extremum.rs`), and that MVT's and LUB's row 2 are
currently asserted unavailability rather than proved refutations.

# Lane NRA-ALGEBRAIC-WITNESS

ADR-2134 — exact replay at an algebraic sample (QF_NRA).

## Status

**In progress, 2026-09-16.** The lever is built and OFF. The larger finding is a
wrong sign in the trusted evaluator, fixed and not behind any lever.

| exit criterion | state |
| --- | --- |
| 1. sizing before code | **MET** — `algebraic-witness` = 7 of the pinned 200, 6 of them `unknown` |
| 2. design claims at `file:line` | **MET** — ADR-2134 §"Design claims" |
| 3. lever, exact replay, root objects, three fixtures, fuzz nonzero | **MET** — fuzz `algebraic_models=855`, 855 agreements, 0 disagreements |
| 4. interleaved A/B | see below |
| 5. mutation | see below |
| 6. gates | see below |

## The finding

`RealAlgebraic::sign_at` decided a polynomial's sign at an algebraic point by
comparing that polynomial's values at the two ENDPOINTS of the isolating
bracket, and returned as soon as they agreed and were nonzero.

Two point samples are not an enclosure of a range. For `α = √2` bracketed by
`(1, 2)` and `q = 25x² − 70x + 48 = (5x − 6)(5x − 8)`:

    q(1) = 3 > 0     q(2) = 8 > 0     q(√2) ≈ −0.995 < 0

The function answered `Pos` for a value that is `Neg` — a wrong sign in a `pub`
API whose doc comment claimed the stronger property the code did not check.

Fixed with an exact Sturm root count over the bracket (`poly_big::RootCounter`),
not with a smaller interval: a small interval is not evidence, a root count is.

**Not a shipped wrong verdict, as far as this lane can show**, and the claim is
not made larger than that. Both existing callers feed `sign_at` polynomials whose
roots all sit in one sorted arrangement, and `sort_roots` declines unless the
isolating intervals are pairwise disjoint — so no root of `q` was ever inside
`α`'s bracket and the endpoint read happened to be sound. That invariant was
external to `sign_at` and not owned by it; this lane adds call sites.

The existing float-oracle property test **structurally could not** have found it:
its box is `c0, c1 ∈ −5..=5`, `c2 ∈ −3..=3`, and `q(1) > 0 ∧ q(2) > 0 ∧ q(√2) < 0`
has no integer solution there — the constraints force `c1 < −4.83` together with
a `c0` confined to an interval of width `< 0.08`. Replaced by an adversarial
family with an algebraic oracle and a non-emptiness assertion.

## Sizing (criterion 1)

Pinned 200 (`bench-results/board-ab-20260915/QF_NRA.tsv`, verified identical to
the prior lane's draw), `--trace`, shipped default arm:

**`algebraic-witness` = 7 of 200; 6 of the 7 are `unknown`, so the mover ceiling
is 6.** Triangulates ADR-2126's 6-of-24-in-bounds and ADR-2131's
5-of-16-admissible; the three have different denominators.

Behind `non-conjunctive`, via the clause loop's slot: the `clause-loop` arm moves
`non-conjunctive` 118 → 109 and DECIDED 19 → 24, and moves `algebraic-witness`
**7 → 7**. That null is weaker than it looks: `record_cad_decline` keeps the
FIRST cause and the loop runs after `non-conjunctive` is already recorded, so an
`algebraic-witness` decline arising inside the loop is masked. The 109
`non-conjunctive` rows are an upper bound that may hide some.

Full table and the seven file names:
`bench-results/nra-algebraic-witness-20260916/README.md`.

## Landed changes

| date | sha | what |
| --- | --- | --- |
| 2026-09-16 | `1a2d58286` | `sign_at` read two endpoint samples as an enclosure — wrong sign at an algebraic point; exact Sturm side condition, three tests, plus this lane's sizing scaffolding (4 files) |

## Next

The A/B, the mutation controls and the gate sweep; then the ship decision.

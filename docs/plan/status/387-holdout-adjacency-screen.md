# 387 — holdout adjacency screen

<!-- plan-section: lane-status -->

**Status: landed.** ADR-0653's adjacency rule was prose that no code enforced.
It is now `guard()`'s **R11**, backed by `scripts/check-holdout-adjacency.py`,
registered in both aggregate gates, and it refuses the exact draw
[ADR-0762](../../research/09-decisions/adr-0762-draw-8-is-declined-one-constant-cannot-open-a-draw-and-the-guard-has-no-adjacency-screen.md)
measured as passing. Decision:
[ADR-0768](../../research/09-decisions/adr-0768-the-adjacency-rule-becomes-r11-and-covers-one-of-three-contamination-shapes.md).
Every measurement, and how to re-run it:
[notes](../notes/387-holdout-adjacency-screen.md).

Reproduced independently before building anything — real `select` + `guard`,
in memory, nothing written:

    before  A  GUARD PASSED -- 340 entries, 120 held-out rows
               NEW held-out: ['natural-bitwise-core', 'natural-gcd-basic']
    after   A  REFUSED: R11 2 new held-out family/families publish mathematics
               a development/train family already publishes (ADR-0653)
    control D  three families -> REFUSED at R5, before and after

**Covers** topical overlap outright (`natural-gcd`, and the ADR-0762 draw).
**Partially** covers a differently-named theorem: `natural-parity` is refused,
but through sibling adjacency rather than statement comparison. **Does not**
cover a definition that decides rows by reduction — `fermat-numbers` measures
4/10, under the allowance, and passes; that is
`check-holdout-closed-evaluation.py`'s job. `natural-binomial` and
`natural-divisibility` are also missed, and the notes say why.

Calibrated in both directions, because with three draws declined a screen that
refuses everything would look exactly as correct as one that works: **all 11
standing held-out families stay clean** across draws 0–7, while development and
train families measure 10/10 on the same signal. Draws 5 and 7 pass; draw 6
added no families.

25 tests, 18 mutations across two suites, **zero survivors**, both exit 0. Six
tests are false-positive controls and three mutations target them.

`check-autogenesis-holdout-isolation.py` →
`held_out=116 files_scanned=1109 settled=0 references=0 PASS`. **Nothing
held-out was touched, reclassified or dispatched**, and no file under
`artifacts/facts/` was written by this lane.

Two reds on this tree are **not** this lane's and are characterised in the
notes: `gen-autogenesis-nursery-refill.py --check` (two totient fact statements,
red at the merge-base, `e79804fdd`/`bab6a4a8d`) and one shell-control orphan
from `279081ea9`.

**Next.** Shape 3 is the open one: `is_closed_evaluation` requires a
binder-free statement, so `∀ (a : ℕ), Nat.nthRoot 0 a = 1` is invisible to it —
which matters for the `Nat.nthRoot` draw-9 candidate specifically.

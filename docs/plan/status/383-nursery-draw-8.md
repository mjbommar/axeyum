# 383 — nursery draw 8

<!-- plan-section: lane-status -->

**Status: DONE — draw 8 is DECLINED, for a reason draw 7's handoff could not
have measured.**
[`check-dispatchable-frontier.py`](../../../scripts/check-dispatchable-frontier.py)
stays RED at **1 dispatchable against a floor of 10**, and no refill can clear
it until **two** constructions land.

Decision record:
[ADR-0762](../../research/09-decisions/adr-0762-draw-8-is-declined-one-constant-cannot-open-a-draw-and-the-guard-has-no-adjacency-screen.md).
Measurements and reproducible probes:
[`../notes/383-nursery-draw-8.md`](../notes/383-nursery-draw-8.md).

Nothing was written. `FAMILY_MODULES`, `FAMILY_ROUTES`, both manifests, the
statable vocabulary, the environment snapshot and the headroom file are
byte-identical to the merge-base; no row moved partition; no attestation count
was raised; no held-out row was touched.

## Draw 7's prediction: half right, and wrong by a whole constant

**Right.** The un-owned floor is down to seven modules — exactly the four draw 7
took, removed — and **not one is held-out-safe**. Each is adjacent to a
published development or train family, or R9-contaminated, or both. Dist is
unchanged at 2/10. Re-derived, not inherited.

**Wrong.** "One more constant" opens nothing. Enumerating all subsets of size
4, 5 and 6 with R5's two-family minimum and every cycle position ≡ 0 mod 3
required to be held-out-safe:

    no new constant                     LAWFUL family sets: 0
    with ONLY Nat.nthRoot declared      LAWFUL family sets: 0
    with ONLY NatCast.natCast declared  LAWFUL family sets: 0
    with Nat.nthRoot AND Squarefree     LAWFUL family sets: 10

Draw 7 could spend one constant because `Mathlib.Data.Nat.Nth` was banked and
clean. It spent Nth too, so the held-out-safe set is **empty rather than one
short**, and R5 is hard-coded at two.

## Both screens, for every candidate

| candidate constant | opens | pool | screen 1 (R9, exact name) | screen 2 (namespace sweep) | closed-eval spent | verdict |
| --- | --- | --- | --- | --- | --- | --- |
| `Nat.nthRoot` | `…Pow.NthRootLemmas` | 13 | **0/10** | **0** declarations | 0 | **clean — the one candidate** |
| `Squarefree` | `Mathlib.Data.Nat.Squarefree` | 11 | **0/10** | **0** declarations | 0 | judged unsafe on adjacency |
| `NatCast.natCast` | `Init.Data.Int.OfNat` | 14 | 0/10 | 0 | 0 | **rejected — omega vocabulary** |
| `Nat.centralBinom` | `…Choose.Central` | 14 | 0/10 | — | **1** | not safe — natural-binomial development |
| `Nat.div2` / `Nat.bodd` | `Mathlib.Data.Nat.Bits` | 14 / 12 | 0/10 | — | 0 | not safe — natural-bitwise development |

Detail moved to [`../notes/383-nursery-draw-8.md`](../notes/383-nursery-draw-8.md).


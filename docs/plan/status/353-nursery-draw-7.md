# 353 — nursery draw 7

<!-- plan-section: lane-status -->

**Status: DONE. The draw is authored and
[`check-dispatchable-frontier.py`](../../../scripts/check-dispatchable-frontier.py)
is GREEN — 4 dispatchable before, 24 after, against a floor of 10.**

Decision record:
[ADR-0654](../../research/09-decisions/adr-0654-draw-7-is-authored-and-the-lawful-family-set-was-forced-not-chosen.md).
Measurements and reproducible probes: [`../notes/353-nursery-draw-7.md`](../notes/353-nursery-draw-7.md).

Draw 6 was declined twice and both declines were right — ADR-0645 because no
held-out-safe family existed, ADR-0653 because the lane that declared the
unblocking constant `Nat.dist` also proved five exact Mathlib mirror names, two
inside the first ten a draw takes. `Nat.fermatNumber` has since landed, which is
the third unblock ADR-0653 measured, and with it a draw exists.

## The family set was forced, not chosen

Enumerating all subsets of the eleven un-owned modules at the `PER_FAMILY`
floor: a subset is lawful iff every cycle position congruent to 0 mod 3 is
held-out-safe and R5's two-family minimum holds. **Exactly one survives.**

| primary module | family | partition | rows |
| --- | --- | --- | --- |
| `Mathlib.Data.Nat.Nth` | `natural-nth-selector` | **held-out** | 10 of 11 |
| `Mathlib.Data.Nat.Prime.Basic` | `natural-prime-arithmetic` | development | 10 of 29 |
| `Mathlib.Data.Nat.Prime.Defs` | `natural-prime-characterizations` | train | 10 of 29 |
| `Mathlib.NumberTheory.Fermat` | `fermat-numbers` | **held-out** | 10 of 13 |

Only two modules are held-out-safe; Fermat sorts last of all eleven so it must
take index 3, which fixes `n = 4`, puts Nth at index 0, and leaves the two Prime
modules as the only things sorting between them. The Prime families are lawful
because they are **not blind** — v1 `natural-primes` is development, and
ADR-0653 states the rule for exactly that case.

`Mathlib.Data.Nat.Dist` is **not** drawn, against ADR-0653's closing
recommendation: it sorts before Nth, so including it either lands it at held-out
(R9 refuses) or displaces Fermat. Forced, not overlooked.

## Both screens, both held-out families

| family | screen 1 (R9, exact name) | screen 2 (namespace, any name) |
| --- | --- | --- |
| `fermat-numbers` | **0/10**, whole module 0/13 | 1 declaration — `Nat.fermatNumber` |
| `natural-nth-selector` | **0/10**, whole module 0/11 | 2 — `Nat.nth`, `Nat.nthAux` |

Positive controls in the same run so a misfiring screen cannot look clean:
`Nat.dist` 8 (the contaminated family), `Nat.gcd` 17, `/[Pp]rime/` 65,
`/dist/i` 40. The sweeps also make ADR-0653's construction-only rule
**measurable** — the `fermatNumber` lane declared the construction and nothing
else, and it shows as a sweep of one.

## Gates

Detail moved to [`../notes/353-nursery-draw-7.md`](../notes/353-nursery-draw-7.md).


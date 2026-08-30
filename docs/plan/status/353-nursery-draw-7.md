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

| check | before | after |
| --- | --- | --- |
| `check-dispatchable-frontier.py` | exit 1, **4** dispatchable | **exit 0, 24** |
| `check-autogenesis-holdout-isolation.py` | `held_out=116 settled=0 references=0 PASS` | `held_out=136 settled=0 references=0 PASS` |
| `gen-autogenesis-nursery-refill.py --check` | **exit 1 — stale on main already** | exit 0, `entries=300 env=2383` |
| `gen-autogenesis-statable-vocabulary.py` | `rows=176 bridge=72 PASS` | unchanged, byte-identical file |
| `check-generated-artifact-ownership.py` | `artifacts=1 producers_run=5 fails=0 PASS` | same |
| `validate-facts.py` | — | 2,262 facts, **0 errors** |
| `check-draw7-frozen-families.py` | — | `frozen=26 moved=0 new=4 control=FIRES PASS` |
| attested / unattested | 411 / 63 | **411** / 103 |

**FROZEN UNCHANGED: True** — 26 preregistered families, 0 moved, and the
negative control fires (mutation-verified: a `compare` that detects nothing
exits 1 with `CONTROL FAILED`).

**No attestation raised** — all 40 new rows are unattested per ADR-0616.
**No held-out row touched** — `nursery-v1.json`, the statable vocabulary, the
environment snapshot and the headroom file are byte-identical to the
merge-base, checked with `git hash-object`.

## Two gates were already red on `main`

Baselined before attributing anything to this lane:

- `gen-autogenesis-nursery-refill.py --check` was RED at the merge-base, proved
  by running the **committed** generator from `git show HEAD:`. Benign
  (`Nat.log2` landed, two screen-rejection counters moved), and committed
  separately so draw 7's diff is attributable to draw 7.
- `check-control-registration.sh` is RED at the merge-base on two hyphenated
  Python files under `scripts/tests/`
  (`check-countrange-bijection-numerics.py`,
  `check-totient-mul-coprime-numerics.py`). Not renamed by this lane, but they
  are two controls that cannot run.

## What the next lane needs

**Held-out supply is exhausted again.** Every remaining un-owned module at the
floor is adjacent to a published v1 family, and Dist is R9-contaminated. Draw 8
needs one more constant, declared **construction-only** per ADR-0653:
`NatCast.natCast` (`Init.Data.Int.OfNat`, 14 rows — judge `Nat.ToInt.*` against
the generator's `HYGIENE` rule first) or `Nat.nthRoot`
(`…Pow.NthRootLemmas`, 13 rows, a genuine well-founded construction).

## Landed changes

| commit | what |
| --- | --- |
| `413415fc2` | early status stub with the re-run probe numbers |
| `635bc8576` | regenerate the extension manifest — it was stale on `main`, not from this draw |
| `29d51bd0b` | draw 7: four families, 40 rows, generator + manifest + 40 fact files |
| _this_ | ADR-0654, the frozen-families checker, status and notes |

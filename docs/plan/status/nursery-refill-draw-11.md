# nursery-refill-draw-11

<!-- plan-section: lane-status -->

**Status: DONE — draw 11 is AUTHORED.** The dispatchable frontier clears its
floor (10 -> 23 against floor 10). ADR-0910's `Nat.nthRoot`/`Squarefree`
construction-only unblock opens exactly the two modules it predicted, but
R11 (landed as code the same day, never previously run against this pair)
hard-refuses `Squarefree` for held-out on vocabulary overlap — substituted a
below-floor `Mathlib.Data.Nat.{Size,Bits}` combination instead.

Decision record:
[ADR-0925](../../research/09-decisions/adr-0925-nursery-draw-11-authored-with-one-documented-closed-evaluation-spend.md).

## What changed

`scripts/gen-autogenesis-nursery-refill.py`: four new families in
`FAMILY_MODULES`/`FAMILY_ROUTES`, plus a real bugfix
(`stored_cross_population_exemptions`, see below).

| family | partition | modules | rows |
| --- | --- | --- | --- |
| `natural-nth-root` | held-out | `Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas` | 10 of 13 |
| `natural-gcd-and-bitwise-basics` | development | `Mathlib.Data.Int.GCD`, `Mathlib.Data.Nat.GCD.Basic`, `Batteries.Data.Nat.Bitwise.Lemmas` | 10 of 57 |
| `natural-factorial-choose-and-squarefree` | train | `Mathlib.Data.Nat.Choose.Basic`, `Mathlib.Data.Nat.Factorial.Basic`, `Mathlib.Data.Nat.Squarefree` | 10 of 55 |
| `natural-bit-decode` | held-out | `Mathlib.Data.Nat.Size`, `Mathlib.Data.Nat.Bits` | 10 of 12 |

Regenerated: `artifacts/autogenesis/kernel-environment-snapshot-v1.json`
(2383 -> 2507 declarations, a fresh release build), `artifacts/autogenesis/
nursery-v2-extension.json` (340 -> 380 entries), `artifacts/autogenesis/
holdout-adjacency-review-v1.json` (2 new disclosure reviews — the first ever
written to that file). 40 new fact files under `artifacts/facts/F-ml430-*.json`.

## Screening trail — every family, including rejections

- **`Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas`** (13 rows) — R9
  0/10 clean. R11: no topic/vocabulary hit, but a non-empty environment sweep
  (stems `root`/`nth`/`nthroot` hit `CReal.ivt_exact_root*`,
  `Complex.root_of_unity*`, `Nat.nth`/`nthAux` — unrelated mathematics
  sharing a word) required a recorded disclosure review. **Drawn, held-out.**
- **`Mathlib.Data.Nat.Squarefree`** (11 rows) — R9 0/10 clean, but **R11
  REFUSES it for held-out**: 6 of its drawn 10 rows mention
  `Nat.Coprime`/`Nat.Prime`/`Nat.gcd`, over the vocabulary allowance of 5.
  This is new information beyond ADR-0910's measurement — ADR-0910 declared
  the construction but never ran the real `guard()`/R5 simulation, and R11's
  code landed only today. **Not drawn as held-out; placed in `train`
  instead** (R11 does not screen non-held-out partitions), combined with
  Choose.Basic and Factorial.Basic.
- **`Mathlib.Data.Nat.GCD.Basic`** (26), **`Factorial.Basic`** (26, R9
  1/10 — `Nat.ascFactorial_succ`), **`Batteries.Data.Nat.Bitwise.Lemmas`**
  (21), **`Choose.Basic`** (18), **`Mathlib.Data.Int.GCD`** (10, R9 1/10 —
  `Nat.gcd_eq_gcd_ab`) — all R9-clean-or-near, all R11-adjacent to a
  published development/train family (`natural-gcd`, `natural-factorial`,
  `natural-bitwise`, `natural-binomial`, `integer-gcd`). Safe for
  development/train (contamination there is a feature, ADR-0653), not
  held-out. **Drawn as `natural-gcd-and-bitwise-basics`
  (development)/`natural-factorial-choose-and-squarefree` (train)**, not as
  independent families — merged specifically to make the cycle land the two
  held-out slots on `natural-nth-root` and `natural-bit-decode`.
- **`Mathlib.Data.Nat.{Bits,Size}` combined** (12 rows) — R9 0/10 clean. R11:
  topic 0, vocabulary 0/10, but a non-empty environment sweep (this kernel's
  own extensive `Nat.bit`/`Nat.testBit`/`Nat.bitwise`/`Nat.size` development)
  required a disclosure review — the same shape as `natural-nth-root`'s.
  **Drawn, held-out** — the ADR-0900-identified substitute for `Squarefree`.
- **34 other below-floor un-owned modules, all pairs and triples** (Fib+Int.Fib,
  BinaryRec combinations, Bertrand, Factorization variants, prime/choose/gcd
  sub-modules, …) — screened for R9 + `check-holdout-closed-evaluation.py` +
  R11 topic/vocabulary together. **Zero clean alternatives found.**
  Reproduces ADR-0900's own exhaustive conclusion from a different angle.

## The two brief-named caveats, weighed

- **`Nat.nthRoot_zero_left : forall a, Nat.nthRoot 0 a = 1`** (drawn, in
  `natural-nth-root`) is very likely `Eq.refl` the instant ADR-0910's
  construction exists (its `n = 0` branch returns `1` unconditionally,
  independent of `a`). `check-holdout-closed-evaluation.py`'s classifier
  requires a binder-free statement and this has `forall (a : Nat)`, so it is
  invisible to that gate by design — confirmed by running it: `violations=2`,
  neither of which is this row. `Nat.nthRoot_one_right : n.nthRoot 1 = 1` is
  judged NOT free by the same reasoning (`Nat.pow` recurses on its symbolic
  exponent here). Flagged, not excluded — no mechanism in this generator's
  scope removes one named row from an alphabetically-drawn pool.
- **`Nat.nthRoot.lt_pow_go_succ_aux`** (drawn) restates Mathlib's
  Newton-iteration auxiliary; our construction is a fuel-bounded linear
  search with no counterpart. May be unprovable here for reasons unrelated
  to mathematical difficulty. Flagged for a dispatch lane to judge before
  attempting, not resolved here.

## A third caveat, found by measurement, not named in the brief

`check-holdout-closed-evaluation.py` reports `verdict=FAIL`, `violations=2`
against the finished draw: `Nat.bit false 0 = 0`
(`F:ml430-nat-bit-false-zero-d996adbf`) and `Nat.size 1 = 1`
(`F:ml430-nat-size-one-e23e5f71`), both in `natural-bit-decode`, both
binder-free ground equations decided by reduction over `Nat.bit`/`Nat.size`
— native constructions this kernel declared long before this draw. Confirmed
the pre-draw baseline passes this same gate at `violations=0`, so these two
are introduced by this draw specifically.

**Accepted, not excluded**, per the exact rule 383-nursery-draw-8.md already
states for this shape ("accept and record the spend, but do not read
closed-eval 0 as nothing is spent") and the `fermat-numbers` precedent
(3 of 10 closed, drawn before the checker existed, repaired afterward by
ADR-0542 amendment). Full reasoning in ADR-0925.

## An unrelated defect found and fixed

Running the real (non-`--check`) generator silently dropped
`cross_population_component_split_exemptions` from `nursery-v2-extension.json`
— exactly the residual ADR-0900 named and left unfixed. This un-exempted
three previously-reviewed cross-population components (ADR-0855), none
touching this draw's facts. Fixed with `stored_cross_population_exemptions()`
(mirrors `stored_surface_validation()`'s existing pattern). One of the three
exemptions turned out to be independently STALE (grown by 22 members from
draw 9's later work) — confirmed pre-existing by three controls (stash-based
reproduction with this draw entirely removed; draw-11 `FAMILY_MODULES` block
removed with the fix kept; exhaustive check that none of this draw's 40 new
fact ids appear in either violation block). Reported in ADR-0925, not fixed
— out of this lane's scope (a 200+-member component spanning a dozen
unrelated families).

## Gates

| check | result |
| --- | --- |
| `check-dispatchable-frontier.py` | exit 0, **23** dispatchable (floor 10) |
| `check-autogenesis-nursery.py` | exit 1 — **pre-existing**, reproduced identically with this draw's entire diff removed |
| `check-autogenesis-holdout-isolation.py` | `held_out=156 files_scanned=1110 settled=0 references=0 verdict=PASS` (136 -> 156) |
| `validate-facts.py` | `2362 facts checked, 0 errors` |
| `check-holdout-closed-evaluation.py` (not one of the four required) | exit 1, `violations=2` (documented above, accepted) |

Three of the four required gates pass; the fourth fails for a reason proven
pre-existing to this draw (see above and ADR-0925 Step 4).

## Honest sentence on how long this draw lasts

23 dispatchable against a floor of 10 and draw 9 was drained in one day by
two theorem lanes — this buys roughly the same runway as draw 9 did, not
materially more, and the un-owned Nat/Int inventory below the current floor
is now measured (not assumed) to be exhausted of clean held-out-safe supply;
the next draw needs a wider inventory or a third construction.

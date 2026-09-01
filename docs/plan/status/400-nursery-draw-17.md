# Lane: nursery-draw-17 — author nursery refill draw 17 and clear the dispatchable floor

<!-- plan-section: lane-status -->

**Your lane's block (`DONE — draw REFUSED`, nursery-draw-17, 2026-09-01).**
Draw 17 is not authored. The `Nat.count` disclosure review is a refusal, and
R5's two held-out families cannot both be honest from today's modules.
Decision: [ADR-1450](../../research/09-decisions/adr-1450-the-count-family-is-not-blind-and-draw-17-is-refused.md).

## Baseline at `b558d9b5a`, each gate run bare

| gate | exit | headline |
| --- | ---: | --- |
| `gen-autogenesis-nursery-refill.py --check` | **0** | `entries=460 env=2829 development=170 held-out=170 train=120 screen_drift=31` |
| `check-autogenesis-holdout-isolation.py` | **0** | `held_out=186 files_scanned=1110 PASS` |
| `check-holdout-adjacency.py` | **0** | 18 held-out families, 0 refused, 4 undisclosed (advisory) |
| `check-dispatchable-frontier.py` | **1** | G7, **2** dispatchable, floor 10 |
| `validate-facts.py` | **0** | — |
| `check-autogenesis-nursery.py` | **1** | pre-existing; output byte-identical before and after this lane |

Three corrections, re-derived rather than inherited: the frontier is **2**, not
3; `--check` is **green** (ADR-1445's freeze fixed ADR-1430's red); and
**ADR-1430's draw does not run as stated** — `MaxPowDiv` yields 7 and
`Factorization.Basic` yields 5 against `PER_FAMILY` 10, so both must be bundles.

## The draw is mechanically authorable; the disclosure is what stops it

    [0] Mathlib.Data.Nat.Count               natural-counting-predicate   -> held-out
    [1] Mathlib.Data.Nat.Factorization.Basic natural-prime-factorization  -> development
    [2] Mathlib.Data.Nat.Log                 natural-logarithm-base       -> train
    [3] Mathlib.Data.Nat.MaxPowDiv           natural-max-power-dividing   -> held-out
    pools 22/10/17/13   select OK 500 entries   R9, R12, R11 topic+vocab CLEAN
    churn over the 460 already-drawn rows: NONE

**`Nat.count` is not blind.** It is a definitional alias of `Nat.countRange`, on
which the kernel carries **22** lemmas (the module doc says 19). Four drawn rows
are the same proposition term-for-term — `count_add`≡`countRange_split`,
`count_le`≡`countRange_le`, `count_mono_left`≡`countRange_le_of_subset` (whose
`Nat.Subset` is *defined* as Mathlib's hypothesis verbatim),
`count_monotone`≡`countRange_le_of_le` — and `count_lt_count_succ_iff` is
entailed by the stronger declared `countRange_succ`. Only `count_injective` is
untouched. R9 reports 0/10 because it compares NAMES. Independently: Mathlib's
`(ℕ → Prop) + DecidablePred` against our `Nat → Bool` is the same type
divergence the registry records for `Nat.nth`, so the mirrors are unclosable
anyway. Both branches disqualify held-out.

**And the partition cannot be repaired.** Exhaustively: 902 subsets of the 10
unowned modules sorting before `Mathlib.Data.Nat.Count` reach the ten-row floor,
**0 viable**. Over all 28 unowned modules there are 240 viable held-out families
at ≤3 modules and every one contains `Count`, `MaxPowDiv` or
`FactorisationProperties` — the last already `do-not-draw-held-out`, and one
module cannot anchor the two families R5 needs. At ≤4 modules with all three
removed: 0 of 9,129. At ≤6: 4, all exactly-10-row bundles sitting at vocabulary
exactly 5/10 (the allowance); one was screened as a full arrangement and is
refused anyway, on topic.

## The finding that outlasts the draw

**A `do-not-draw-held-out` verdict for this exact module was already on record**
(ADR-1100, restated ADR-1115), saying what this lane re-derived — and **nothing
read `refused`.** `screen_family` looks up `reviews[family]`; the refusal was
keyed by a MODULE name, so no lookup the guard performed could reach it.
ADR-1430 then declared `Nat.count` to open that module for a held-out draw and
every screen stayed green.

`assert_draw_lawful` now enforces it, scoped to draw time and to held-out
families (inert on today's manifest, verified). **Four guards, each
mutation-verified in a scratch copy to kill exactly one test, each a different
one**; two of the four aim at the opposite failure, a bar that refuses too much.
Registered in `mutation_controls.py`'s `holdout-adjacency` suite; all six
anchors confirmed unique so no existing mutant becomes AMBIGUOUS.

## Zero-diff, with its negative control

    committed 460 entries, re-derived 460
    entries list byte-identical under canonical_json: True    fact_id sets identical: True
    REAL:    added 0  removed 0  changed 0  partition moves 0
             partitions {development 170, held-out 170, train 120}
    CONTROL: one held-out row flipped to train in an in-memory COPY
             added 0  removed 0  changed 1  partition moves 1  (names the row)
    ZERO-DIFF HOLDS   CONTROL FIRES

## Next

ADR-1420 Route 1 for the third time, and ADR-1450 states the requirement
exactly: declare a construction opening a module that sorts before
`Mathlib.Data.Nat.MaxPowDiv`, is topic- and vocabulary-clean, and leaves room
for two families between it and `MaxPowDiv`. `Factorization.LCM` behind
`Nat.factorizationLCMLeft`/`…Right` is the measured spare and sorts in the right
place — but its window arithmetic is the `LCM`/`MaxPowDiv` one, not the
`Count`/`LCM` one ADR-1430 checked, so re-derive it.

`Nat.count` is not spent: 22 rows of dispatchable work the day a held-out-safe
family sorts ahead of it.

## Did not run

`just check` / `scripts/check.sh` and any `cargo` build — nothing here touches
Rust, and the coordinator re-runs the aggregate gate before merging.

<!-- plan-section: landed-changes -->

| 2026-09-01 | nursery-draw-17 | REFUSED draw 17 and said why: `Nat.count` is a definitional alias of `Nat.countRange` and **4 of 10 drawn rows are the same proposition term-for-term** with a 5th entailed, invisible to R9 (which compares names) and to R11's vocabulary map (which holds only nursery family subjects); independently, the `(ℕ → Prop)+DecidablePred` vs `Nat → Bool` divergence is the one the registry records for `Nat.nth`. Exhaustive: **0 of 902** viable held-out families sort before `Mathlib.Data.Nat.Count`, and all 240 viable families over the whole unowned universe contain one of three anchors, two of which are refused — so R5 cannot be met. Found that a `do-not-draw-held-out` verdict for this module was **already on record and enforced by nothing** (`screen_family` reads `reviews[family]`; the row is module-keyed); `assert_draw_lawful` now enforces it, draw-time and held-out-only, with 4 mutation-verified guards each killing exactly one test. Zero-diff over all 460 drawn rows with a firing negative control. ADR-1450 |

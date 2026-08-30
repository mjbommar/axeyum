# 387 — holdout adjacency screen: every measurement

Detail behind [`../status/387-holdout-adjacency-screen.md`](../status/387-holdout-adjacency-screen.md) and [ADR-0768](../../research/09-decisions/adr-0768-the-adjacency-rule-becomes-r11-and-covers-one-of-three-contamination-shapes.md).

## What it covers, and what it does not

| shape | example | R11 |
| --- | --- | --- |
| topical overlap | `natural-gcd`, and the ADR-0762 draw | **covered** |
| a differently-named theorem | `natural-parity` | **partial** — refused, but through sibling adjacency, not statement comparison |
| a definition deciding rows by reduction | `fermat-numbers` | **not covered** — that is `check-holdout-closed-evaluation.py`'s job |

Retrospective over the five families ever amended out of held-out, each screened
against what was published at or before its own draw:

| family | verdict | signal |
| --- | --- | --- |
| `natural-gcd` | **refused** | topic `GCD`, vocabulary 13/19 |
| `natural-parity` | **refused** | topic `Even`/`Parity`, vocabulary 10/10 |
| `natural-binomial` | clean — **missed** | topic 0, vocabulary 2/20 (its cause was `choose.rs`, not a nursery family; the environment sweep sees it at 28 declarations on `choose`, so a draw today is refused for want of a disclosure) |
| `natural-divisibility` | clean — **missed** | every signal 0 |
| `fermat-numbers` | clean — **missed** | vocabulary 4/10, under the allowance of 5 |

## Calibration — it must not refuse every draw

All **11** standing held-out families come out clean, across draws 0–7; every
one is authored and on `main`. Development and train families measure 10/10 on
the same vocabulary signal, so the separation is real rather than a lenient
threshold. **Draw 5** (1/10 and 1/10) and **draw 7** (0/10 and 4/10) both pass;
**draw 6 added no families** — it was itself a decline — so it has nothing to
screen. Draw 7 passes with a margin of one row, and draw 7 *was* wrong about
`fermat-numbers`, for a shape-3 reason this screen does not cover.

Two design choices were the difference between a screen and a refuse-everything,
both measured:

- **Ambience is derived from the nursery, not from Mathlib frequency.** An
  inventory-frequency rule at 2% calls `Nat.Prime` (390 rows) and `Nat.Coprime`
  (241) ambient — the exact subjects `natural-primes` and `natural-coprimality`
  own. Importance and frequency are the same thing in a mathematical library.
- **Syntax is not mathematics.** `n &&& m` elaborates to `HAnd.hAnd` +
  `Nat.instAndOp`. Without the structural filter, 40 of 42 families come out
  adjacent to something.

## For draw 9

Measured on today's tree, through this gate:

- `Nat.nthRoot` — pool 10, topic 0, vocabulary **0/10**, sweep `root` 9 /
  `nth` 2. **Clean**, and the disclosure is required: the top `root` hit is
  `Complex.root_of_unity_pow`, which is exactly the case a count cannot judge.
- `Squarefree` — pool 10, vocabulary **6/10** on `Nat.Coprime`, `Nat.Prime`,
  `Nat.gcd`. **Refused.** Draw 8 rejected it by hand at 8 of 10 by judgement;
  the mechanical screen reaches the same verdict at 6 of 10.

## Controls

25 tests, 18 mutations across two suites, **zero survivors**, both suites exit
0. Twelve mutations kill exactly one test; the four that kill more are guards
genuinely reached by two tests, or (the one killing four) the held-out scoping
filter, whose removal screens development and train families too. Six of the
twenty-five tests are false-positive controls and three mutations target them
directly.

    python3 scripts/tests/mutation_controls.py holdout-adjacency
    python3 scripts/tests/mutation_controls.py nursery-refill-adjacency

## Gates on this tree

| check | result |
| --- | --- |
| `check-autogenesis-holdout-isolation.py` | `held_out=116 files_scanned=1109 settled=0 references=0 PASS` |
| `check-holdout-adjacency.py` | 11 held-out families, 0 refused, exit 0 |
| `check-holdout-adjacency.py --self-test` | 11 passed, 0 failed |
| `scripts.tests.test_check_holdout_adjacency` | 25 tests, OK |
| `scripts.tests.test_gen_autogenesis_nursery_refill` | 37 tests, OK |
| `check-mirror-statement-fidelity.py` | `facts=2270 mirrors=514 hash_verified=502 unpinned=12 violations=0 PASS` |
| `gen-adr-index.py --check` | `rows=640` exit 0 |
| `check-links.sh` | all links ok |

**Nothing held-out was touched, reclassified or dispatched.** No manifest, fact
or artifact under `artifacts/facts/` was written by this lane.

## Two reds that are not this lane's

- `gen-autogenesis-nursery-refill.py --check` is **red at this lane's
  merge-base** on two totient fact statements
  (`F-ml430-nat-eq-or-eq-of-totient-eq-totient-d4d154c7.json` first) whose last
  touches are `e79804fdd` and `bab6a4a8d`. This lane's diff to that generator is
  purely additive and the drift check runs before `guard()`.
  `check-mirror-statement-fidelity.py` is PASS at violations=0 on the same tree,
  so the two checkers disagree about the same files and someone should reconcile
  them — the refill compares against `preregistered_view`, the fidelity checker
  against the pinned hash.
- `check-control-registration.sh` reports one orphan,
  `scripts/tests/test-ntheory-certificate-guards.sh`, from `279081ea9`.
  `py_orphans=0`, so this lane's control is registered.

## Next

- Shape 3 is the open one: `check-holdout-closed-evaluation.py`'s
  `is_closed_evaluation` requires a binder-free statement, so
  `∀ (a : ℕ), Nat.nthRoot 0 a = 1` — `refl` the moment the construction lands —
  is invisible to it. That matters specifically for the `Nat.nthRoot` draw-9
  candidate, whose own equation lemmas have that shape.
- `natural-divisibility` is missed by every signal. Worth understanding what its
  amendment was actually for before assuming a fourth signal would help.

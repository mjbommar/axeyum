# ADR-0768: The adjacency rule becomes R11, and it covers one of three contamination shapes

Status: accepted
Date: 2026-08-30
Index-summary: ADR-0653's adjacency rule is now code, as `guard()`'s R11 — three signals over a join of every nursery row to the pinned Mathlib inventory, and it refuses the exact draw ADR-0762 measured as returning GUARD PASSED; retrospectively it catches `natural-gcd` and `natural-parity` and MISSES `natural-binomial`, `natural-divisibility` and `fermat-numbers`, so it covers topical overlap outright, a differently-named theorem only where a sibling family publishes the same mathematics, and a definition that decides rows by reduction not at all; calibrated in both directions — all 11 standing held-out families stay clean while development and train families measure 10/10 on the same signal — because with three draws declined a screen that refuses everything would look exactly as correct as one that works

Related: ADR-0542 (held-out isolation and the amendment ledger), ADR-0653
(a family may be blind only if its mathematics is unpublished), ADR-0695
(the construction spends the closed rows, not the evaluation test),
ADR-0762 (draw 8 declined; the guard has no adjacency screen)

Authority for: `scripts/check-holdout-adjacency.py`, `guard()`'s R11 in
`scripts/gen-autogenesis-nursery-refill.py`,
`artifacts/autogenesis/holdout-adjacency-review-v1.json`

## The deficiency

[ADR-0653](adr-0653-declaring-the-unblocking-constant-contaminated-the-family-it-opened.md)
states the rule in one sentence:

> a family may be held out only if its mathematics is not already published by
> an existing development/train family.

[ADR-0762](adr-0762-draw-8-is-declined-one-constant-cannot-open-a-draw-and-the-guard-has-no-adjacency-screen.md)
measured that **no code enforced it**. `guard()` carried ten rules and the
blindness screen, R9, compares a candidate's Mathlib declaration NAME against
the kernel environment. A draw putting `Init.Data.Nat.Bitwise.Lemmas` and
`Mathlib.Data.Nat.GCD.Basic` into **held-out** — beside `natural-bitwise` and
`natural-gcd`, both *development*, both worked by lanes that week — is R9-clean
0/10 on each.

Reproduced independently by this lane, calling the real `select` and `guard`
in memory and writing nothing:

    A  four un-owned modules at the floor, no new constant
       GUARD PASSED -- 340 entries, 120 held-out rows, 12 held-out families
       NEW families placed in held-out:
         ['natural-bitwise-core', 'natural-gcd-basic']
    D  control, three families
       REFUSED: RefillError: R5 the refill adds 1 held-out families

Scenario D is what makes A a finding rather than a broken probe: the same
machinery, one family fewer, refuses and names the rule. `guard` was live and
discriminating; it simply had no adjacency rule to discriminate with.

## Decision

R11 runs `scripts/check-holdout-adjacency.py` over the **new** held-out
families of a draw, scoped exactly as R9 is. Three signals, from a join of
every nursery row to the pinned Mathlib inventory (v1's Mathlib names are
recovered from the fact ledger's `provenance.prior_art`, because v1 entries
carry only an opaque catalog hash):

| signal | question | effect |
| --- | --- | --- |
| `topic` | do the module topic segments coincide with a development/train family's? | refuse |
| `vocabulary` | how many drawn rows are about constants a development/train family publishes? | refuse above `VOCABULARY_MAX_ROWS = 5` of 10 |
| `environment` | does our kernel declare anything about the candidate's subject operators? | **required disclosure** |

An import failure is a **refusal**, not a skip: a draw that could not run the
screen has not passed it.

## Which contamination shapes this covers — and which it does not

Three shapes have occurred and they are different problems. Claiming one screen
covers all three would be worse than shipping a partial screen with the gap
named, so the retrospective is stated in full. Every family below was
preregistered held-out and later amended out of it; each is screened here
against the development/train families published **at or before its own draw**.

| family | amended for | R11 verdict | by which signal |
| --- | --- | --- | --- |
| `natural-gcd` | an operation registered against a held-out fact (ADR-0542) | **refused** | topic `GCD`, vocabulary 13/19 |
| `natural-parity` | a theorem proving the same proposition under a different name, landed five hours before preregistration | **refused** | topic `Even`/`Parity`, vocabulary 10/10 |
| `natural-binomial` | ordinary development in `choose.rs` already proved 5 of 20 | **clean — MISSED** | topic 0, vocabulary 2/20 |
| `natural-divisibility` | (ADR-0542 amendment) | **clean — MISSED** | every signal 0 |
| `fermat-numbers` | three rows decided by reduction when the definition landed (ADR-0695) | **clean — MISSED** | vocabulary 4/10, under the allowance |

So:

- **Shape 1, topical overlap — COVERED.** This is `natural-gcd`, and it is the
  ADR-0762 draw. Both `topic` and `vocabulary` fire on it.
- **Shape 2, a differently-named theorem — PARTIALLY COVERED.**
  `natural-parity` is refused, but *not* because the screen detected the
  differently-named theorem: it is refused because `integer-parity` (train)
  publishes the same mathematics. The screen reaches this case through
  adjacency, not through statement comparison, and it will miss a
  differently-named theorem in a family with no published sibling.
- **Shape 3, a definition that decides rows by reduction — NOT COVERED.**
  `fermat-numbers` measures 4 of 10 on vocabulary, under the allowance, and
  passes. That is `scripts/check-holdout-closed-evaluation.py`'s job and it has
  its own recorded blindness (`is_closed_evaluation` requires a binder-free
  statement, so `∀ (a : ℕ), Nat.nthRoot 0 a = 1` — refl the moment the
  construction lands — is invisible to it). Nothing here narrows that gap.
- **`natural-binomial` is missed and is worth its own line**, because it is
  ADR-0542's headline breach. Its cause was not another *nursery family*; it
  was ordinary hand development in `choose.rs`. The `environment` signal does
  see it — the sweep returns 28 declarations on the stem `choose` — and under
  R11 as adopted a `natural-binomial` draw today would be **refused for want of
  a disclosure**, not for adjacency. That is a weaker catch than a verdict and
  it is the honest description of it.

## Why the environment sweep is a disclosure rather than a threshold

Measuring it is what shows why. `natural-square-root` is a legitimate standing
held-out family and our kernel declares `Nat.sqrt`, `Nat.sqrt_zero`,
`Nat.sqrt_one` — draw 8 compared all four by hand and none is a mirror. A
`natural-nth-root` candidate picks up 9 hits on the stem `root`, of which the
top is `Complex.root_of_unity_pow`: unrelated mathematics that happens to share
a word. No count separates those two situations; a person reading five names
does, in a minute.

So a new held-out family with a non-empty sweep must carry a review in
`artifacts/autogenesis/holdout-adjacency-review-v1.json` before it may be drawn,
and the review must **reproduce the live sweep exactly**. That is what makes it
a disclosure rather than a rubber stamp: a later declaration landing in that
namespace changes the sweep and invalidates the review, rather than passing
silently.

The demand is scoped to draw time. Every standing held-out family was
preregistered before this screen existed; demanding a review for one
retroactively would mean either a red gate on `main` or a review file asserting
diligence nobody performed, and the second is the checker-that-cannot-fail
defect wearing a paper trail. A **stale** review is refused wherever it is
found, because that is a claim someone made.

## Calibration — the screen must not refuse every draw

The queue is at 1 dispatchable against a floor of 10 and three consecutive
draws have been declined, so a screen that refuses everything is
indistinguishable from a broken flywheel and would look exactly as correct as
one that works. Measured on the committed manifests:

- **All 11 standing held-out families are clean**, across draws 0 through 7.
  Every one authored, every one on `main`.
- Development and train families measure 10/10 on the same vocabulary signal —
  the separation is real, not an artefact of a lenient threshold.
- **Draw 5** (`integer-multiplicative-structure` 1/10,
  `descent-and-well-ordering` 1/10) and **draw 7** (`natural-nth-selector`
  0/10, `fermat-numbers` 4/10) both pass. **Draw 6 added no families** — it was
  itself a decline — so there is nothing of draw 6's to screen.
- Draw 7 passes with a margin of one row: `fermat-numbers` sits at 4 against an
  allowance of 5. Draw 7 was **wrong** about `fermat-numbers`, as ADR-0695
  established three days later — but it was wrong for a shape 3 reason this
  screen explicitly does not cover, so passing it is the correct behaviour
  here, not a lucky escape.

Two design choices exist only because they were measured to be the difference
between a screen and a refuse-everything:

- **Ambience is derived from the NURSERY, not from Mathlib frequency.** An
  inventory-frequency rule at 2% classifies `Nat.Prime` (390 rows) and
  `Nat.Coprime` (241) as ambient — the exact subjects `natural-primes` and
  `natural-coprimality` own. In a mathematical library importance and frequency
  are the same thing.
- **Syntax is not mathematics.** `n &&& m` elaborates to `HAnd.hAnd` +
  `Nat.instAndOp`, and `natural-modulus` really is characteristic in
  `Nat.instMod`, so no frequency rule separates plumbing from subject. Without
  the structural filter, 40 of 42 families come out adjacent to something.

## Consequences

- A draw cannot be authored past this rule by trusting `GUARD PASSED`. The
  ADR-0762 scenario now returns `R11 2 new held-out family/families publish
  mathematics a development/train family already publishes`.
- **Draw 9 must re-screen its candidates through this gate before declaring
  anything.** Measured here on today's tree: `Nat.nthRoot`'s pool is **clean**
  (topic 0, vocabulary 0/10, sweep `root` 9 / `nth` 2 — a disclosure is
  required and the `Complex.root_of_unity_pow` hit is the reason to write one),
  and `Squarefree`'s pool is **refused** at vocabulary 6/10 on `Nat.Coprime`,
  `Nat.Prime` and `Nat.gcd`. Draw 8 rejected `Squarefree` by judgement at 8 of
  10 by hand; the mechanical screen reaches the same verdict at 6 of 10, which
  is the point of the exercise.
- Two contamination shapes remain uncovered and are named above. The next
  increment against shape 3 is `check-holdout-closed-evaluation.py`'s binder
  blindness, not this screen.

## Controls

25 tests, 18 mutations across two suites, **zero survivors**. Six of the
twenty-five are false-positive controls and three mutations are aimed at them:
dropping the library-root rule, the syntax filter or the plumbing rule each
makes the screen refuse *more*, and each kills an accepting test. The call site
has its own suite, because deleting `_adjacency_screen(...)` from `guard()`
leaves every screen test green while the rule never runs — which is precisely
the state ADR-0762 found.

    python3 scripts/tests/mutation_controls.py holdout-adjacency
    python3 scripts/tests/mutation_controls.py nursery-refill-adjacency

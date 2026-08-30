# ADR-0762: Draw 8 is declined — one constant cannot open a draw, and the guard has no adjacency screen

Status: accepted
Date: 2026-08-30
Index-summary: Draw 7's handoff predicted draw 8 would need one more construction-only constant, and half of that prediction is right — the un-owned floor is down to seven modules and not one is held-out-safe; but the held-out-safe set is now EMPTY rather than one short, because draw 7 spent the banked `Mathlib.Data.Nat.Nth` too, so enumeration gives zero lawful family sets with either named constant declared alone and draw 8 is declined; `NatCast.natCast` is rejected outright rather than deferred (its fourteen rows are `Nat.ToInt.*` omega transfer lemmas in `Int.Linear.*`'s own normal form), `Squarefree` is measured as a third candidate the handoff never named, and the in-memory `guard` probe shows the deeper problem — a draw putting two DEVELOPMENT-adjacent modules into held-out returns GUARD PASSED, because ADR-0653's adjacency rule is prose that no rule enforces

Related: ADR-0542 (held-out isolation and the amendment ledger), ADR-0615
(the evaluation envelope is per-cohort and a draw is incremental), ADR-0616
(the ceiling counts attestation, not membership), ADR-0620 (held-out supply
is the scarce half of a draw), ADR-0645 (draw 6 declined — no held-out-safe
family left), ADR-0652 (one owner for the statable vocabulary), ADR-0653
(an unblocking lane declares the construction and nothing else), ADR-0654
(draw 7 authored, the lawful family set was forced), ADR-0695 (the
construction spends the closed rows, not the evaluation test)

## Context

`check-dispatchable-frontier.py` fails: **1 dispatchable mirror against a
floor of 10**. That is the lowest it has been — draw 7 left it at 24, and the
twenty prime rows plus most of `fermat-numbers` have closed since. The single
survivor is `F:ml430-nat-fermat-primefactors-one-lt-58343c6f`, and it exists
only because ADR-0695 amended `fermat-numbers` out of held-out.

Draw 7's lane left a prediction, and this ADR's first job was to verify it
rather than inherit it:

> Draw 8 has no held-out supply again. Every remaining un-owned module at the
> floor is adjacent to a published v1 family, and Dist is permanently
> R9-contaminated for held-out. **One more constant**, declared
> construction-only: `NatCast.natCast` (14 rows — judge `Nat.ToInt.*` against
> `HYGIENE` first) or `Nat.nthRoot` (13 rows).

## Decision

**Decline draw 8.** Nothing was drawn: `FAMILY_MODULES`, `FAMILY_ROUTES`, both
manifests, the statable vocabulary, the environment snapshot and the headroom
file are byte-identical to the merge-base. No row moved partition, no
attestation count was raised, no held-out row was touched.

**Record that draw 9 needs TWO constructions, not one**, with the arithmetic
that forces it. **Reject `NatCast.natCast` outright** rather than leaving it
as an option. **Record `Squarefree` as the only measured second candidate**,
with the numbers to overrule this ADR's judgment of it. And **log the guard's
missing adjacency screen** as a first-class deficiency, because it is the
reason this decline is a judgment the tooling could not have made.

Every number is re-derived on this tree. Measurements and reproducible probes:
[`docs/plan/notes/383-nursery-draw-8.md`](../../plan/notes/383-nursery-draw-8.md).

## Every number is re-derived, and two of draw 7's are stale

| quantity | ADR-0645 | ADR-0653 | ADR-0654 | this run |
| --- | --- | --- | --- | --- |
| env declarations | 2,207 | 2,374 | 2,383 | **2,383** |
| bridge constants | 72 | 72 | 72 | **72** |
| un-owned modules at the `PER_FAMILY` floor | 11 | 10 | 11 | **7** |
| dispatchable mirrors before the draw | — | 6 | 4 | **1** |
| held-out rows | — | 116 | 136 | **116** |

The floor going 11 → 7 is exactly the four modules draw 7 took, so the screens
are behaving rather than drifting.

## Half of draw 7's prediction holds, and half is wrong by a whole constant

**Holds.** Seven un-owned modules remain at the floor and **not one is
held-out-safe**. Each is adjacent to a published development or train family,
or R9-contaminated, or both:

| module | rows | R9 | blocked by |
| --- | --- | --- | --- |
| `Init.Data.Nat.Bitwise.Lemmas` | 33 | 0/10 | `natural-bitwise` — development |
| `Batteries.Data.Nat.Bitwise.Lemmas` | 21 | 0/10 | `natural-bitwise` — development |
| `Mathlib.Data.Nat.GCD.Basic` | 26 | 0/10 | `natural-gcd` — development |
| `Mathlib.Data.Nat.Choose.Basic` | 18 | 0/10 | `natural-binomial` — development (ADR-0542's own breach family) |
| `Mathlib.Data.Nat.Factorial.Basic` | 26 | **1/10** | `natural-factorial` — train, and contaminated |
| `Mathlib.Data.Int.GCD` | 10 | **1/10** | `integer-gcd` — train, and contaminated |
| `Mathlib.Data.Nat.Dist` | 18 | **2/10** | contaminated (ADR-0653), unchanged |

**Wrong.** "One more constant" does not open a draw. Enumerating all subsets of
size 4, 5 and 6, with cycle positions ≡ 0 mod 3 required to be held-out-safe
and R5's two-family minimum applied:

    no new constant                    LAWFUL family sets: 0
    with ONLY Nat.nthRoot declared     LAWFUL family sets: 0
    with ONLY NatCast.natCast declared LAWFUL family sets: 0
    with Nat.nthRoot AND Squarefree    LAWFUL family sets: 10

Draw 7 could spend a single constant because `Mathlib.Data.Nat.Nth` was
already banked and clean; it then spent Nth as well. The held-out-safe set is
now **empty rather than one short**, and R5 (`len(new_held_out) < 2` raises) is
hard-coded. One constant produces one held-out-safe module and R5 refuses.

ADR-0695 does not help and it is worth saying why, because the direction is
counter-intuitive: amending `fermat-numbers` out of held-out moved it to
*development*, which removed blind supply. It did not return `Mathlib.NumberTheory.Fermat`
to the drawable pool as an un-owned module — the family still owns it.

## `NatCast.natCast` is rejected, not deferred

Draw 7 flagged `Nat.ToInt.*` to be judged against `HYGIENE`, which already
drops `^Int\.Linear\.` (341 inventory rows) and `^Nat\.Linear\.` (96) as
`omega`'s internal certificate vocabulary. All fourteen rows
`Init.Data.Int.OfNat` would supply are `Nat.ToInt.*`, and the statements decide
it, not the name:

    Nat.ToInt.add_congr    ↑a = a' → ↑b = b' → ↑(a + b) = a' + b'
    Nat.ToInt.le_eq        ↑a = a' → ↑b = b' → (a ≤ b) = (a' ≤ b')
    Nat.ToInt.of_not_le    ↑a = a' → ↑b = b' → ¬a ≤ b → b' + 1 ≤ a'
    Nat.ToInt.sub_congr    … ↑(a - b) = if b' + -1 * a' ≤ 0 then a' - b' else 0
    Nat.ToInt.toNat_nonneg ∀ (x : ℕ), -1 * ↑x ≤ 0

Two tells. The namespace is one uniform schema — "if `a` and `b` transfer, so
does `a op b`" — which is a preprocessing interface rather than a body of
mathematics. And the normal form is `omega`'s own: nonnegativity written
`-1 * ↑x ≤ 0`, a guard written `if b' + -1 * a' ≤ 0`. Nobody writes `0 ≤ x`
that way except a linear-arithmetic certificate producer.

`^Nat\.ToInt\.` therefore belongs in `HYGIENE`. **That one-line edit is not
made here**, for a mechanical reason: it changes the generator's rejection
counters, so `nursery-v2-extension.json` must be regenerated — and
`gen-autogenesis-nursery-refill.py --check` is already red at the merge-base
(below), so regenerating would sweep another lane's in-flight fact edits into
this diff.

## `Squarefree` is the only measured second candidate, and this ADR judges it unsafe

Not named in draw 7's handoff, and found by attributing every
single-missing-constant row to its constant rather than by working from the
handoff's list. `Mathlib.Data.Nat.Squarefree` would yield 11 rows at R9 **0/10**
with a namespace sweep of **0** — clean on both screens.

Judged unsafe on adjacency anyway:

- **Eight of the ten mention `Nat.Prime`, `Nat.Coprime` or `Nat.gcd`**, all
  published by *development* families (`natural-primes` 21, `natural-gcd` 19,
  `natural-coprimality` 10). `Nat.squarefree_iff_prime_squarefree` does not
  merely use primes, it characterises the predicate in terms of them. Draw 7
  permitted **two of ten** `fermat-numbers` rows to mention `Nat.Prime` as
  shared vocabulary and recorded it as the nearest thing to an adjacency in
  that draw; eight of ten, with the defining biconditional among them, is a
  different thing.
- **`Squarefree` is a generic Mathlib predicate** over a monoid
  (`∀ x, x * x ∣ r → IsUnit x`). Declaring that bare name for a `Nat`-only
  specialisation is the `Nat.multichoose` hazard — our body would not be
  Mathlib's `def`.

Recorded with the numbers rather than as a verdict, so a later lane can
overrule it with evidence instead of re-measuring.

## The guard has no adjacency screen, and that is the deeper finding

The real rule, stated in ADR-0653 prose:

> a family may be blind only if its mathematics is unpublished.

Run the actual `select` and `guard` in memory over a family set that violates
it — `Init.Data.Nat.Bitwise.Lemmas` and `Mathlib.Data.Nat.GCD.Basic` into
**held-out**, beside `natural-bitwise` and `natural-gcd`, both *development*,
both worked by lanes today:

    Init.Data.Nat.Bitwise.Lemmas      natural-bitwise-core      held-out
    Mathlib.Data.Nat.Dist             natural-distance          development
    Mathlib.Data.Nat.Factorial.Basic  natural-factorial-basic   train
    Mathlib.Data.Nat.GCD.Basic        natural-gcd-basic         held-out
    select -> 340 entries
    GUARD PASSED -- 340 entries, 120 held-out rows, 12 held-out families

R9 is a **name** screen; both modules are R9 0/10, so nothing fires. The
control in the same run keeps this from being a vacuous observation — the same
machinery with one family fewer refuses:

    REFUSED: RefillError: R5 the refill adds 1 held-out families; the blind
    population is already down to two capabilities

So `guard` is live and discriminating. It simply has no adjacency rule to
discriminate with, and a lane that trusts `GUARD PASSED` can author the
ADR-0542 breach deliberately and see green. That is the checker-that-cannot-fail
shape one arrow upstream from where ADR-0542 found it.

**No screen is added here, and the reason is that a bad one is worse than
none.** The obvious derivations are both defective: a hand-maintained
module → family adjacency table measures the maintainer's memory, which is the
"every X" defect this repository has hit before; and "the new held-out family
shares a constant with a published family's rows" is far too coarse, since
`Nat.pow` and `Nat.le` appear everywhere. A screen wanting a *characteristic*
constant needs a ubiquity threshold, and a threshold chosen to make today's
seven modules come out right is a screen fitted to its own answer. It is logged
as a deficiency with the reproducing probe rather than closed badly under time
pressure.

## Gates — before and after are identical, because nothing was written

| check | before | after |
| --- | --- | --- |
| `check-dispatchable-frontier.py` | exit 1, **1** dispatchable, floor 10 | exit 1, **1** dispatchable, floor 10 |
| `check-autogenesis-holdout-isolation.py` | `held_out=116 files_scanned=1109 settled=0 references=0 PASS` | identical |
| `check-draw7-frozen-families.py` | `frozen=30 moved=0 new=0 control=FIRES PASS` | identical |
| `gen-autogenesis-statable-vocabulary.py` (ADR-0652 owner) | not run against; file untouched | byte-identical |
| attested / unattested | **411 / 103** | **411 / 103** |

**FROZEN UNCHANGED: True** — 30 preregistered families, 0 moved, 0 new, and the
checker's own negative control fires (`control=FIRES`), re-run here rather than
cited from draw 7.

**No attestation was raised**, and none could be: no row was added. Attestation
is read through the generator's own `V1_EVALUATION_ENTRIES + len(validation
["attested"])` and `unattested_cohort`, not counted by hand.

**No held-out row was touched.** `Nat.sqrt_zero` and `Nat.sqrt_one` are
declared here and `natural-square-root` is held-out, so its sixteen rows were
listed and checked; neither name is a mirror of any of them.

## `gen-autogenesis-nursery-refill.py --check` is RED at the merge-base

Established before attributing anything to this lane. At the time of the run
this lane's entire diff against `main` was one new documentation file, so the
generator and every artifact it reads were byte-identical to `main`:

    autogenesis-nursery-refill: 2 fact file(s) disagree with the preregistration;
    first: artifacts/facts/F-ml430-nat-eq-or-eq-of-totient-eq-totient-d4d154c7.json
    has drifted from its preregistration in ['statement']

The two commits touching those files are the totient lane's `105550cdf` and the
repair before it, `e79804fdd`. Left alone — `artifacts/facts/` is not this
lane's path.

It matters beyond bookkeeping: **the refill generator cannot be run to
completion on this tree**, so even a lawful family set could not have been
emitted today. The in-memory probe bypasses it only because it calls the two
pure functions directly.

## Consequences

- `check-dispatchable-frontier.py` stays RED at **1** dispatchable against a
  floor of 10, and no refill can clear it until two constructions land. The
  honest alternative routes are the eleven structurally blocked mirrors
  (`Nat.multichoose`, `Nat.testBit`, `Nat.minFac`, `Nat.fastFib`), which are
  proof work rather than queue work.
- **Draw 9 needs two constructions, each construction-only.** `Nat.nthRoot`
  (`Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas`, 13 rows, R9 **0/10**,
  namespace sweep **0**, closed-evaluation **0** in the first ten) is the one
  clean candidate. The second is unidentified; `Squarefree` is the only
  measured option and is judged unsafe above.
- **A warning ADR-0695's screen cannot give**, and the `Nat.nthRoot` lane needs
  it: `Nat.nthRoot_zero_left : ∀ (a : ℕ), Nat.nthRoot 0 a = 1` is in the drawn
  ten and is `Eq.refl` the moment the construction is admitted, if it is
  declared with that as its first recursion equation. `is_closed_evaluation`
  requires a *binder-free* statement, so it reports 0 spent. The spend is real;
  only the screen is blind to it. Do not read `closed-eval 0` as "nothing is
  spent" for a definition whose equation lemmas are quantified.
- `Nat.squarefree_two : Squarefree 2` sorts **eleventh** in its pool and so
  misses `pool[:10]` by one position. That is luck, not design — one new name
  sorting before it pulls a closed-evaluation row into the draw. Re-check
  before drawing.
- `Mathlib.Data.Nat.Dist`'s 18 rows remain real supply for development or
  train, and unlike draw 7 the cycle positions now allow it: with two held-out
  modules at indices 0 and 3, Dist fits at 1 or 2. ADR-0653's closing
  recommendation becomes executable at draw 9.
- The guard's missing adjacency screen is logged, not closed. Anyone adding one
  must show it refuses the `Init.Data.Nat.Bitwise.Lemmas` + `Mathlib.Data.Nat.GCD.Basic`
  set above **and** admits draw 7's authored set, or it is fitted to its own
  answer.

# ADR-0654: Draw 7 is authored, and the lawful family set was forced, not chosen

Status: accepted
Date: 2026-08-30
Index-summary: ADR-0645 and ADR-0653 declined draw 6 twice; `Nat.fermatNumber` has since landed, which is the third unblock ADR-0653 measured, and a draw now exists — enumerating all subsets of the eleven un-owned modules at the `PER_FAMILY` floor shows EXACTLY ONE lawful family set, so draw 7 was not selected but derived, `check-dispatchable-frontier.py` goes from 4 dispatchable to 24 against a floor of 10, and the `fermatNumber` lane's compliance with ADR-0653's construction-only rule is now measurable as a namespace sweep returning exactly one declaration

Related: ADR-0542 (held-out isolation and the amendment ledger), ADR-0615
(the evaluation envelope is per-cohort and a draw is incremental), ADR-0616
(the ceiling counts attestation, not membership), ADR-0620 (held-out supply
is the scarce half of a draw), ADR-0645 (draw 6 declined — no held-out-safe
family left), ADR-0652 (one owner for the statable vocabulary), ADR-0653
(declaring the unblocking constant contaminated the family it opened)

## Context

Draw 6 was declined twice, and both declines were correct.

ADR-0645 declined it because no coherent held-out-safe family existed, and
named the exact unblock: declare `Nat.dist` and `Nat.nth`. ADR-0653 declined
it again after both landed, because the lane that declared `Nat.dist` also
proved seven theorems, five carrying exact Mathlib mirror names and two of
those landing inside the alphabetically-first ten a draw takes. R9 therefore
refuses `Mathlib.Data.Nat.Dist` for held-out permanently. ADR-0653 measured
three replacement unblocks and called `Nat.fermatNumber` the cheapest.

`Nat.fermatNumber` has since landed
(`crates/axeyum-lean-kernel/src/nat_prelude/fermat_number.rs`). This ADR is
the draw.

## Decision

**Author draw 7.** Four new families, 40 new rows, two of them held-out.
`check-dispatchable-frontier.py` goes green.

**And record that the family set was not a choice.** It is the unique lawful
one, and that is a stronger statement than "we picked carefully".

## Every number is re-derived on this tree

ADR-0645's readiness figures were honest when written and stale by the time
they mattered. ADR-0653's are already stale too. None are carried:

| quantity | ADR-0645 | ADR-0653 | this run |
| --- | --- | --- | --- |
| env declarations | 2,207 | 2,374 | **2,383** |
| bridge constants | 72 | 72 | 72 |
| un-owned modules at the `PER_FAMILY` floor | 11 | 10 | **11** |
| dispatchable mirrors before the draw | — | 6 | **4** |

The brief for this lane said 6 dispatchable; it was **4** by the time the
lane measured, because two more closed in between. Re-derive, always.

## The family set is forced

A subset of the ready modules is **lawful** iff every cycle position
congruent to 0 mod 3 — the held-out positions, since `assign_partitions`
walks `held-out, development, train` over `FAMILY_MODULES[f][0]` sorted
lexicographically — is occupied by a held-out-safe module, and R5's
two-held-out-family minimum is met.

Enumerated over all subsets of the eleven un-owned modules at the floor,
**exactly one subset survives**:

| primary module | family | partition | generator rows |
| --- | --- | --- | --- |
| `Mathlib.Data.Nat.Nth` | `natural-nth-selector` | **held-out** | 11 |
| `Mathlib.Data.Nat.Prime.Basic` | `natural-prime-arithmetic` | development | 29 |
| `Mathlib.Data.Nat.Prime.Defs` | `natural-prime-characterizations` | train | 29 |
| `Mathlib.NumberTheory.Fermat` | `fermat-numbers` | **held-out** | 13 |

The reason it is forced, in four steps:

1. **Held-out-safe** means R9-clean across the first ten *and* no published
   v1 family over the same mathematics. Exactly two of the eleven qualify:
   `Mathlib.Data.Nat.Nth` and `Mathlib.NumberTheory.Fermat`. The other nine
   are each adjacent to a v1 family that is development or train —
   natural-bitwise, natural-primes, natural-factorial, natural-gcd,
   natural-binomial, integer-gcd — or, for `Mathlib.Data.Nat.Dist`,
   contaminated at R9 2/10.
2. **R5 needs two held-out families**, so `ceil(n/3) = 2` and `n` is 4, 5 or 6.
3. **`Mathlib.NumberTheory.Fermat` sorts last** of all eleven (`NumberTheory`
   > `Data` > `Batteries`/`Init`), so it lands at index `n-1`, which must be
   3. Hence `n = 4`, and `Mathlib.Data.Nat.Nth` must be index 0 — nothing in
   the set may sort before it.
4. **Only two ready modules sort strictly between them**, the two Prime
   modules. They fill indices 1 and 2.

## The Prime families are lawful because they are not blind

Draws 2 through 5 each excluded `*.Prime.*`, and this draw takes two Prime
modules. That is not a reversal. The exclusion was always a **held-out**
exclusion: v1 `natural-primes` is *development*, so a blind prime family
would sit beside published mathematics that lanes actively work — the
natural-division violation.

ADR-0653 states the converse rule directly, for the Dist case:
`Mathlib.Data.Nat.Dist` "remains perfectly good for development or train,
where nothing is blind and contamination is a fast-closure feature rather
than a defect". These two land at development and train.

### Stated limitation

Two of `fermat-numbers`' ten blind rows —
`Nat.fermat_primeFactors_one_lt` and `Nat.pow_of_pow_add_prime` — mention
`Nat.Prime`, and this same draw dispatches twenty prime rows.

That is shared **vocabulary**, not a shared statement: neither name appears
in either Prime pool, and a blind family must be permitted to use developed
tools or nothing could ever be held out. It is recorded rather than waved
past because it is the nearest thing to an adjacency in this draw, and the
next lane should know it was seen and judged rather than missed.

## `Mathlib.Data.Nat.Dist` is not drawn, against ADR-0653's recommendation

ADR-0653 closes by recommending Dist be taken as development or train in the
next draw. It cannot be, and the enumeration is what shows this is forced
rather than an oversight: Dist sorts *before* `Mathlib.Data.Nat.Nth`, so
including it either lands it at index 0 — held-out, which R9 refuses — or
displaces Fermat from index 3. Its 18 rows remain real supply for a draw
whose held-out slots come from elsewhere.

## The `fermatNumber` lane followed ADR-0653's rule, measurably

ADR-0653's general rule was: **a lane sent to unblock a held-out family
declares the CONSTRUCTION and nothing else.** That rule is now testable, and
the namespace sweep is the test:

    fermatNumber  -> 1 env declaration:  Nat.fermatNumber
    Nat.nth       -> 2 env declarations: Nat.nth, Nat.nthAux
    Nat.dist      -> 8 env declarations  (the contaminated family, control)

The `dist` row is the positive control: the same sweep over mathematics we
did prove returns eight, so a sweep returning one is a clean family and not
a misfiring screen. Additional controls in the same run: `Nat.gcd` 17,
`/[Pp]rime/` 65, `/dist/i` 40.

## Both screens, for each held-out family

A name screen is structurally blind to a proposition proved under a
different name (draw 5: `F:ml430-nat-dvd-mul-right` satisfied by a
declaration named `Nat.dvd_mul`), so both are run.

| family | screen 1 (R9, exact name) | screen 2 (namespace, any name) |
| --- | --- | --- |
| `fermat-numbers` | **0/10** (whole module 0/13) | 1 declaration, the construction |
| `natural-nth-selector` | **0/10** (whole module 0/11) | 2 declarations, construction + aux |

**Recorded as a limitation, unchanged from draw 6b:** the environment
snapshot carries names only (`values_indexed=false`), so a true *type*
screen cannot be run from it, and the type-bearing route
(`prelude_theorem_inventory --release`) needs a cold kernel build this lane
did not pay for. A row proved under a wholly unrelated name would be caught
by neither screen run here.

## Gates

| check | before | after |
| --- | --- | --- |
| `check-dispatchable-frontier.py` | exit 1, **4** dispatchable, floor 10 | exit 0, **24** dispatchable |
| `check-autogenesis-holdout-isolation.py` | `held_out=116 settled=0 references=0 PASS` | `held_out=136 settled=0 references=0 PASS` |
| `gen-autogenesis-nursery-refill.py --check` | **exit 1, stale on main** | exit 0, `entries=300 env=2383` |
| `gen-autogenesis-statable-vocabulary.py` | `rows=176 bridge=72 PASS` | unchanged, file byte-identical |
| `check-generated-artifact-ownership.py` | `artifacts=1 producers_run=5 fails=0 PASS` | same |
| `validate-facts.py` | — | 2,262 facts, **0 errors** |
| `check-draw7-frozen-families.py` | — | `frozen=26 moved=0 new=4 control=FIRES PASS` |
| attested / unattested | 411 / 63 | **411** / 103 |

**No attestation was raised.** All 40 new rows are unattested, per ADR-0616;
`attested` is the same 411 list.

**No existing held-out row was touched.** `nursery-v1.json`, the statable
vocabulary, the environment snapshot and the headroom file are all
byte-identical to the merge-base, verified with `git hash-object` rather than
by inspection.

## `check-fast.sh` was baselined, and the comparison is a SET

A failure count from one tree is not evidence: this gate fails 27 steps at the
merge-base. Both trees were run and their FAILED blocks compared as sets.

    baseline (merge-base 4cd995620) failures = 27
    this tree failures                       = 25
    FIXED by this lane: autogenesis-nursery-refill, dispatchable-frontier
    NEW failures introduced by this lane: none

The first pass showed 28, and the set comparison is what made that legible —
a count alone reads as "one step worse" and conceals that two were fixed and
three were new. The three were the maintenance a draw requires, not defects in
the draw: `refill-headroom-v1.json` goes stale by construction when a draw
lands and needs `--remeasure` (and needs to be **committed**, which one of the
proposer's own controls checks), and
`test_check_autogenesis_holdout_isolation` pins the held-out population, moved
116 → 136 to the value the checker itself reports.

## Two gates were already red on `main`, and nobody had run them

Baselined before attributing anything to this lane, which is the rule
`docs/plan` keeps re-learning:

- **`gen-autogenesis-nursery-refill.py --check` was RED at the merge-base.**
  Verified by materialising the *committed* generator with `git show HEAD:`
  and running it — it reported the same staleness and produced exactly the
  diff now committed separately. The cause is benign: `Nat.log2` landed, so
  two rows moved from `not-statable-here` to `held-out-construction`. No
  entry, partition or attestation changed. It is committed on its own so
  draw 7's diff is attributable to draw 7.
- **`check-control-registration.sh` is RED at the merge-base**, on
  `scripts/tests/check-countrange-bijection-numerics.py` and
  `scripts/tests/check-totient-mul-coprime-numerics.py` — both hyphenated
  Python files under `scripts/tests/`, unreachable by both the `test_*.py`
  discovery glob and by `python3 -m unittest`. Not this lane's to rename, and
  left alone deliberately, but they are two controls that cannot run.

This lane's own new checker tripped the same rule and was moved from
`scripts/tests/` to `scripts/` — it is a gate invoked by path, not a
unittest control.

## Consequences

- The dispatchable queue is 24 against a floor of 10. Twenty of those are
  prime rows across a development and a train family, which is ordinary
  closable work.
- Two blind families are banked: `fermat-numbers` and
  `natural-nth-selector`, 20 rows, both clean on both screens.
- **The next draw has no held-out-safe supply again.** Every remaining
  un-owned module at the floor is adjacent to a published v1 family, and
  `Mathlib.Data.Nat.Dist` is R9-contaminated. The unblocks ADR-0653 measured
  and this draw did not spend are `NatCast.natCast`
  (`Init.Data.Int.OfNat`, 14 rows — but judge `Nat.ToInt.*` against the
  generator's `HYGIENE` rule first) and `Nat.nthRoot`
  (`…Pow.NthRootLemmas`, 13 rows, a genuine well-founded construction).
  Either one, declared **construction-only** per ADR-0653, opens draw 8.
- `check-draw7-frozen-families.py` carries its own negative control and was
  mutation-verified: replacing `compare` with one that detects nothing makes
  it exit 1 with `CONTROL FAILED`, not pass quietly.

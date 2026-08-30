# ADR-0653: Declaring the unblocking constant contaminated the family it opened

Status: accepted
Date: 2026-08-30
Index-summary: ADR-0645 declined draw 6 and named `Nat.dist` + `Nat.nth` as the exact unblock, measuring `Mathlib.Data.Nat.Dist` R9-clean 0 of 18; the lane that declared `Nat.dist` also proved seven theorems, five of them exact Mathlib mirror names and two in the first ten a draw takes, so R9 is now 2 of 10 and the family it opened is no longer blind — draw 6 is declined a second time, on a different ground, with three R9-clean unblocks measured for draw 7 and the general rule stated: an unblocking lane declares the CONSTRUCTION and nothing else

Related: ADR-0542 (held-out isolation and the amendment ledger), ADR-0615
(the evaluation envelope is per-cohort and a draw is incremental), ADR-0616
(the ceiling counts attestation), ADR-0620 (held-out supply is the scarce
half of a draw), ADR-0645 (draw 6 declined — no held-out-safe family left),
ADR-0652 (one owner for the statable vocabulary)

## Context

ADR-0645 declined draw 6 because zero coherent held-out-safe families
existed, and named the exact unblock: declare `Nat.dist` and `Nat.nth`.
It measured both candidate modules and reported, for each, **R9 name
screen 0 of 18** and **0 of 11**.

Both constants have since been declared (`nat_prelude/dist.rs`,
`nat_prelude/nth.rs`) and the screen now admits both modules at the
predicted counts. This ADR is the attempt to author the draw.

## Decision

**Decline draw 6 a second time, on a ground ADR-0645 could not have
measured.** Nothing was drawn: `FAMILY_MODULES`, `FAMILY_ROUTES` and all
three manifests are byte-identical to the merge-base, no row moved
partition, and no attestation count was raised.

Record the general rule the incident establishes, and the three measured
unblocks for draw 7.

## What was measured

Every number is re-derived for this run against the current environment
snapshot. **They differ from ADR-0645's and the difference matters**, which
is why that ADR's own numbers are not carried:

| quantity | ADR-0645 | this run |
| --- | --- | --- |
| env declarations | 2,207 | **2,374** |
| bridge constants | 72 | 72 |
| drawable (generator screens) | 2,155 | **2,295** |
| un-owned modules at the `PER_FAMILY = 10` floor | 11 | **10** |
| proposer's "ready families" | 15 | **17** |
| `Mathlib.Data.Nat.Dist` | 18 | 18 |
| `Mathlib.Data.Nat.Nth` | 11 | 11 |

### The unblock contaminated the family it opened

`nat_prelude/dist.rs` declares `Nat.dist` **and seven theorems**. Five carry
exact Mathlib mirror names present in the `Mathlib.Data.Nat.Dist` pool —
`dist_comm`, `dist_self`, `dist_succ_succ`, `dist_zero_left`,
`dist_zero_right` — and **two of those five land in the alphabetically-first
ten**, which is what `select` takes (`pool[:PER_FAMILY]` over a name-sorted
pool). So the R9 name screen for that module is now **2 of 10**, and 5 of 18
across the whole module.

Measured against the real generator rather than argued — `select` and
`guard` run in memory over the current tree, writing nothing:

    GUARD REFUSED: R9 2 held-out candidate(s) already have a declaration of
    the same Mathlib name in the kernel environment, so they are not blind:
    [('natural-distance', 'Nat.dist_comm'), ('natural-distance', 'Nat.dist_self')]

The control that isolates it — same machinery, same four families, Dist
moved to development — passes: `GUARD PASSED -- 300 entries, 120 held-out`.
So R9-on-Dist is the **single** mechanical blocker, and
`Mathlib.Data.Nat.Nth` is fully held-out-safe at **R9 0 of 11**, whole
module 0 of 11.

`Nat.nth` did not contaminate anything: the environment contains exactly
`Nat.nth` and `Nat.nthAux`, and no `Nat.nth_*` lemma.

### The contamination cannot be dodged, and the family cannot be repaired

- **Not by module choice.** `Nat.dist_comm` sorts fourth in the pool. Only
  names sorting *before* it could displace anything, and they displace the
  *tail*, never `dist_comm` itself.
- **Not by a screen change.** `select` has no environment screen, and adding
  one would let Dist draw ten clean rows from its thirteen. That would still
  be wrong: R9 is a proxy for the real rule, which is that a family may be
  blind only if its mathematics is unpublished. Our own development has now
  entered the `dist` family and proved a quarter of it. This is exactly the
  natural-binomial shape ADR-0542 records — ordinary development in
  `choose.rs` spending a held-out family — arriving *before* preregistration
  instead of three days after. R9 is the system working.
- **`Mathlib.Data.Nat.Dist` remains perfectly good for development or
  train**, where nothing is blind and contamination is a fast-closure
  feature rather than a defect.

### There is no replacement second family

R5 is hard-coded (`len(new_held_out) < 2` raises), so a draw needs two.
`Mathlib.Data.Nat.Nth` is one. Of the other nine un-owned modules at the
floor, **all nine are over mathematics a development or train family
already publishes** — the exclusion list draws 2 through 5 each applied
unchanged (`*.Bitwise.*` → natural-bitwise, `*.Prime.*` → natural-primes,
`*.GCD.*`/`Int.GCD` → natural-gcd/integer-gcd, `*.Factorial.*` →
natural-factorial, `*.Choose.*` → natural-binomial).

The un-owned sub-floor remainder is **136 rows across 52 modules**, and the
subset that is both R9-clean and unpublished is still ADR-0645's finding
unchanged: several unrelated questions, none reaching ten. The largest
coherent unpublished groupings are Int natCast/literals
(`Init.Data.Int.Basic`, 6) and the binary-representation cluster
(`Mathlib.Data.Nat.{Bits,BinaryRec,Size}`, 15 clean) — and the second is
**not** held-out-safe, because `Nat.bit` is directly load-bearing for the
open `land_bit`/`lor_bit`/`ldiff_bit` mirrors in `natural-bitwise`, which is
a DEVELOPMENT family lanes are actively working.

### The bridge is not a lever

`bridge == (union of settled row constants) − env`, so a constant enters it
only because a mirror mentioning it was already CLOSED here. It cannot be
widened by choice, and no vocabulary edit can open a family.

## Three measured unblocks for draw 7

ADR-0645's constant sweep, re-derived here with the screen it lacked: a
module counts as newly opened only if its first `PER_FAMILY` rows are also
**R9-clean**. That is precisely the screen `Nat.dist` failed.

| declare | opens | rows | R9 first-10 | nearest adjacency |
| --- | --- | --- | --- | --- |
| `Nat.fermatNumber` | `Mathlib.NumberTheory.Fermat` | 13 | **0/10** | no family names Fermat numbers |
| `NatCast.natCast` | `Init.Data.Int.OfNat` | 14 | **0/10** | `integer-natcast` — held-out |
| `Nat.nthRoot` | `…Pow.NthRootLemmas` | 13 | **0/10** | `natural-square-root` — held-out |
| `Nat.centralBinom` | `Mathlib.Data.Nat.Choose.Central` | 14 | 0/10 | natural-binomial — **development, published** |
| `Nat.div2` / `Nat.bodd` | `Mathlib.Data.Nat.Bits` | 14 / 12 | 0/10 | natural-bitwise — **development, published** |
| `instSubNat` | `Mathlib.Data.Nat.Fib.Basic` | 11 | 1/10 | natural-fibonacci — **train, published** |

The first three are held-out-safe on adjacency (blind beside blind, or no
family at all); the last three are not, and are listed so the next lane does
not re-derive their exclusion.

**`Nat.fermatNumber` is the cheapest**: `F_n = 2^(2^n) + 1` over the existing
`Nat.pow`, and the sweep confirms every other constant in all thirteen rows
is already admissible. `Nat.nthRoot` is a genuine well-founded construction.
`NatCast.natCast` opens fourteen `Nat.ToInt.*` rows, which a next lane should
first judge against the generator's own `HYGIENE` rule that drops
`Int.Linear.*`/`Nat.Linear.*` as `omega`'s internal certificate vocabulary —
`Nat.ToInt.*` may belong in the same category.

## The rule this establishes

**A lane sent to unblock a held-out family declares the CONSTRUCTION and
nothing else.** Every mirror-named theorem it proves alongside is one row
subtracted from the blind population it was sent to create, and R9 will
refuse the family if any lands in the first ten.

The `dist` lane did nothing wrong by its own brief — seven genuine theorems,
each admitted axiom-free, is good work — and the `nth` lane, which declared
only the construction and its auxiliary, produced the family that survives.
The difference was not care; it was that nobody had stated the constraint.

Generalised: **the act of making a proposition statable is not neutral with
respect to whether it can be evaluated blind.** Any unblocking brief must
say so, and the evaluation-test requirement for a new `Definition` is safe
here precisely because a test is not a declaration.

## Consequences

- Draw 6 is not authored, for the second time and for a different reason.
  `FROZEN UNCHANGED: True` asserted directly, with a negative control that
  fires; all three manifests byte-identical to the merge-base;
  `held_out=116 settled=0 references=0 PASS`; attested 411 / unattested 63
  before and after.
- **`check-dispatchable-frontier.py` stays RED at 6 dispatchable against a
  floor of 10, and no draw can clear it.** R5 refuses any `FAMILY_MODULES`
  addition that does not add two held-out families, so the gate is not
  reachable through a refill until a constant from the table above is
  declared. The honest alternative routes are the eleven structurally
  blocked mirrors (`Nat.multichoose`, `Nat.testBit`, `Nat.minFac`,
  `Nat.fastFib`), which are proof work, not queue work.
- `Mathlib.Data.Nat.Dist` should be drawn as **development or train** in the
  next draw. Its 18 rows are real supply; only its blindness is spent.
- The next lane needs exactly **one** more constant, not two:
  `Mathlib.Data.Nat.Nth` is banked and clean.

# 351 — nursery draw 6b

<!-- plan-section: lane-status -->

**Draw 6 is DECLINED a second time, and the reason is new: the unblock
contaminated the family it opened.** Nothing was drawn — `FAMILY_MODULES`,
`FAMILY_ROUTES` and all three manifests are byte-identical to the
merge-base, no row moved partition, no attestation count was raised, and
`FROZEN UNCHANGED` is asserted directly with a negative control that fires.

ADR-0645 named `Nat.dist` + `Nat.nth` as draw 6's exact unblock and measured
`Mathlib.Data.Nat.Dist` at **R9 name screen 0 of 18**. That was measured
before `Nat.dist` existed. `nat_prelude/dist.rs` declares the definition
**and seven theorems**; five carry exact Mathlib mirror names in the Dist
pool, and two of them — `Nat.dist_comm`, `Nat.dist_self` — land in the
alphabetically-first ten a draw takes. **R9 is now 2 of 10.**

Measured against the real generator rather than argued — `select` + `guard`
run in memory, writing nothing:

    GUARD REFUSED: R9 2 held-out candidate(s) already have a declaration of
    the same Mathlib name in the kernel environment, so they are not blind:
    [('natural-distance', 'Nat.dist_comm'), ('natural-distance', 'Nat.dist_self')]

Control, same machinery, Dist moved to development: `GUARD PASSED -- 300
entries, 120 held-out`. So R9-on-Dist is the **single** mechanical blocker
and `Mathlib.Data.Nat.Nth` is fully held-out-safe (**R9 0 of 11**, whole
module 0 of 11 — the environment holds exactly `Nat.nth` and `Nat.nthAux`).

Selection is `pool[:PER_FAMILY]` over a name-sorted pool and `Nat.dist_comm`
sorts fourth, so no module tuple dodges it. Adding an environment screen
would let Dist draw ten clean rows of its thirteen — and would still be
wrong, because R9 is a proxy for the real rule that a blind family's
mathematics must be unpublished, and our own development has now proved a
quarter of `dist`. This is ADR-0542's natural-binomial shape caught at the
door instead of three days later.

R5 needs two held-out families. Of the other nine un-owned modules at the
floor, all nine are over mathematics a development or train family already
publishes — draws 2 through 5's exclusion list unchanged. The un-owned
sub-floor remainder is 136 rows across 52 modules and still several
unrelated questions, none reaching ten.

## Numbers re-derived for THIS draw, not carried

| quantity | ADR-0645 | this run |
| --- | --- | --- |
| env declarations | 2,207 | **2,374** |
| drawable (generator screens) | 2,155 | **2,295** |
| un-owned modules at the floor | 11 | **10** |
| proposer "ready families" | 15 | **17** (generator yields **10**) |

## The rule, and the unblock for draw 7

**A lane sent to unblock a held-out family declares the CONSTRUCTION and
nothing else.** Every mirror-named theorem it proves alongside subtracts a
row from the blind population it was sent to create. The `dist` lane did
good work by its own brief; the `nth` lane declared only the construction
and its auxiliary, and its family is the one that survived. Nobody had
stated the constraint.

Re-derived constant sweep, with the R9 screen ADR-0645's version lacked —
each opens a new un-owned module at the floor whose first ten are clean:

| declare | opens | rows | held-out-safe |
| --- | --- | --- | --- |
| `Nat.fermatNumber` | `Mathlib.NumberTheory.Fermat` | 13 | yes — no family names it |
| `NatCast.natCast` | `Init.Data.Int.OfNat` | 14 | yes — beside held-out `integer-natcast` |
| `Nat.nthRoot` | `…Pow.NthRootLemmas` | 13 | yes — beside held-out `natural-square-root` |
| `Nat.centralBinom` | `…Choose.Central` | 14 | **no** — natural-binomial is development |
| `Nat.div2` / `Nat.bodd` | `Mathlib.Data.Nat.Bits` | 14 / 12 | **no** — natural-bitwise is development |

`Nat.fermatNumber` is cheapest (`2^(2^n)+1` over the existing `Nat.pow`; the
sweep confirms every other constant in all thirteen rows is already
admissible). **Draw 7 needs one more constant, not two** — `Nat.Nth` is
banked and clean — and `Mathlib.Data.Nat.Dist` should be drawn as
development or train, where its 18 rows are still real supply.

`check-dispatchable-frontier.py` stays RED at **6** against a floor of 10,
and **no draw can clear it**: R5 refuses any family addition that does not
add two held-out families. The other honest route is the eleven structurally
blocked mirrors, which is proof work.

Gates: holdout isolation `held_out=116 files_scanned=1107 settled=0
references=0 PASS` exit 0, unchanged; frontier exit 1 and byte-identical
before and after; refill `--check` green (`entries=260 bridge=72 env=2374
attested=411 unattested=63`, unchanged before and after); vocabulary owner
PASS; artifact-ownership gate PASS.

Detail, both screens, the probe and every command:
[`../notes/351-nursery-draw-6b.md`](../notes/351-nursery-draw-6b.md).
Decision: [ADR-0653](../../research/09-decisions/adr-0653-declaring-the-unblocking-constant-contaminated-the-family-it-opened.md).

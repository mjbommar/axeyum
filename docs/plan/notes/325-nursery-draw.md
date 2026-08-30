# Notes: 325-nursery-draw

Detail moved out of [`../status/325-nursery-draw.md`](../status/325-nursery-draw.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

- `integer-multiplicative-structure` — Cooper's divisibility transfers
  plus Int units. The Cooper rows are the same mathematics as
  `integer-division`, `integer-division-boundary-cases` and
  `integer-division-inequalities`, all three already held-out. No family
  names Int units.
- `descent-and-well-ordering` — well-ordering of bounded integer sets,
  Cauchy (forward–backward) induction, Lagrange four squares with
  Euler's identity. `cauchy_induction` is adjacent to
  `natural-induction-and-divisibility` and `range-induction`, both
  held-out; the other two modules have no existing family.

`Mathlib.NumberTheory.{SumTwoSquares,PythagoreanTriples}` were available
and **deliberately declined**: `Int.sq_ne_two_mod_four` is mod-4
arithmetic adjacent to the TRAIN family `integer-modular-equivalence`,
and a mild leak is not worth buying pool slack. Both held-out pools are
therefore exactly 10 with nothing dropped.

Nothing went near `natural-square-root`, now the **only** surviving v1
held-out family.

## The finding — ADR-0620

Held-out supply, not pool size, is what gates a draw. Three screens sit
between "survivor" and "drawable into held-out", and only the first is
visible in the proposer's output:

1. **A module belongs to exactly one family** (`select`'s
   `module_family` is a flat dict). The 193 unused survivors in
   `Init.Data.Int.DivMod.Lemmas` are unreachable because
   `integer-division` owns that module. 2,235 survivors is nowhere near
   2,235 drawable rows.
2. **The generator applies `HELD_OUT_CONSTRUCTIONS` and the proposer
   does not**, so `Mathlib.Data.Nat.Log` (34) and
   `Mathlib.Data.Nat.Sqrt` (24) appear in the ready list and yield
   ZERO. The drawable ready set is **13**, not the 15 reported.
3. **Every remaining large module is over already-published
   mathematics** — gcd, ModEq, Prime, factorial, choose, bitwise, fib,
   Int basics. Fine for development/train, never for held-out.

So both held-out slots came from un-owned sub-floor modules with no
published adjacency. That entire supply is **24 propositions across
eight modules**; this draw took 20. **About four remain, so draw 6
cannot satisfy R5 from un-owned modules at all.** ADR-0620 records that
terminal condition and the three honest routes out of it — declaring
blocking constants, releasing spent owned modules, or amending R5 on the
record — and says explicitly that lowering R5 or putting a published
family into held-out are not among them.

## Verification — every command run in the foreground

| check | before | after |
| --- | --- | --- |
| `check-dispatchable-frontier.py` | exit 0, dispatchable **23**, floor 10 | exit 0, dispatchable **63**, `queue_below_floor: false`, `guard_failures: []` |
| `check-autogenesis-holdout-isolation.py` | `held_out=96 settled=0 references=0 PASS` exit 0 | `held_out=116 settled=0 references=0 PASS` exit 0 |
| `validate-facts.py` | — | 2216 facts, **0 errors**, exit 0 |
| `create-autogenesis-mathlib-nursery-split.py --check` | — | OK, `evaluation=214 development=120 held-out=16 train=78 amendments=4`, exit 0 |
| `gen-autogenesis-nursery-refill.py --check` | — | OK, `entries=260`, exit 0 (idempotent) |
| `propose-nursery-refill.py` | exit 0, 19 ready | exit 0, 15 ready after `--remeasure` |
| `gen-adr-index.py` | — | `rows=614`, exit 0 |
| `gen-plan.py --check` | — | exit 0 |

`nursery-v1.json` was not touched. No entry moved partition. **No
attestation count was raised**: attested stayed 411, unattested went
0 → 63, and the new rows are reported as unattested rather than
inheriting a grade nobody ran for them.

### One pre-existing red, not caused here

`check-autogenesis-nursery.py` fails with *"declared dependency
component crosses evaluation partitions"*. It is **not** from this draw:
that checker walks `nursery-v1.json`'s own 214 entries and the edges
among them, and this draw touched no v1 entry and no existing fact file.
Confirmed by running it in a detached worktree at the pre-draw commit
(exit 1, same message) and at draw 4's commit `474ed7158` (exit 1), so
it has been red for some time.

The three leaking components are all **development ↔ train** and none
touches held-out, so the blind population is not implicated:

- `integer-gcd` (train) ↔ `natural-gcd` (development)
- `natural-binomial` (development) ↔ `natural-factorial` (train)
- `natural-factorial` (train) ↔ `natural-modular-equivalence` (development)

These are `depends_on` edges accumulated by ordinary settlement linking
facts across families. Whoever owns the v1 split should decide whether
the rule or the edges are wrong; this lane did not touch it.

## Next

- **Someone must decide what draw 6 is**, before the queue drains
  again. ADR-0620 names the three honest routes; the cheapest is
  declaring blocking constants, since `instSubNat` alone gates 292 rows
  (ADR-0619).
- **`check-autogenesis-nursery.py` is red on main** and nobody appears
  to be watching it. It is a real gate with a real finding.
- Decide whether to drop `Nat.log`/`Nat.clog`/`Nat.log2` from
  `HELD_OUT_CONSTRUCTIONS` now that `natural-logarithm` is development.
  Doing so unlocks 34 candidates for a development/train family. Left
  alone here on purpose — over-excluding is the safe direction and it
  should be a deliberate choice, not a side effect.

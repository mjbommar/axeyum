# ADR-1045: Draw 12 is declined — a clean second held-out family was not found

Status: accepted
Date: 2026-08-31
Index-summary: Refreshed the environment snapshot (2507 -> 2552 declarations)
and re-ran the real `select()`/`guard()`/`screen_family` against all 32
currently un-owned Nat/Int modules plus every below-floor combination this
lane could construct from them; every one collides in TOPIC or VOCABULARY
with a development/train family (the elementary-number-theory territory is
now almost fully claimed across twelve draws), reproducing and extending
ADR-0900's finding. One genuinely clean, floor-clearing candidate WAS found
by simulation -- `Nat.avg`/`Nat.pair` (two simple, typeclass-free, Prod-free
definitions expressible from existing `Nat.add`/`Nat.mul`/`Nat.lt`/`ite`)
would open `Batteries.Data.Nat.Bisect` + `Mathlib.Data.Nat.Pairing` as one
15-candidate held-out family, R9 0/10 and R11 fully clean (zero topic hits,
zero vocabulary hits, zero environment-sweep hits) -- but R5 needs TWO new
held-out families per draw and a comparably clean second was not found
despite a deliberate search of every module with a single missing bridge
constant; declining rather than forcing a marginal family through, and
naming the exact unblock for the next lane

Related: ADR-0900 (draw 10 declined, the precedent this ADR follows and
re-measures), ADR-0925 (draw 11 authored; also names
`natural-bit-decode`'s later ADR-0542 amendment, confirmed below), ADR-0542
(the amendment ledger -- seven amendments landed since draw 11, all
discussed here), ADR-0762 (draw 8 declined, the construction-only-route
precedent), ADR-0910 (`Nat.nthRoot`/`Squarefree` declared construction-only,
the search methodology this ADR reuses), ADR-0768/ADR-0855 (R11), ADR-0950
(R12, the draw-time closed-evaluation screen)

## Step 1: refresh the environment snapshot

Built `shape_search --release` fresh and regenerated the snapshot:

    ./target/release/examples/shape_search --include-constructed --limit 999999 \
      --kind axiom --kind definition --kind theorem --kind inductive \
      --kind constructor --kind recursor
    -> verdict: FOUND 2552
    python3 scripts/gen-autogenesis-nursery-refill.py --snapshot-from <dump>
    -> KERNEL_ENVIRONMENT_SNAPSHOT|declarations=2552

`env` moved 2507 -> 2552 (45 declarations landed since ADR-0925). Confirmed
this change is inert for the committed manifest: `gen-autogenesis-nursery-
refill.py --check` still reports `AUTOGENESIS_NURSERY_REFILL_OK|entries=380`,
byte-identical to before the refresh -- growing the environment did not shift
which candidates any already-drawn family selects.

## Step 2: the frontier reads 10, exactly at floor, and why

`check-dispatchable-frontier.py` reports **10 dispatchable against the floor
of 10** (not 4, as an earlier brief reported from a lagging branch). The
reason is visible in `artifacts/autogenesis/mathlib-nursery-split-policy-v1.json`:
**seven ADR-0542 amendments landed since draw 11**, each moving a family from
`held-out` to `development` because ordinary hand development (or, in
`fermat-numbers`' and `natural-bit-decode`'s case, R12-shaped closed
evaluation) had already spent it blind:

    2026-08-22  natural-gcd          held-out -> development
    2026-08-25  natural-binomial     held-out -> development
    2026-08-30  natural-logarithm    held-out -> development
    2026-08-30  natural-divisibility held-out -> development
    2026-08-30  natural-parity       held-out -> development
    2026-08-30  fermat-numbers       held-out -> development
    2026-08-30  natural-bit-decode   held-out -> development

The last one is ADR-0925's own named residual, resolved: `natural-bit-decode`
was moved out of held-out (the exact `Nat.bit_false_zero`/`Nat.size_one`
closed-evaluation spend ADR-0925 flagged and declined to fix). Confirmed via
`check-holdout-closed-evaluation.py`: **violations=0** now (was 2 in
ADR-0925), because the two offending rows are no longer held-out and the
checker only screens the held-out population.

Each amendment freed its family's remaining open rows into `development`,
which is dispatchable -- this is *why* the frontier reads 10 rather than
draining further despite five theorem lanes closing ~30 mirrors since draw
11. It is a one-time unlock, not a supply source a future draw can rely on:
the held-out population it drew from (146 rows now, was 156 at ADR-0925,
136 before that) keeps shrinking, and R5 requires every new draw to pay two
families back into it. `check-autogenesis-holdout-isolation.py` also
reports the pre-existing `check-autogenesis-nursery.py` cross-population
failure ADR-0925 named is **resolved**: both now exit 0 (see gates below).

## Step 3: the below-floor un-owned held-out-safe supply, re-measured and still exhausted

Reproduced ADR-0900's methodology directly: imported `gen-autogenesis-
nursery-refill.py` by path, ran its own `select()`'s per-record filter
against every module in the pinned inventory, and tabulated real (not
`propose-nursery-refill.py`'s looser) candidate counts for every module NOT
already in `FAMILY_MODULES`. **32 un-owned modules carry >= 1 real survivor,
totalling 94 candidates; not one individually clears `PER_FAMILY` (10).**
The three largest:

    8  Mathlib.Data.Nat.Fib.Basic
    7  Mathlib.Data.Nat.BinaryRec
    7  Mathlib.Data.Nat.Choose.Bounds

Every combination this lane tried, screened through the REAL
`screen_family` (R11, imported from `check-holdout-adjacency.py`) rather than
by inspection:

    Fib.Basic + Int.Fib.Basic (14 rows)
        -> R9 clean, R11 REFUSED: topic Fib (published by v1's
           integer-fibonacci/natural-fibonacci) -- reproduces ADR-0900 exactly
    BinaryRec + Bitwise (13 rows)
        -> R9 CONTAMINATED 3/10 (Nat.bit_div_two, Nat.bit_false, Nat.bit_true
           already declared) AND R11 refused (topic Bitwise, vocab 9/10
           Nat.bit -- natural-bit-decode is DEVELOPMENT now, so it screens)
    11 small (1-3 candidate) modules combined for volume -- RingTheory.Int.Basic,
    Algebra.Order.Ring.Int, PythagoreanTriples, FieldTheory.Finite.Basic,
    IntervalCases, FactorisationProperties, GCDMonoid.Nat, PrimesCongruentOne,
    Batteries.Data.Nat.Gcd, Factorial.BigOperators, Prime.Infinite (16 rows)
        -> R9 clean, R11 REFUSED: topic Gcd (integer-gcd-algorithm,
           natural-gcd-algorithm), vocab 7/10 (Nat.Prime, Even, Int.gcd,
           Nat.gcd, Nat.Coprime all already published)

Every remaining un-owned module's subject (Choose, Prime, Factorization,
GCD, Fib, Bitwise, Totient, parity) is claimed by a published dev/train
family. This is ADR-0900's finding ("every subject with real supply left is
a subject some published family already owns"), reproduced on a tree with
one more draw's worth of families claimed and TWO more amendments moving
previously-excluded held-out families into the dev/train population R11
screens against (`natural-bit-decode` in particular now blocks any new
attempt at the `Nat.bit`/bitwise topic that ADR-0900's `Bits`+`Size` combo
used to occupy safely). **The below-floor un-owned supply is not merely
thin; every module this lane could find is topically spoken for.**

## Step 4: the construction-only route, searched and one clean candidate found

Followed ADR-0762/ADR-0910's methodology: tabulated, over the FULL pinned
inventory (not restricted to un-owned modules), every candidate row blocked
by exactly one or two missing constants, ranked by how many rows a single
new bridge constant would unlock. Two things this surfaced:

**`Init.Data.Nat.MinMax` (30 real candidates once `Max.max`/`Min.min`/
`Nat.instMax`/`instMinNat` are admissible)** is the single largest
opportunity and a genuinely fresh, unclaimed topic (`Nat.max`/`Nat.min` do
not exist in this kernel -- `CReal.max`/`CReal.min`/`Rat.min` do, plain
`Nat.max`/`Nat.min` do not). It is NOT a simple construction, though:
Mathlib states every MinMax lemma through the `Max`/`Min` typeclass, so the
missing constants are literally `Max.max`, `Min.min`, `Nat.instMax`,
`instMinNat` -- typeclass-elaborated names this generator's `admissible()`
can only satisfy via the accretive vocabulary bridge (which requires an
ALREADY-SETTLED mirror using that exact syntax -- none exists, a
chicken-and-egg gap) or by declaring literal kernel constants under those
unconventional names. Flagged as a real but harder-to-execute unblock, not
pursued further here.

**`Batteries.Data.Nat.Bisect` (`Nat.avg`) + `Mathlib.Data.Nat.Pairing`
(`Nat.pair`) is the clean one.** Both are plain, monomorphic, directly-named
functions -- `Nat.avg a b := (a + b) / 2` and `Nat.pair a b := if a < b then
b*b+a else a*a+a+b` -- expressible today from existing `Nat.add`/`Nat.mul`/
`Nat.lt`/`ite`, no typeclass bridging and no dependency on `Prod` (which this
kernel does not have -- confirmed by inspecting `Nat.unpair`'s Mathlib
signature, which returns `Nat x Nat` via literal `Prod`/`Prod.mk` constants
and is therefore NOT reachable this way; `Nat.pair`, the one-directional
half, has no such dependency and every one of its clean candidates was
checked constant-by-constant to confirm it).

Simulated by adding `{"Nat.avg", "Nat.pair"}` to the environment set and
re-running the real `select()` + `screen_family` (not by inspection):

    SIMULATED (Nat.avg + Nat.pair declared): 15 candidates
      Nat.add_le_pair, Nat.avg_comm, Nat.avg_le_left, Nat.avg_le_right,
      Nat.avg_lt_left, Nat.avg_lt_right, Nat.le_add_one_of_avg_eq_left,
      Nat.le_add_one_of_avg_eq_right, Nat.le_avg_left, Nat.le_avg_right,
      Nat.left_le_pair, Nat.pair_eq_pair, Nat.pair_lt_pair_left,
      Nat.pair_lt_pair_right, Nat.right_le_pair

    R9 (in REAL env already, first 10): 0/10  []
    R11 verdict=clean topic_hits=[] vocab=0/10 vocab_hits=[] env_hits=[]

Zero topic hits, zero vocabulary hits, zero environment-sweep hits -- this
is as clean a candidate as `natural-nth-root` was at ADR-0910, and simpler to
build (two arithmetic one-liners against existing primitives, versus a
fuel-bounded search construction). **This alone is not sufficient**: R5
requires two NEW held-out families per draw, unconditionally, whenever any
family is added (`guard()`'s `if new_entries: ... if len(new_held_out) < 2:
raise`), and this is one.

A second comparably clean candidate was searched for and not found within
this session's budget. Checked and rejected, each verified against the real
screen or by direct inspection of the pinned inventory's constants rather
than by topic-name guessing:

    Nat.divMaxPow (Mathlib.Data.Nat.MaxPowDiv)
        -> only 7 real candidates once declared (not 8, two rows also need
           HPow/instNatPowNat which are not yet admissible) -- below PER_FAMILY
    Nat.doubleFactorial (Mathlib.Data.Nat.Factorial.DoubleFactorial)
        -> 5 candidates free of Finset; module topic segment "Factorial" is
           already published by natural-factorial-choose-and-squarefree (train)
           -- would be R11-refused even at floor
    Nat.factorizationLCMLeft/Right (Mathlib.Data.Nat.Factorization.LCM)
        -> ~10 candidates by count, but every clean one mentions Nat.lcm,
           already published by natural-lcm (development) -- vocabulary
           collision, not screened in detail further since the collision is
           unambiguous from the constant list alone
    Nat.centralBinom, Nat.uniformBell (Bell numbers), Nat.largeSchroder
    (Schröder numbers), Nat.stirlingFirst/Second
        -> either topically owned (Choose) or require Finset.sum/List
           machinery this kernel does not model at that level -- not a
           near-term construction

## Decision

**Decline draw 12.** `FAMILY_MODULES`, `FAMILY_ROUTES`, both nursery
manifests, and every file under `artifacts/facts/` are untouched except for
the environment snapshot refresh (Step 1), which is inert for the committed
manifest (confirmed: `--check` reproduces `entries=380` byte-for-byte). No
family moved partition, no held-out row was touched, and no marginal family
was forced through to manufacture a passing `--check`.

R5's two-new-held-out-family minimum cannot be met honestly this draw. One
verified-clean candidate exists (`Nat.avg` + `Nat.pair`, Step 4); a second
does not, and forcing one of the rejected candidates through would either
fail R9/R11 mechanically or (for the ones that would pass the mechanical
screen only because their statement happens not to mention the overlapping
vocabulary, like a hypothetical narrow slice of `divMaxPow`) still be below
`PER_FAMILY`.

## Gates (current tree, environment snapshot refreshed, no other change)

| check | result |
| --- | --- |
| `check-dispatchable-frontier.py` | exit 0, **10** dispatchable, floor 10 (exactly at floor -- fragile, see Step 2) |
| `gen-autogenesis-nursery-refill.py --check` | exit 0, `entries=380\|env=2552\|development=150\|held-out=130\|train=100` |
| `check-autogenesis-nursery.py` | exit 0, `AUTOGENESIS_NURSERY_OK\|...\|evaluation=214\|blockers=0` + `AUTOGENESIS_NURSERY_CROSS_POPULATION_OK\|...\|v1=216\|v2=380\|components=301` -- ADR-0925's named pre-existing failure is now resolved |
| `check-autogenesis-holdout-isolation.py` | exit 0, `held_out=146\|files_scanned=1110\|settled=0\|references=0\|verdict=PASS` |
| `check-holdout-closed-evaluation.py` | exit 0, `held_out=146\|closed_shaped=0\|violations=0\|...\|verdict=PASS` -- ADR-0925's 2-violation spend is resolved (the family carrying it is no longer held-out) |
| `validate-facts.py` | `2365 facts checked, 0 errors` |

All five of this lane's required gates pass, unconditionally, in the state
this ADR leaves the tree in.

## Consequences

- The frontier floor is not lowered; no existing held-out row is touched; no
  fact was added.
- **The next draw's exact unblock is named precisely**: declare `Nat.avg :
  Nat -> Nat -> Nat` and `Nat.pair : Nat -> Nat -> Nat` in
  `crates/axeyum-lean-kernel` (both simple, directly expressible from
  existing `Nat.add`/`Nat.mul`/`Nat.lt`/`ite`; `Nat.unpair` is NOT reachable
  the same way, since it needs `Prod`, which this kernel does not have --
  build `Nat.pair` alone, not the round-trip pair). That alone opens ONE new
  held-out family (`Batteries.Data.Nat.Bisect` + `Mathlib.Data.Nat.Pairing`,
  15 candidates, verified R9/R11-clean by simulation in Step 4). A SECOND
  construction is still needed to clear R5; `Init.Data.Nat.MinMax` (30
  candidates) is the largest remaining opportunity but needs the harder
  typeclass-bridging route (Step 4) rather than a plain definition, and is
  named here as the next thing to scope, not a confirmed unblock.
- **The held-out population is shrinking under its own success**: seven
  ADR-0542 amendments in the time since draw 11 (Step 2), each a genuine
  case of ordinary development outpacing a preregistered blind family. This
  is not a defect to fix -- it is the flywheel working -- but it means every
  future draw needs to authentically add two NEW held-out families just to
  stand still, and the un-owned Nat/Int Mathlib supply for that (Step 3) is
  now exhausted. Widening the pinned inventory beyond Nat/Int (none exists
  today -- checked `/nas3/data/axeyum/autogenesis/sources/`, only Nat/Int
  inventories at two Mathlib versions) or building held-out-safe
  constructions (Step 4) are the only two ways forward.
- At the observed drain rate (~30 mirrors closed by five theorem lanes since
  draw 11, one drawer's worth of supply consumed roughly every session) and
  with the below-floor un-owned supply now at zero, this draw's decline
  buys no runway by itself -- the frontier stands at 10 (exactly floor) only
  because of the seven amendments in Step 2, which are a one-time release of
  previously-blind rows, not a repeatable supply.

# ADR-1220: The binding slot moved from index 3 to index 0, and two screens nobody had run

Status: accepted
Date: 2026-08-31
Index-summary: Draw 15 consumed the last three free early-sorting families, and
that inverted ADR-1100's positional framing: index 3 is now REACHABLE (six
candidates pass every hard signal, three survive ADR-1160's boundary reading)
and **index 0 is the slot with no free option at all**. Measured exhaustively
over all 265 un-owned modules, 1-, 2-, 3- and 4-element construction subsets,
against the real `select()`/`assign_partitions()`/`screen_family()`/
`is_closed_evaluation`: exactly ONE free family remains
(`Mathlib.NumberTheory.FactorisationProperties`, 15 rows) and it is the only
free family R11 calls clean, while R12 refuses it on two already-spent rows.
Every other free family is R11-refused as held-out. Two screens no prior draw
or unblock lane had run change the answer and are the durable contribution:
**frozen-family drawn-ten CHURN** (declaring `Nat.count` swaps five of
`natural-nth-selector`'s ten) and **stale recorded REVIEW** (declaring
`Nat.ceilRoot`/`Nat.floorRoot` reds `check-holdout-adjacency.py` by moving
draw 11's `natural-nth-root` sweep from 11 `root` hits to 13). The verified
layout needs five constants; this lane landed three of them
(`Nat.unpairLeft`/`unpairRight`/`unpaired`, construction only), taking the
index-0 candidate from three missing constants to two. No draw is authored and
no fact is registered.

Related: ADR-1175 (draw 15, which consumed the three free early families),
ADR-1160 (the index-3 unblock, the nine-candidate search this re-runs, and the
boundary-equation READING), ADR-1115 (the pre-declaration closed-evaluation
check), ADR-1100 (the positional framing this ADR inverts), ADR-1095 (the
`ceil(n/3)` mechanism), ADR-1060 (`Nat.avg`/`Nat.pair`, whose module doc
records `Nat.unpair` as unreachable), ADR-0768 (R11 and its disclosure
review), ADR-0695/ADR-0950 (R12), ADR-0653 (construction-only unblocks),
ADR-0542 (the amendment ledger)

## What this lane was asked to do, and where the brief was wrong

The brief said: make draw 16 possible by finding or building what lets a fifth
family sit at **cycle index 3**, on ADR-1100's framing that "families
constructible with no new work sort EARLY and fill index 0; index 3 needs a
late-sorting one."

That framing was correct when written and is **false today**, because draw 15
spent it. `natural-avg-pair` (`Batteries.Data.Nat.Bisect`), `natural-minmax`
(`Init.Data.Nat.MinMax`) and `natural-stirling-numbers`
(`Mathlib.Combinatorics.Enumerative.Stirling`) were exactly the free
early-sorting supply, and all three are now frozen. What remains free sorts
LATE and is R11-refused; what could sit at index 0 needs a construction.

So the brief's fallback clause — "if nothing can sit at index 3, say so" —
does not describe the situation either. Something can. The measured answer is
the other way round.

## Everything was re-measured; three numbers had moved

`shape_search --release` was rebuilt in this worktree rather than trusted from
a prebuilt binary (the documented stale-index hazard, where a false ABSENT is
the expensive verdict).

- **Environment: 2629 committed, 2685 live.** The min/max and Stirling mirror
  lanes had added 56 declarations after draw 15's snapshot. Refreshed, and
  checked rather than assumed because ADR-1095's own refresh displaced two
  `train` rows: `gen-autogenesis-nursery-refill.py --check` regenerates the
  manifest **byte-identically** under the refreshed snapshot.
- **`G7 queue-below-floor`: 4 dispatchable against a floor of 10.** Reproduced
  from `check-dispatchable-frontier.py`, unchanged from the brief.
- **`check-autogenesis-nursery.py` is RED on `main`, and has been.** Verified
  from a detached worktree at `main` (69eb494e9): identical message, exit 1,
  `2 cross-population partition-leak violation type(s)` over `depends_on`
  components spanning development / train / longitudinal. Nothing held-out is
  involved and nothing in this lane touches its inputs. It is reported here
  because this lane's first read of it used the banned pipeline-`$?` idiom and
  printed a green `exit=0` for a script that exits 1 — the trap CLAUDE.md
  names first, hit on the very check meant to establish a baseline.

`propose-nursery-refill.py` was not used as a candidate space (ADR-1160: it
mirrors only the hygiene screen, and it both over- and under-counts).

## The candidate space, measured exhaustively in both directions

For every un-owned module, the smallest set of currently-inadmissible constants
whose declaration lifts the module's pool to `PER_FAMILY = 10`, computed over
all 1-, 2-, 3- and 4-element subsets of its most-frequent missing constants,
against the real screen. 265 un-owned modules carry at least one candidate.

**Free (k = 0) families — the whole remaining supply:**

| composition | primary module | pool | held-out verdict |
| --- | --- | --- | --- |
| bit representation (3 modules) | `Init.Data.Nat.Bitwise.Basic` | 17 | R9 fail 3, R11 refused (topic `Bitwise`, vocab 9/10) |
| fibonacci (2 modules) | `Mathlib.Data.Int.Fib.Basic` | 14 | R9 fail 1, R12 fail 6, R11 refused |
| prime divisibility (7 modules) | `Mathlib.Data.Int.NatPrime` | 18 | R11 refused (topic + vocab 10/10) |
| binomial bounds (4 modules) | `Mathlib.Data.Nat.Choose.Bounds` | 14 | R11 refused (topic + vocab 10/10) |
| factorization structure (4 modules) | `Mathlib.Data.Nat.Factorization.Basic` | 10 | R11 refused (vocab 9/10) |
| late number theory (8 modules) | `Mathlib.FieldTheory.Finite.Basic` | 17 | R11 refused (vocab 7/10) |
| factorisation properties | `Mathlib.NumberTheory.FactorisationProperties` | 15 | **R9 pass, R11 CLEAN (vocab 4/10)**, R12 fail 2 |

So **exactly one free family is R11-clean**, and R12 refuses it. Its two
failing rows are `Nat.abundant_twelve` (`Nat.Abundant 12`) and
`Nat.deficient_one` (`Nat.Deficient 1`); verified directly rather than through
the screen, `Nat.Abundant`, `Nat.Deficient` and `Nat.Perfect` are all in the
environment, so those two rows are decided by reduction and are spent. Nothing
that can be declared repairs that — declaring more only spends more.

**With constructions, passing every hard signal (R9, R12, R11 with
`require_disclosure=False` so the authorable step does not mask the hard
ones):**

| candidate | primary module | pool | constructions | boundary rows in the drawn ten |
| --- | --- | --- | --- | --- |
| `integer-natcast-ofnat` | `Init.Data.Int.OfNat` | 14 | `NatCast.natCast` | 0 — but see below |
| `natural-decimal-string` | `Init.Data.Nat.ToString` | 34 | `Char`, `Char.ofNat`, `Nat.digitChar` | **10 of 10** |
| `natural-primitive-recursion` | `Mathlib.Computability.Primrec.Basic` | 11 | `Nat.Primrec`, `Nat.casesOn` (+ `Nat.unpaired`, now landed) | **0** |
| `natural-counting` | `Mathlib.Data.Nat.Count` | 22 | `Nat.count` | 0 — refused, see below |
| `natural-factorization-lcm` | `Mathlib.Data.Nat.Factorization.LCM` | 10 | `factorizationLCMLeft`/`Right` | 4, and needs a product over prime factors this kernel cannot state |
| `natural-integer-root` | `Mathlib.Data.Nat.Factorization.Root` | 18 | `Nat.ceilRoot`, `Nat.floorRoot` | **3** |
| `natural-max-pow-div` | `Mathlib.Data.Nat.MaxPowDiv` | 10 | `Nat.divMaxPow`, `padicValNat` | **6** |

The boundary counts are ADR-1160's READING, performed by printing the drawn ten
verbatim rather than inferring from names — which matters, because a name-based
guess put `Factorization.Root` at 5 and the statements put it at 3, reproducing
ADR-1160's figure exactly. `Nat.ceilRoot 1 a = a`, `Nat.ceilRoot 0 a = 0` and
`n.ceilRoot 0 = 0` are the three; `ceilRoot_eq_zero` and `ceilRoot_one_right`
LOOK like boundary rows and are not (an `iff` over both arguments, and a
hypothesis-carrying statement).

Two candidates pass every mechanical signal and must still be refused:

- **`Init.Data.Nat.ToString`.** All ten drawn rows are `digitChar` equations
  (`Nat.digitChar_eq_a`, `Nat.a_eq_digitChar`, …), every one settled by
  reduction against any correct `digitChar`. The ADR-1160 reading in its most
  extreme form: R12 cannot see them because they carry hypotheses.
- **`Init.Data.Int.OfNat`.** Its ten are `Nat.ToInt.*` — `omega`'s internal
  Nat-to-Int preprocessing lemmas, the direct cousins of `Int.Linear.*` and
  `Nat.Linear.*`, which `HYGIENE` excludes by name. `Nat.ToInt.*` is not in
  that pattern. **That is a hygiene gap worth closing**, and it is recorded
  here rather than acted on, because widening `HYGIENE` changes what every
  family draws and is a decision for a lane that owns it. Separately,
  `NatCast.natCast` is a typeclass projection this kernel has no way to
  declare honestly.

`Mathlib.Data.Nat.Count` remains refused on ADR-1100's shape-2 grounds
(`Nat.countRange` already proves five of its rows under other names), and this
lane found a **second, independent reason** — see the churn screen below.

## The two screens nobody had run, and both change an answer

Every prior draw and unblock ADR screens a candidate against R9, R11 and R12.
None of them asks what DECLARING the construction does to the families that are
already frozen. Two things can happen, and both did.

### Frozen-family drawn-ten churn

`select()` regenerates every entry on every run, taking `pool[:10]` in name
order. A new constant that makes a previously-unstatable row statable can
insert itself ahead of a frozen family's drawn ten. Measured by diffing each
frozen family's drawn ten with and without the candidate's constants:

    Nat.count        CHURN natural-nth-selector
      out: Nat.nth_mem_anti, Nat.nth_mem_of_ne_zero, Nat.nth_ne_zero_anti,
           Nat.nth_of_forall, Nat.nth_true
      in : Nat.count_eq_zero, Nat.count_nth_zero, Nat.le_nth_count',
           Nat.le_nth_of_count_le, Nat.nth_count

    every other candidate set                 no frozen family's ten changes

So declaring `Nat.count` would silently rewrite **half of a held-out family's
preregistered rows**. `natural-nth-selector` is held-out (draw 7). That is a
second, independent reason to keep `Mathlib.Data.Nat.Count` refused, and it is
a reason nothing in the guard would have reported as such — the regenerated
manifest would simply differ, and `--check` would call it stale.

### Stale recorded review

`check-holdout-adjacency.py` screens EVERY held-out family, frozen ones
included, and `screen_family` REFUSES a family whose recorded review no longer
matches the live environment sweep — deliberately, because a review describing a
tree that no longer exists reads as diligence and is not. Four families carry
recorded reviews. A construction whose NAME shares a word stem with a reviewed
family's subject operators moves that sweep's count:

    Nat.ceilRoot + Nat.floorRoot
      REFUSED natural-nth-root -- recorded sweep [('root', ..., 11), ...]
                                 live sweep     [('root', ..., 13), ...]

    + Nat.findLeast, Nat.decidableDvd
      REFUSED natural-find-greatest -- 'decidable' 20 -> 21, 'find' 1 -> 2

    Nat.Primrec + constructors + recursor + unpaired + unpair projections
      no stale review, no churn

This is not noise. `Nat.floorRoot n a` is the greatest `b` with `b^n ∣ a` and
`Nat.nthRoot` is the greatest `m` with `m^k ≤ n`; the two ARE adjacent, and the
screen is right to demand the review be redone. But it is a real, unbudgeted
cost of the `Factorization.Root` route that no prior ADR names, and it lands as
a red standing gate rather than as a draw-time refusal.

**Generalise it: an unblocking lane must screen its construction NAMES against
the recorded reviews and against every frozen family's drawn ten, before
writing any code.** Both screens are cheap, both are pure Python against the
existing machinery, and each of them changed a decision here.

## The verified layout

Run through the real machinery, three layouts, `require_disclosure=False`:

    LAYOUT F -- four free families, nothing declared
      [0] natural-bit-representation      held-out  R9 FAIL, R11 refused
      [1] natural-fibonacci               development
      [2] natural-binomial-bounds         train
      [3] natural-factorisation-properties held-out R12 FAIL (2 rows)

    LAYOUT R -- index 3 solved, index 0 not
      [0] natural-bit-representation      held-out  R9 FAIL, R11 refused
      [1] natural-fibonacci               development
      [2] natural-prime-divisibility      train
      [3] natural-integer-root            held-out  R9/R12/R11 all PASS

    LAYOUT RP -- both slots solved
      [0] natural-primitive-recursion     held-out  R9 PASS R12 PASS R11 clean (vocab 0/10)
      [1] natural-fibonacci               development
      [2] natural-prime-divisibility      train
      [3] natural-integer-root            held-out  R9 PASS R12 PASS R11 clean (vocab 0/10)

Layout RP is the target. Note what the cycle actually constrains: with four or
more fresh families sorted by primary module, held-out lands at indices 0, 3,
6 — so the FIRST and FOURTH in sort order both need to be viable, and the two
in between need nothing but a pool of ten. Adding a fifth or sixth family does
not relax it. Free fillers are plentiful (seven of them); the two held-out
slots are the whole problem.

## Decision

**Declare `Nat.unpairLeft`, `Nat.unpairRight` and `Nat.unpaired` —
construction only (ADR-0653) — and author no draw.**

`crates/axeyum-lean-kernel/src/nat_prelude/unpair.rs`:

```text
Nat.unpairLeft  (n : Nat) : Nat := let s := sqrt n; let r := n - s * s
                                   in if r < s then r else s
Nat.unpairRight (n : Nat) : Nat := let s := sqrt n; let r := n - s * s
                                   in if r < s then s else r - s
Nat.unpaired (f : Nat → Nat → Nat) (n : Nat) : Nat
  := f (Nat.unpairLeft n) (Nat.unpairRight n)
```

These are Lean core's own `Nat.unpair` branches, component by component, over
the already-declared `Nat.sqrt`. Nothing recurses; `Nat.sqrt` supplies the only
recursion and `add`/`mul`/`sub`/`ble` are total.

**`avg_pair.rs` records `Nat.unpair` as unreachable here, and that reading is
right about `Nat.unpair` and wrong about the unpairing.** Mathlib's returns
`Prod`, which this kernel does not have. But the two PROJECTIONS have type
`Nat → Nat`, which mentions no product, and `Nat.unpaired` — the consumer that
actually appears in Mathlib statements — has Mathlib's own
`(Nat → Nat → Nat) → Nat → Nat`, which mentions no product either. Only the
BODY of Mathlib's version needs `unpair`. This is the standing
Bool-selected-scalar workaround (`Nat.xgcdAux (sel : Bool)`,
`Nat.divModState`, `creal/ivt.rs`'s `Bool → CReal`) applied to a case nobody
had applied it to, and it is the general lesson: **"needs `Prod`" is a claim
about a TYPE, and splitting the projections often makes it false.**

Every `ml430` mirror stated over Mathlib's `Nat.unpair` stays `open` — ours is
a different construction with a different type, the `Nat.multichoose` side of
the mirror-flip criterion.

**No theorem about any of the three is declared, and no fact is registered.**
The round-trip identity `unpairLeft (pair a b) = a` is exactly the ordinary
supporting theorem ADR-0653 says to land the day after a draw, from
`development`, where it costs nothing.

### Why these three and not the `Factorization.Root` pair

Both were available. `Nat.ceilRoot`/`Nat.floorRoot` solve index 3, which is
already solvable; the unpair trio moves the slot that is actually binding, and
it is the half of the index-0 construction that is testable by evaluation.
Measured against the two new screens, the choice is not close:

|  | churn | stale review | boundary rows | evaluation test possible |
| --- | --- | --- | --- | --- |
| `Nat.ceilRoot` + `Nat.floorRoot` | none | **reds `natural-nth-root`** | 3 of 10 | yes |
| unpair trio (toward Primrec) | none | none | **0 of 10** | yes |
| `Nat.count` | **5 of 10 in a held-out family** | none | 0 of 10 | yes |

## The evaluation suite, and why it is not decoration

The kernel cannot tell a `Definition` is wrong: `Nat → Nat` is `Nat → Nat`
whatever the body computes, so `add_declaration` accepts a transposed branch, a
projection that forgets the `- s` correction, or the two projections swapped
exactly as happily as the intended definition.

Three tests in `unpair_tests.rs`, all `def_eq` at concrete numerals against a
hand-computed table covering the whole first block `n ∈ [0, 8]`, so both arms of
the `r < s` test are exercised on both projections. Each negative control names
the specific wrong definition it rules out:

| control | discriminator | rules out |
| --- | --- | --- |
| `unpairLeft 5 = 1`, `unpairRight 5 = 2` | the true arm | a transposed branch condition, which gives `(2, 1)` |
| `unpairRight 6 = 0` | `r = s = 2` | a false arm that forgets `- s`, which gives `2` |
| `unpairLeft 4 = 0` | `(0, 2)` | the two projections swapped |
| round trip against `Nat.pair`, all 9 pairs in `[0,2]²` | `pair` is not symmetric | any wrong branch, at an argument pair `avg_pair_tests.rs` already pins independently |
| `unpaired sub 6 = 2`, `unpaired sub 5 = 0` | `Nat.sub` is asymmetric | swapped projections inside `unpaired` |

Two properties are load-bearing rather than stylistic:

- **The round trip's swap control is vacuous on the diagonal**, where `a = b`,
  so the test ASSERTS its own off-diagonal count (`assert_eq!(off_diagonal, 6)`)
  rather than trusting the loop. A control that never executes is the failure
  this repository cares most about.
- **`unpaired` is checked with an ASYMMETRIC `f`.** With `add` or `mul` the
  test cannot see swapped projections at all — it would pass against
  `f (unpairRight n) (unpairLeft n)`. `Nat.sub` at `n = 6` and `n = 5` covers
  the disagreement in both directions, so truncating to the right answer at one
  argument fails at the other. A symmetric check is included too, and is
  labelled in the source as testing the application shape only.

Magnitudes are single digits throughout: this prelude's numerals are unary
towers, and `Nat.sqrt n` is a linear search with `n` fuel.

**Mutation-verified**, in this lane's own worktree (never the shared checkout).
Transposing `unpairLeft`'s branch kills all three tests; replacing the `- s`
correction with `r` kills all three and names `unpairRight 2 must be 0`,
`unpairRight (pair 1 0) must be 0` and `unpaired sub 6 must be sub 2 0 = 2`.
Restored, and green.

## Verification

**Kernel.** `--lib unpair` 3 passed / 0 failed (nonzero, confirmed).
`--lib nat_prelude::` **299 passed / 0 failed**, up from 296 — the whole
prelude sweep, because one bad declaration poisons the shared prelude build and
a filtered subset cannot see it. All three names are covered by
`nat_prelude_tests`' environment-derived definition list.

**Environment.** `shape_search --release` rebuilt after the declarations:
**2688**, exactly +3 over the pre-declaration 2685, all three present.
`control: axiom=30` unchanged — that is `AxReal` and nothing here touches it.

**Gates.**

| gate | result |
| --- | --- |
| `gen-autogenesis-nursery-refill.py --check` | OK, `env=2688`, manifest byte-identical, 420 entries |
| `check-autogenesis-holdout-isolation.py` | `held_out=166 settled=0 PASS`, before and after |
| `check-holdout-closed-evaluation.py` | `held_out=166 closed_shaped=0 violations=0 snapshot_declarations=2688 PASS` |
| `create-autogenesis-nursery-dispatch-baseline.py --check` | OK |
| `check-holdout-adjacency.py` | 16 held-out families, 0 refused, no review stale |
| `check-shape-duplicates.py` | OK, 15 groups, all allowlisted |
| `check-autogenesis-already-proved.py` | exit 0 |
| `check-autogenesis-nursery.py` | **exit 1, RED ON `main` TOO** — verified from a detached worktree at `main`, unrelated to this lane |

**Blind-evaluation integrity.** No fact moved partition, no fact was
registered, `nursery-v1.json` was never touched, and no
`FAMILY_MODULES`/`FAMILY_ROUTES` edit is committed — that is the draw lane's
edit. Both snapshot refreshes were checked for manifest churn and produced
none.

## Consequences

- **Draw 16 is NOT authorable yet, and the reason is index 0, not index 3.**
  Layout RP needs `Nat.Primrec` and `Nat.casesOn`; this lane supplied
  `Nat.unpaired`, taking `Mathlib.Computability.Primrec.Basic` from three
  missing constants to two. `Nat.Primrec` is an inductive predicate over
  `Nat → Nat` with seven constructors, and the honest caveat is that an
  inductive `Prop` admits **no evaluation test** — the safeguard every
  definition in this repository leans on does not apply, so that lane needs
  discriminating checks designed for an inductive (each of Mathlib's
  constructors type-checking against the declaration, and each closure property
  in the drawn ten being *statable*) rather than a numeral table.

- **Index 3 is solved on paper and costs a re-review.**
  `Nat.ceilRoot`/`Nat.floorRoot` give `natural-integer-root` (18 rows, R9/R12/
  R11 all clean) with a disclosed 3-of-10 boundary reading, and reds
  `check-holdout-adjacency.py` until draw 11's `natural-nth-root` review is
  redone against the new environment. That re-review is real work and it is the
  right work: `floorRoot` and `nthRoot` are genuinely adjacent.

  **The boundary reading is DEFINITION-RELATIVE and this ADR's count assumes
  Mathlib's definition.** Mathlib's `ceilRoot` goes through `Nat.factorization`
  (a `Finsupp`), which this kernel cannot state, so ours would have to be a
  different construction — plausibly a bounded least-witness search, under
  which `ceilRoot 1 a = a` becomes a real theorem rather than `refl` and the
  count drops. That is a measurement the building lane must make, not a claim
  to inherit.

- **Two screens are now named and should be run by every unblocking lane
  before it writes code:** frozen-family drawn-ten churn, and stale recorded
  review. Each changed a decision here, neither appears in any prior draw ADR,
  and both are pure Python against machinery that already exists.

- **`Nat.ToInt.*` is a hygiene gap.** `HYGIENE` excludes `Int.Linear.*` and
  `Nat.Linear.*` as `omega`'s internal certificate vocabulary; `Nat.ToInt.*` is
  the same thing and is not excluded, and it currently constitutes a
  14-row family that passes every screen. Widening the pattern changes what
  other families draw, so it needs its own lane.

- **`Mathlib.NumberTheory.FactorisationProperties` should be spent as
  development or train, not held out.** It is 15 free rows, R11-clean, and only
  two of its drawn ten are spent — as a filler it is the best free supply
  remaining, and holding it out is the one thing it cannot be.

- **`Nat.unpair` is no longer a documented impossibility.** `avg_pair.rs`'s
  module doc should be read as scoped to `Nat.unpair`'s `Prod`-returning type,
  which is what it says; the function it computes is available now.

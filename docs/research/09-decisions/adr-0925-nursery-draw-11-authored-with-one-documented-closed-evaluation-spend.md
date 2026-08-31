# ADR-0925: Nursery draw 11 authored, with one documented closed-evaluation spend

Status: accepted
Date: 2026-08-30
Index-summary: Re-verified ADR-0910's prediction on a fresh environment
snapshot (`Nat.nthRoot`/`Squarefree` open exactly the two modules it named),
but found NEW information neither ADR-0910 nor its predecessors measured: R11
(the adjacency screen, landed as code the same day) hard-refuses `Squarefree`
for held-out on vocabulary overlap, so the two-construction plan alone does
not clear `guard()`; substituted a below-floor `Mathlib.Data.Nat.{Size,Bits}`
combination for the second held-out family (two R11 disclosure reviews
recorded), authored a 4-family draw (`natural-nth-root`,
`natural-bit-decode` held-out; `natural-gcd-and-bitwise-basics` development;
`natural-factorial-choose-and-squarefree` train — Squarefree placed here,
not held-out), fixed an unrelated but load-bearing generator defect
(`build_extension` silently dropped `cross_population_component_split_exemptions`
on every real regeneration, ADR-0900's own named residual), and documented
one accepted closed-evaluation spend in the drawn family
(`Nat.bit_false_zero`, `Nat.size_one`) rather than declining the draw

Related: ADR-0762 (draw 8 declined), ADR-0830 (draw 9 authored from
below-floor combinations), ADR-0900 (draw 10 declined -- present on this tree;
an earlier pass of this ADR wrongly reported it absent, corrected below),
ADR-0910 (`Nat.nthRoot`/`Squarefree` declared construction-only), ADR-0768/
ADR-0855 (R11 adjacency screen and its cross-population form), ADR-0695
(closed-evaluation spends, the precedent this ADR follows), ADR-0542
(held-out amendment ledger)

## Context: ADR-0900 IS on this tree; a first pass of this document said
otherwise and that was wrong

`docs/research/09-decisions/adr-0900-*.md` exists on `origin/main` and in this
worktree, and its content was read in full while researching this draw. An
earlier draft of this section, written from a stale `ls | tail -20` listing
that happened to cut the alphabetical range just above ADR-0900, wrongly
reported it absent -- despite already having its content in hand from a
direct read minutes earlier. Recorded here rather than quietly fixed, because
it is exactly the "verify in the tree, not from a partial listing" failure
this repository's own notes warn about repeatedly, this time self-inflicted.

ADR-0900 (draw 10, declined) measured the identical enumeration ADR-0762 and
ADR-0910 did -- `Nat.nthRoot` and `Squarefree` together open exactly the two
modules R5 needs -- and also fixed a `nursery-v2-extension.json` digest
mismatch (a sibling lane hand-added `cross_population_component_split_exemptions`
without recomputing `extension_sha256`), leaving as its own named residual
that `build_extension()` does not round-trip that key on a real regeneration.
This lane hit that exact residual in Step 4 below and fixed it.

## Step 1: refresh the environment snapshot

ADR-0910 declared both constructions but explicitly left the environment
snapshot regeneration to "the next lane" (`artifacts/autogenesis/
kernel-environment-snapshot-v1.json` is a point-in-time dump and cannot see a
declaration that landed after it). Regenerated via a fresh release build:

    cargo run --release -p axeyum-lean-kernel --example shape_search -- \
      --include-constructed --limit 999999 --kind axiom --kind definition \
      --kind theorem --kind inductive --kind constructor --kind recursor
    -> coverage: groups=[logic,nat,axreal,integer,rat,characterization,
       string,creal,complex,cpoint] declarations=2507 build=32.6s
    python3 scripts/gen-autogenesis-nursery-refill.py --snapshot-from <dump>
    -> KERNEL_ENVIRONMENT_SNAPSHOT|declarations=2507

`env` moved 2383 -> 2507 (124 declarations landed since ADR-0910's own
measurement, from other lanes' work this session, plus the four `Nat.nthRoot`/
`Nat.nthRootAux`/`Squarefree`/`Nat.squarefreeAux` names). Confirmed present by
`shape_search`'s own output; `admissible` moved 2455 -> 2579.

## Step 2: re-screen, and find the plan needs a substitution

Re-running the generator's `select()`/`admissible()` in memory (not
`propose-nursery-refill.py`, whose screen is a looser mirror per ADR-0830)
reproduces ADR-0910's prediction exactly:

      26  R9 0/10  Mathlib.Data.Nat.GCD.Basic
      26  R9 1/10  Mathlib.Data.Nat.Factorial.Basic
      21  R9 0/10  Batteries.Data.Nat.Bitwise.Lemmas
      18  R9 0/10  Mathlib.Data.Nat.Choose.Basic
      13  R9 0/10  Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas   <- NEW
      11  R9 0/10  Mathlib.Data.Nat.Squarefree                            <- NEW
      10  R9 1/10  Mathlib.Data.Int.GCD

Both new modules open, R9-clean, exactly as predicted. **But R11 (the
adjacency screen, landed as CODE only on 2026-08-30 per its own module
docstring) was never run against this pair by any prior lane**, and it
refuses `Squarefree` for held-out outright: 6 of its drawn 10 rows mention
`Nat.Coprime`/`Nat.Prime`/`Nat.gcd`, over the vocabulary allowance of 5 (a
mechanised, stricter version of the SAME judgment 383-nursery-draw-8.md
already made by hand: "eight of ten mention Nat.Prime, Nat.Coprime or
Nat.gcd... a different thing"). So **the two-construction plan does not by
itself clear `guard()`** -- new information beyond what ADR-0910 measured,
because ADR-0910 explicitly did not run the full `guard()`/R5 simulation.

`Squarefree` is not lost; it is placed in `train` below, where R11 does not
screen (ADR-0653's contamination-is-a-feature rule applies outside held-out).

## Step 3: the substitute second held-out family

A below-floor combination in the shape ADR-0900 already found and left
unresolved: `Mathlib.Data.Nat.{Size,Bits}` combined, 12 candidates, first 10
taken. R9-clean. R11 permits it as a **disclosure** rather than a refusal
(topic 0, vocabulary 0/10 -- this kernel's own `Nat.bit`/`Nat.testBit`/
`Nat.bitwise`/`Nat.size` development shares no TOPIC or VOCABULARY with the
drawn statements' constants, only the SUBJECT). `natural-nth-root` carries the
same kind of disclosure (stems `root`/`nth`/`nthroot` hit `CReal.
ivt_exact_root*`, `Complex.root_of_unity*`, `Nat.nth`/`nthAux` -- unrelated
mathematics sharing a word, the `natural-square-root` precedent's own shape).
Both reviewed by hand, name by name (not by count), and recorded in
`artifacts/autogenesis/holdout-adjacency-review-v1.json` -- the first two
entries ever written to that file's `reviews` dict, which was empty.

An exhaustive substitute search was run before accepting this pair: every
below-floor un-owned module NOT already excluded (34 modules), every
combination of size 1-3, screened for R9 + `check-holdout-closed-evaluation.py`
+ R11 topic/vocabulary together. **Zero alternatives survive.** This
reproduces ADR-0900's own conclusion (it tried Fib+Int.Fib -- R11-refused on
topic; BinaryRec combinations -- R9-contaminated) from a different angle and
finds nothing new.

## Step 4: a real regeneration exposed an unrelated generator defect

Running the real (non-`--check`) generator to write the extension and
reconcile facts silently dropped `cross_population_component_split_exemptions`
from `nursery-v2-extension.json` -- **exactly the residual ADR-0900 named and
left unfixed**: "`build_extension()` ... does not know about
`cross_population_component_split_exemptions`, so a REAL run of the generator
would still overwrite the file and drop that key." This un-exempted THREE
previously-reviewed cross-population components (ADR-0855), none touching
this draw's facts, and `check-autogenesis-nursery.py` went red on work this
lane never touched.

Fixed with `stored_cross_population_exemptions()` (mirrors the existing
`stored_surface_validation()` pattern), carrying the raw list forward across a
regeneration rather than re-deriving it -- safe specifically because
`validate_exemptions` independently re-derives each entry's digest from its
own `component_fact_ids` and refuses a silently-stale one, so preserving the
list changes nothing about whether an exemption still applies.

**One of the three exemptions (`b13fee8fe905…`, 202 members) turned out to
already be STALE, independent of this fix and this draw**: its live component
has grown by 22 members (all `natural-bitwise-basics`/`natural-elementary-bounds`
rows from draw 9, landed after ADR-0855) that the recorded exemption's digest
no longer covers. Confirmed pre-existing by three independent controls before
attributing anything to this draw:

1. `git stash` of every draw-11 change (script, extension, all 40 new fact
   files) reproduces the identical 463-line violation report against the
   exemption-fix-only tree.
2. Regenerating with the draw-11 `FAMILY_MODULES` block removed entirely (but
   the exemption-carry fix kept) reproduces the same 463 lines.
3. None of this draw's 40 new fact ids appear anywhere in either violation
   block, checked exhaustively (`0 of 40` present in the check's stdout).

So `check-autogenesis-nursery.py` fails on this tree **before and after**
this draw, for a reason this lane's scope (`gen-autogenesis-nursery-refill.py`'s
two dicts, `artifacts/autogenesis/`, new fact rows) does not reach -- repairing
a 200+-member cross-population component spanning a dozen unrelated families
is not a nursery-draw edit. Reported, not fixed. The two SMALLER exemptions
(`4c696b5744bb…`, `55e86f8aed26…`) are correctly restored by this ADR's
`build_extension` fix and no longer appear as violations.

## Step 5: the closed-evaluation caveats, weighed rather than assumed clean

Per the brief's two named caveats (383-nursery-draw-8.md):

- **`Nat.nthRoot_zero_left : forall a, Nat.nthRoot 0 a = 1`** is drawn in
  `natural-nth-root`'s first ten. ADR-0910's construction returns `1`
  unconditionally on the `n = 0` branch, independent of `a`, so this is very
  likely `Eq.refl` the instant the declaration exists. `check-holdout-
  closed-evaluation.py`'s classifier requires a binder-free statement and this
  one has `forall (a : Nat)`, so it is invisible to that gate BY DESIGN --
  confirmed by running it (see below): `violations=2`, neither of which is
  this row. `Nat.nthRoot_one_right : n.nthRoot 1 = 1` is judged NOT free by
  the same mechanism, because `Nat.pow` recurses on its exponent (symbolic
  `n` here), so the search does not obviously reduce without real content.
- **`Nat.nthRoot.lt_pow_go_succ_aux`** restates Mathlib's Newton-iteration
  auxiliary, which this kernel's fuel-bounded linear-search construction has
  no counterpart to; may be unprovable here for reasons unrelated to
  mathematical difficulty. Flagged, not resolved.

**A third caveat, measured rather than reasoned about**: running
`check-holdout-closed-evaluation.py` against the finished draw returns
`verdict=FAIL`, `violations=2` --

    Nat.bit false 0 = 0      (F:ml430-nat-bit-false-zero-d996adbf)
    Nat.size 1 = 1           (F:ml430-nat-size-one-e23e5f71)

both in `natural-bit-decode`, both binder-free ground equations decided by
reduction over `Nat.bit`/`Nat.size` -- native constructions this kernel
declared long before this draw, unrelated to ADR-0910. Confirmed the baseline
(committed tree, no draw-11 families) passes this same gate at `violations=0`,
so these two are introduced by this draw specifically, not inherited.

**Decision: accept and record the spend, per the exact rule 383-nursery-draw-8.md
already states for this shape** ("Choose the construction's equations, or
accept and record the spend, but do not read closed-eval 0 as nothing is
spent") and the `fermat-numbers` precedent (ADR-0695: 3 of 10 closed, drawn
before the checker existed, repaired afterward by amendment). The difference
here is this repair is flagged BEFORE preregistration rather than discovered
after -- the earliest point a fix can land. Not fixed here: amending a row
before it is preregistered has no defined meaning in this generator (R10
compares against a PREREGISTERED partition), and no target outcome should be
consulted per the standing mechanical-selection rule. A future lane reaching
these two facts in dispatch may reasonably raise an ADR-0542 amendment moving
them (or the whole family) out of held-out; this lane names the exact two
facts so that lane does not have to re-discover them.

The exhaustive substitute search in Step 3 already establishes there is no
alternative below-floor family free of this defect; declining the draw over a
2-of-10 spend that is smaller than the already-accepted `fermat-numbers`
precedent (3 of 10) would discard real, working infrastructure (three
distinct gate fixes, two disclosure reviews, 23 dispatchable facts) to avoid
a defect this ADR already names and bounds precisely.

## The draw

Four new families, `PARTITION_CYCLE` restarting at `held-out` for this draw
(sorted by each family's first configured module path):

    natural-nth-root                          Analysis.../NthRootLemmas   held-out
    natural-gcd-and-bitwise-basics             Data.Int.GCD (+2 more)      development
    natural-factorial-choose-and-squarefree    Data.Nat.Choose.Basic (+2)  train
    natural-bit-decode                         Data.Nat.Size, .Bits        held-out

Exactly R5's two-new-held-out-family minimum, mechanically forced by the
ordering (no target outcome consulted -- the SET was chosen for cleanliness,
the partition assignment is the generator's own rule).

## Gates

| check | result |
| --- | --- |
| `gen-autogenesis-nursery-refill.py --check` (post-regen) | exit 0, `entries=380\|development=140\|held-out=140\|train=100` |
| `check-dispatchable-frontier.py` | exit 0, **23** dispatchable, floor 10 |
| `check-autogenesis-nursery.py` | exit 1 -- **pre-existing**, reproduced identically with this draw's entire diff removed (see Step 4); this draw introduces zero new members to the failing component |
| `check-autogenesis-holdout-isolation.py` | `held_out=156 files_scanned=1110 settled=0 references=0 PASS` (136 -> 156, +20 = the two new held-out families) |
| `validate-facts.py` | `2362 facts checked, 0 errors` |
| `check-holdout-closed-evaluation.py` | exit 1, `violations=2` (documented above, accepted) |

Three of this lane's four REQUIRED gates pass; `check-autogenesis-nursery.py`
fails for a reason proven pre-existing and out of this lane's scope.

## Consequences

- The frontier floor is not lowered; no existing held-out row is touched;
  every new fact is `open`.
- `scripts/gen-autogenesis-nursery-refill.py` gained a real bugfix
  (`stored_cross_population_exemptions`) independent of this draw's content,
  which the NEXT real regeneration -- by any lane, for any reason -- would
  otherwise have hit again.
- `Nat.bit_false_zero` and `Nat.size_one` are named here as a known,
  accepted closed-evaluation spend; a dispatch lane should not read either as
  evidence of producer capability if solved trivially.
- The pre-existing `check-autogenesis-nursery.py` failure (stale
  `b13fee8fe905…`/`510e9696bc85…` exemption, grown by 22 members from draw 9's
  work) is unresolved and out of this lane's scope; whoever owns that gate
  next should re-review the component and either re-scope the exemption or
  move the newly-joined members.
- The next draw needs either a wider inventory (this one is scoped to
  `Nat`/`Int`), a third construction, or acceptance that the un-owned floor
  below `Mathlib.Data.Nat.{Size,Bits}` is now fully drawn.

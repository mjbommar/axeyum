# ADR-1115: Draw 14 is declined — the index-3 family's rows were already decided, and R12 could not see the shape

Status: accepted
Date: 2026-08-31
Index-summary: ADR-1100 enabled two four-family layouts for draw 14 and left
the R11 disclosure to the draw lane. Both sweeps were performed.
`natural-avg-pair` is clean and its review is recorded. The other held-out
family, `natural-factorisation-properties` — the ONLY late-sorting
held-out-viable candidate in the whole space, re-confirmed here by running the
real `select()` over every un-owned module — draws
`Nat.abundant_twelve : Nat.Abundant 12` and `Nat.deficient_one :
Nat.Deficient 1`, which the committed `abundant_evaluates_at_twelve` `def_eq`
test already shows unfold to the ground inequalities `Lt 24 28` and `Lt 1 2`.
They are decided by reduction the instant the ADR-1100 construction landed, so
they are not blind. **R12 reported a clean 0 of 10 because
`is_closed_evaluation` required an `=` and a ground PREDICATE application has
none** — a shape gap, not a judgement call, and the gate built to prevent
exactly this spend was silent. `is_closed_evaluation` is now the disjunction of
`_is_ground_equation` and `_is_ground_predicate`; blast radius measured at zero
(0 of 146 committed held-out rows change classification) and mutation-verified.
With the gap closed the gate names both rows, so draw 14 is **declined** — the
fourth consecutive decline, and the first with a mechanised finding behind it.
Held-out isolation `held_out=146 settled=0 PASS` before and after; a separate
repair unblocked `gen-autogenesis-nursery-refill.py`, which was RED on `main`.

Related: ADR-1100 (enabled the draw, declared the four definitions, deliberately
did not author it), ADR-1095 (draw 13 declined; derived the `ceil(n/3)`
mechanism), ADR-1045 (draw 12 declined), ADR-0695/ADR-0950 (R12, the
closed-evaluation screen — this ADR widens its classifier), ADR-0768 (R11, the
adjacency screen and its disclosure review), ADR-0653 (contamination in a
published partition is a feature; in held-out it is a spend), ADR-0542 (the
amendment ledger)

## What this lane was asked to do

Author `FAMILY_MODULES`/`FAMILY_ROUTES` for one of ADR-1100's two layouts,
record the two R11 disclosure sweeps, and regenerate `nursery-v2-extension.json`.

Everything ADR-1100 measured reproduces. What it did not measure — because the
gate it relied on could not see it — is why the draw does not happen.

## Re-screening, and one blocker that had to be cleared first

**`gen-autogenesis-nursery-refill.py` was RED on `main` and nothing reported
it.** Not `--check`, not a plain regeneration:

    autogenesis-nursery-refill: nursery-v2-extension.json does not match its
    own extension_sha256, so its recorded partitions cannot be trusted as the
    freeze

`frozen_partitions()` raises before a single row is selected, so no draw lane
could have got past step one. Bisected over the last eight commits touching the
manifest, each checked with **that commit's own** copy of the generator:
`d3384d7fb` MATCH, `b81f22780` MISMATCH. That commit hand-edited the
`cross_population_component_split_exemptions` reason string and did not re-pin
the digest — the guard firing exactly as its docstring says it should. Repaired
by recomputing the digest over the committed body and nothing else (one line;
the writer asserts the reloaded body equals the body it read).

**The environment has not moved since ADR-1100.** `shape_search --release`
rebuilt fresh in this worktree (71 s cold build, then a full dump) reports
`declarations=2593` with control `axiom=30 definition=360 theorem=2124`, and the
NAME SET is identical to the committed snapshot — 0 declarations on either side
of the difference, checked as sets rather than counts. So ADR-1100's numbers
were measured against the same tree this draw would be authored against.

**Every one of ADR-1100's three screening results reproduces**, from the real
`select()`/`assign_partitions()`/`guard()` imported and patched in memory only:

| layout | result |
| --- | --- |
| control, 3 free families | `R5 the refill adds 1 held-out families` |
| A (`fib-and-bitwise` at train) | only R11's disclosure remains |
| B (`stirling-numbers` at train) | only R11's disclosure remains |
| five families | `R9 … [('natural-fib-and-bitwise', 'Nat.fib_add')]` |

So "exactly four" is right, and adding a fifth is refused for the reason
ADR-1100 gives.

**The positional search was re-run rather than inherited**, because ADR-1100's
own closing advice is to ask the positional question. Over all 38 un-owned
modules with at least one screened candidate, exactly seven sort strictly after
`Mathlib.NumberTheory.FactorisationProperties`, totalling 14 rows —
`PowModTotient` (4), `PrimeCounting` (2), `PrimesCongruentOne` (1),
`PythagoreanTriples` (1), `SumTwoSquares` (1), `RingTheory.Int.Basic` (3),
`Tactic.IntervalCases` (2). Combined they clear the floor, so a **layout C** is
arithmetically available: demote `natural-factorisation-properties` to train at
index 2 and put the late combination at held-out index 3. Screened with the real
`guard()`:

    natural-late-number-theory: vocabulary: 7 of 10 rows are about constants a
      development/train family publishes (allowance 5) -- Nat.Prime, Nat.totient,
      Nat.Coprime, Int.gcd

Vocabulary is a hard signal, not waivable. So `natural-factorisation-properties`
really is the only family that can occupy the late held-out slot, exactly as
ADR-1100 says.

## The finding

`natural-factorisation-properties` draws these ten rows, alphabetically:

    Nat.Abundant.mul_left            Nat.Abundant.of_dvd
    Nat.Prime.deficient              Nat.Prime.deficient_pow
    Nat.Prime.not_abundant           Nat.Prime.not_perfect
    Nat.abundant_iff_not_perfect_and_not_deficient
    Nat.abundant_twelve
    Nat.deficient_iff_not_abundant_and_not_perfect
    Nat.deficient_one

**Two of them are not propositions anybody has to prove.** `Nat.Abundant 12`
unfolds to `Lt 24 28` and `Nat.Deficient 1` to `Lt 1 2`, both ground numeric
inequalities over a definition declared hours earlier. This is measured, not
reasoned: `nat_prelude/abundant_deficient_tests.rs` — written by ADR-1100's own
lane, as CLAUDE.md requires of every new `Definition` — already asserts

    def_eq(Nat.Abundant 12, Lt 24 28)

with `Lt 28 24` and `Lt 12 28` as negative controls. `Nat.lt x y` is
definitionally `Nat.le (succ x) y`, so what remains after the unfold is a
constructor tower, not an argument.

That is precisely ADR-0695's spend, and ADR-0695's gate said nothing.

### Why the gate was silent, and why that is the important half

`is_closed_evaluation` classified a statement as a closed evaluation only if it
was a binder-free statement with exactly one `=` and a bare numeral on one side.
Every family the gate had ever screened stated its ground rows as equations —
`Nat.fermatNumber 0 = 3` (draw 7), `Nat.bit_false_zero = 0` and `Nat.size_one =
1` (draw 11) — so the `=` requirement looked like part of the definition of
"closed evaluation". It was an artefact of the sample.

A ground PREDICATE application has no `=` at all. The gate ran, exited 0, and
printed a correct answer to a question nobody had asked it.

Fixed by splitting the classifier into two named shapes and taking their
disjunction. The numeral requirement is what keeps the new one narrow:
`Monotone Nat.fermatNumber` and `StrictMono Nat.fermatNumber` are binder-free
non-equations in the same family and are genuinely blind, because they quantify
over the whole function and nothing reduces.

**Blast radius measured before the code was written**, which is what made the
change safe to make from a draw lane: the committed held-out population of 146
rows across both manifests contains **zero** predicate-shaped rows. Nothing
reclassifies, no gate turns red, and no existing draw is retroactively
condemned. The gate reads `held_out=146 closed_shaped=0 violations=0
verdict=PASS` after the change as before.

**Mutation-verified** on a scratch copy with `__pycache__` cleared between
iterations (the documented stale-bytecode trap):

    baseline                  killed=0
    drop the numeral guard    killed=2   Monotone / StrictMono
    drop the head guard       killed=1   "12"
    drop the whole branch     killed=3   Abundant 12 / Deficient 1 / Prime 7

An explicit `"=" not in text` guard was written and then **removed**: it is
unkillable — zero fixtures die without it, because `=` is neither an identifier
nor a numeral and the token check already rejects it. That is the same finding,
with the same remedy, that the equation branch already records about its own
redundant guard.

**The discriminating evidence**, R12's body called directly on this draw's
candidate entries (R11 raises first inside `guard()`, so the ordering hides it):

    with the extension   REFUSED: R12 2 held-out candidate(s) …
                           ('natural-factorisation-properties', 'Nat.Abundant 12')
                           ('natural-factorisation-properties', 'Nat.Deficient 1')
    pre-extension        no violation      <- what the draw would have shown

## Decision

**Draw 14 is declined.** The one family that can occupy the late held-out slot
draws two rows the unblocking construction already settles, and this generator
has no lawful mechanism to drop one row from an alphabetically-drawn pool.

Three things were considered and rejected:

- **Accept and record the spend**, the ADR-0695 route draws 7 and 11 took. The
  empirical record is against it: draw 11's `natural-bit-decode` was drawn at
  the same 2-of-10 and then **amended out of held-out entirely** under ADR-0542
  (commit `7296730d6`). Knowingly preregistering a family whose documented
  repair is a ten-row partition move is worse than not drawing it.
- **Enlarge the family so the two rows fall outside the alphabetical ten.** This
  is available — adding an un-owned module whose names sort earlier would do it
  — and it is disqualified on principle. Every prior draw's comment states that
  the family SET was chosen without consulting outcomes; choosing a module in
  order to displace two rows one dislikes is exactly consulting the outcome, and
  it would put a fabricated blindness into the ledger.
- **Add `Nat.Abundant`/`Nat.Deficient` to `HELD_OUT_CONSTRUCTIONS`.** That
  screen is per-constant and global, so it removes all fifteen of the family's
  rows from every partition, not the two.

## The two disclosure sweeps

Both were performed against the live environment and both are recorded in
`artifacts/autogenesis/holdout-adjacency-review-v1.json`, verbatim, including
what is awkward.

**`natural-avg-pair` — clean, recorded as a `reviews` row.** The sweep is
`[["avg", "Nat.avg", 1]]` and the count of 1 IS the finding: every declaration
whose lowered name contains `avg` was enumerated and there is only the
construction, with no theorem about it. Each of the ten drawn statements was
compared against it.

Two things the stem mechanism does not reach were checked separately, because
the screen structurally cannot see them:

- **`Nat.pair` is never swept.** It is the subject of `Nat.add_le_pair` but
  appears in 1 of 10 rows, below `SUBJECT_FRACTION`, so it is not a subject
  constant and no `pair` stem exists. Enumerated by hand: 16 environment
  declarations contain `pair`. `Nat.pair` is ADR-1060's Cantor pairing, again
  with no theorem about it; `Nat.Pair`/`.mk`/`.fst`/`.snd`/`.ext`/`.eta`/`.rec`
  are the inductive pair TYPE added for `Nat.binaryRec`; and
  `Nat.restrict_pair_injective`/`Nat.restrict_pair_maps_into` are about
  `compact_pair`/`expand_pair` index reindexing from the Gauss-lemma work — an
  unrelated function sharing a word, the same false-positive class
  `natural-square-root`'s accepted review names. Nothing states
  `m + n ≤ Nat.pair m n`.
- **All ten rows carry binders**, so none is ground under either shape the
  widened R12 classifies. Checked, not assumed.

Verified live both ways: `screen_family` returns `clean` with the recorded row,
and `refused` as stale when the recorded count is perturbed to 2.

**`natural-factorisation-properties` — reviewed and REFUSED, deliberately NOT a
`reviews` row.** A review row is a licence to draw, and writing one for a family
that must not be drawn would be the rubber stamp the file exists to prevent. It
is recorded in a new top-level `refused` list, which `load_reviews` ignores by
construction.

R11's own three signals are clean on it and that is worth stating plainly: topic
0, vocabulary 4 of 10 against an allowance of 5, and the stem sweep resolves
benignly — the 99 hits on stem `prime` are dominated by `coprime` merely
containing the substring, and read by name they are the `Nat.coprime_*` /
`Nat.prime_*` / totient / gcd development, none of which states a drawn row
(all four `Nat.Prime.*` rows conclude about `Abundant`/`Deficient`/`Perfect`,
and the stems `abundant`, `deficient` and `perfect` each resolve to exactly one
declaration, the definition itself). What refuses the family is R12.

Two further findings from that review, neither a refusal on its own and both
material to what a held-out result here would MEAN:

- **The sweep does not reach `Nat.sumDivisors`**, through which all three
  predicates are defined — `sumdivisors` is not a stem of `Abundant`,
  `Deficient`, `Perfect` or `Prime`. Enumerated by hand: `Nat.sumDivisors` plus
  four theorems, of which `Nat.sumDivisors_prime : Prime p → sumDivisors p =
  succ p` makes `Nat.Prime.deficient`, `Nat.Prime.not_abundant` and
  `Nat.Prime.not_perfect` cheap rather than open — each becomes an order fact
  about `p + 1` against `2p`, with `Nat.prime_one_lt` already present. Nothing
  proves them, so those rows are blind in the letter; a reader deciding what a
  held-out result means needs to know they are much easier than the module name
  suggests. This is ADR-1100's own flag, confirmed and made specific.
- **`Nat.Perfect` is already declared against the same `Nat.sumDivisors`**, so
  the trichotomy rows are an arithmetic trichotomy on `sumDivisors n` against
  `2n` rather than a factorisation argument.

`Mathlib.Data.Nat.Count` is recorded in the same list and **labelled as carried
forward from ADR-1100 rather than verified here**: it screens held-out-viable
(22 rows, R9 0/10, R12 0/10, R11 clean) and is not, because `Nat.countRange`
already proves five of its rows under other names. Recorded so that the screen
PASSING it is not read as evidence — that is R11's documented shape-2 blindness,
which no name-based screen can see.

## Consequences

- **The mathematics queue stays below its floor**, and the next draw needs a
  new index-3 candidate, not a fifth family. ADR-1100's list of late,
  topic-clean, R9/R12-clean candidates still needing constructions stands, with
  one addition this lane's finding makes: **the construction must not settle any
  of the family's alphabetically-first ten rows by reduction**, and that is now
  checkable before declaring anything, by running the widened
  `is_closed_evaluation` over the module's pool. The three named candidates are
  `Mathlib.Data.Nat.Factorization.Root` (18, `Nat.floorRoot` + `Nat.ceilRoot`),
  `Mathlib.Data.Nat.Find` (15, `Nat.find` + `DecidablePred`) and
  `Mathlib.Data.Nat.MaxPowDiv` (10, `Nat.divMaxPow` + `padicValNat`).

- **ADR-1100 is not wrong and should not be read as a wasted lane.** Its screen
  said `R12 0/10` and that was an accurate report of what R12 answered. The
  four definitions are landed, axiom-free and useful, and `natural-avg-pair`'s
  review — the expensive half of a draw's disclosure — is now done and live for
  whoever draws next. What changed is the instrument.

- **An unblocking lane should screen the rows its construction will make
  GROUND, not only the rows R9 will flag.** `Nat.Abundant 12` is in Mathlib's
  own module because it is a worked example; declaring the predicate settles it.
  The rule generalises past this family: a construction whose pool contains a
  worked numeric example spends that row.

- **The gate's own history is the argument for the fix.** R12 exists because
  draw 7 spent three rows on `Nat.fermatNumber` evaluations; it was extended by
  ADR-0950 after draw 11 found two more; and it was silent here on a third
  shape. Each time the shape was one nobody had seen before, and each time the
  gate's clean verdict read as evidence. Treat `violations=0` from a
  shape-matching classifier as "no violation of a shape I model", never as "no
  violation".

# ADR-1420: The refill draw is not authorable -- R5 needs two held-out families, and one two-row module gates every candidate

Date: 2026-09-01
Status: Accepted
Lane: `nursery-draw-author`

Index-summary: Draw 17 is refused, not deferred. R5 requires two NEW held-out
families, which needs at least four new families; exhaustively over all 2^18
subsets of the topic-clean unowned modules, EVERY viable held-out family
contains `Mathlib.Tactic.IntervalCases`, so at most one can exist and no
disjoint pair does.
Index-status: Accepted

## Context

`check-dispatchable-frontier.py` fails at G7 with **3** dispatchable `ml430`
mirrors against a floor of **10**. The prescribed remedy is a nursery refill
draw: a hand edit to `gen-autogenesis-nursery-refill.py`'s `FAMILY_MODULES` and
`FAMILY_ROUTES`. This lane was sent to author it.

ADR-1405 and the two screening reviews of 2026-09-01 established the input:
two ready families, `Mathlib.Data.Nat.Log` (17 survivors) and
`Mathlib.NumberTheory.FactorisationProperties` (15), and the arithmetic
`dispatchable_yield(n) = 10·(n − ⌈n/3⌉)`, which gives **exactly 10** at `n = 2`.

Re-measured here on `main` at `a6c531eab`, both numbers reproduce and
`artifacts/autogenesis/refill-headroom-v1.json` regenerates with a **zero
diff**. Nothing moved.

## The finding

**`dispatchable_yield` is the wrong constraint, and a two-family draw is
refused before it is ever evaluated.**

Run against the real `select()` + `guard()` with those exact two families:

```
  [0] natural-logarithm-base            Mathlib.Data.Nat.Log                          -> held-out
  [1] natural-factorisation-properties  Mathlib.NumberTheory.FactorisationProperties  -> development
select OK: 480 entries
GUARD_REFUSED: R5 the refill adds 1 held-out families; the blind population is
               already down to two capabilities
```

R5 (`gen-autogenesis-nursery-refill.py`) demands at least **two** new held-out
families. `_with_cycle` restarts `("held-out", "development", "train")` at index
0 for each draw's new families, so the held-out count is `⌈n/3⌉` and two
held-out families need **n ≥ 4**. Two ready families cannot produce a lawful
draw at any yield.

## Can four families be assembled?

Only two unowned modules carry ten survivors on their own, but a family is a
BUNDLE of modules, so the question is whether four coherent bundles exist. There
are **104 survivors across 28 unowned modules** — enough rows in principle.

The binding screens are the ones applied to a NEW HELD-OUT family:

- **R9** — no drawn name already declared in this kernel.
- **R12** — no drawn row is a closed evaluation already decided by reduction.
- **R11 topic** — no module topic segment shared with a development/train family.
- **R11 vocabulary** — at most `VOCABULARY_MAX_ROWS = 5` of the ten rows about
  constants a development/train family publishes.
- **R11 disclosure** — a nonempty environment sweep needs a recorded review.
  Fixable by writing the review; not a structural block.

Screened with the real `screen_family()` / `is_closed_evaluation()`, as if each
were held-out:

| candidate family | modules | R9 | R12 | R11 |
| --- | --- | --- | --- | --- |
| `Mathlib.Data.Nat.Log` | 1 | 0/10 | clean | **refused** — topic `Log` (natural-logarithm), vocab 10/10 |
| `Mathlib.NumberTheory.FactorisationProperties` | 1 | 0/10 | **2** (`abundant_twelve`, `deficient_one`) | vocab 4/10, disclosure only |
| bit representation (BinaryRec + Bitwise + Init.Bitwise.Basic) | 3 | **3/10** | clean | **refused** — topic `Bitwise`, vocab 9/10 |
| binomial bounds (Choose.Bounds/Dvd/Sum + Multiplicity) | 4 | **1/10** | clean | **refused** — topic `Choose`,`Dvd`, vocab 10/10 |
| prime-power decomposition (Factorization.* + Factors) | 4 | 0/10 | clean | **refused** — vocab 9/10 |
| prime distribution (Bertrand + PrimeCounting + PowModTotient + …) | 5 | 0/10 | clean | **refused** — topic `Prime`, vocab 10/10 |

Every candidate is refused as held-out. That is not an artefact of how the
bundles were drawn by hand, which is why the search below is exhaustive.

## The exhaustive result

Topic collision is a per-MODULE property and vocabulary is a per-ROW property,
so a held-out family must be built entirely from topic-clean unowned modules.
There are **18** of them, carrying **57** survivors of which **19** are
vocabulary-clean.

Enumerating all `2^18` subsets, taking the first ten survivors by name
(`select()`'s own rule) and applying R9 / R12 / R11-vocabulary:

```
modules 18, viable subsets 36868
modules present in EVERY viable subset: ['Mathlib.Tactic.IntervalCases']
EXACT answer -- two disjoint viable held-out families: NO
```

The disjointness answer is exact, not sampled: it is a subset-sum DP over the
18-bit module universe, so it considers every one of the 36,868 viable subsets
against every other.

**`Mathlib.Tactic.IntervalCases` is in every viable subset**, and it holds two
rows. Its `Int.add_one_le_of_not_le` and `Int.le_sub_one_of_not_le` are both
vocabulary-clean and both sort alphabetically ahead of almost everything else in
the pool, so they enter every drawn ten and supply two of the five clean rows a
family needs. A module belongs to exactly one family, so **at most one viable
held-out family can exist at a time**.

R5 needs two. **Draw 17 is refused.**

## What the exhaustive screen approximates, and in which direction

Two things separate this search from `screen_family()` verbatim, and both were
checked rather than assumed.

**Plumbing.** The real screen computes
`plumbing({**published_rows, family: rows})`; the search computes it over the
published families alone. Adding a family can push a constant into the plumbing
set, which would REMOVE it from the vocabulary owners and make the search
over-count hits. Probed over 19 cases -- every topic-clean module alone, and all
18 together -- plumbing moved in **6** of them and added only logical
connectives (`Ne`, `And`, `Or`), and the vocabulary-owner map was **identical in
every case**: 26 plumbing constants, 24 owners, unchanged. So the approximation
is exact in the dimension that matters. The probe is 19 cases rather than all
`2^18`, so this is a strong sample, not a proof.

**Same-draw publication.** `screen_draw` adds a draw's OWN development/train
families to the published set before screening its held-out ones. The search
scores against today's published families only, so the real hit count can only
be **higher**. That direction is safe for a refusal: a subset the search calls
non-viable stays non-viable.

## What this means, precisely

- It is a supply problem in the vocabulary-clean dimension, not in raw rows.
  Nineteen vocabulary-clean survivors exist and eleven of them are in one
  module, `Mathlib.NumberTheory.FactorisationProperties`.
- `Mathlib.Data.Nat.Log`'s newly-unblocked 17 rows are **all** vocabulary-hitting
  and topic-colliding, because `natural-logarithm` is already a
  development/train family. Log is drawable as `development` or `train`; it can
  never be held-out while `natural-logarithm` is published.
- ADR-1405's "READY FAMILIES = 2 is enough" is arithmetically right about yield
  and does not survive R5. The proposer's own R3 checks yield against the floor
  and has no R5 analogue, so it reports a two-family draw as sufficient. That is
  the gap worth closing next.

## Decision

Do not author draw 17. Do not weaken R5, and do not reorder a family's module
tuple to move a partition — both are edits to the rule made to obtain a
preferred partition, which the preregistration forbids.

## Consequences

The frontier stays below its floor at 3 dispatchable mirrors. The unblock is a
supply question with three named routes, in increasing cost:

1. **Declare a construction that opens a topic-clean, vocabulary-clean module.**
   This is the ADR-0653 route draws 15 and 16 used. The lane must declare the
   DEFINITION only — declaring theorems about it spends the family through R9.
2. **Retire or re-partition a published subject** so a topic segment stops
   colliding. Expensive and probably wrong: it trades blind population for
   dispatchable population in the direction R5 exists to prevent.
3. **Close the 11 divergence-blocked mirrors' divergences** or settle catalog
   rows to widen the statable bridge. The proposer measures the bridge route's
   ceiling at +172 candidates and notes it is not growing.

Route 1 is the one to take, and the screen above says exactly what a new module
must satisfy: topic-clean against every development/train family, and at least
five of its alphabetically-first ten rows about constants no development/train
family publishes.

## Verification

Every number here is from a command run in this lane's worktree.

```
python3 scripts/propose-nursery-refill.py --remeasure   exit 0   17 / 15, zero diff
python3 scripts/check-dispatchable-frontier.py          exit 1   G7, 3 dispatchable
python3 scripts/gen-autogenesis-nursery-refill.py --check exit 0 entries=460, env=2711
python3 scripts/check-autogenesis-holdout-isolation.py  exit 0   held_out=186 PASS
python3 scripts/check-holdout-adjacency.py              exit 0   18 families, 0 refused
```

`check-autogenesis-nursery.py` exits **1** on a cross-population
`depends_on` component spanning development / train / longitudinal. It is red on
`main` and unrelated to this lane; `unblock-draw-16.md` recorded the same
failure on 2026-08-31.

The zero-diff invariant over already-drawn rows holds trivially and is asserted
rather than assumed: no draw was authored, and
`gen-autogenesis-nursery-refill.py --check` re-derives the whole manifest and
every fact file from `FAMILY_MODULES` and reports it byte-identical. All 460
extension entries keep their partition (development 170, held-out 170,
train 120).

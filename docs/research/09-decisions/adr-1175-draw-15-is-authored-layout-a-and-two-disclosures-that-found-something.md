# ADR-1175: Draw 15 is authored — layout A, and two disclosure reviews that found something

Status: accepted
Date: 2026-08-31
Index-summary: Draws 10, 12, 13 and 14 declined in a row on one constraint;
ADR-1160 removed it by declaring `DecidablePred` and `Nat.findGreatest`
construction-only, leaving exactly one refusal — R11's disclosure step, which
is authorable rather than measurable. This lane authored it. Layout A
(`natural-avg-pair` held-out, `natural-minmax` development,
`natural-stirling-numbers` train, `natural-find-greatest` held-out) was chosen
over layout B on a MEASUREMENT, and the measurement refuted the hypothesis that
made the choice look important: neither layout moves any existing held-out
family's topic or vocabulary count. What separates them is dispatch supply —
`natural-stirling-numbers` draws 1 reduction-settled row of ten and 0 already
in the environment, `natural-fib-and-bitwise` draws 4 and 1. Both R11 sweeps
were run against a freshly rebuilt `shape_search` (env=2629) and every
declaration they name was read against the drawn ten. Two things were found
that no gate reports: this kernel has a BOUNDED least-element search over a
decidable predicate (`Nat.lnp_bounded_search`) whose extremality clause is the
structural dual of `findGreatest_eq_iff`, and a greatest-satisfying-index
existence statement (`Nat.exists_most_significant_bit`). Neither settles a drawn
row; both are transportable skeletons, so the family is less blind than a stem
count suggests, and that is disclosed rather than waved past. `GUARD PASSED`,
entries 380 → 420, held-out 146 → 166, `settled=0`, nothing moved partition.

Related: ADR-1160 (the unblock this consumes), ADR-1115 (draw 14 declined; the
`natural-avg-pair` review this one supersedes), ADR-1100 (the positional
framing), ADR-1095 (the `ceil(n/3)` mechanism), ADR-0768 (R11 and its
disclosure review), ADR-0653 (construction-only unblocks; contamination outside
held-out is a feature), ADR-0542 (the amendment ledger)

## What was inherited and what was re-measured

Nothing was inherited that could be measured. In particular:

- **The environment had moved.** The committed snapshot read 2625 declarations;
  a freshly built `shape_search --release` in this worktree reads **2629**. The
  four new names are `Int.pow_neg_one_of_even`, `Int.pow_neg_one_of_odd`,
  `Int.secondSupplementaryLaw` and `Nat.half_ceil_parity`, all from the
  second-supplementary lane merged into `main` minutes before this one started.
  The snapshot was refreshed and `--check` re-run: the manifest is
  **byte-identical** under the refresh, so it churned nothing. Checked rather
  than assumed, because ADR-1095's own refresh displaced two `train` rows.
- **ADR-1160's construction-only claim.** `find_greatest.rs` carries one
  `Declaration::Definition` and **zero** `.theorem(` call sites, read from the
  source.
- **The `Mathlib.Data.Nat.Find` pool.** Replicating `select()`'s screen exactly:
  15 rows, the first ten drawn, and pool rows **12 and 13** are
  `Nat.findGreatest_succ` and `Nat.findGreatest_zero` — the definition's own two
  equations, both `refl` against our construction — falling outside the drawn
  ten by the alphabet. No module was added or removed to put them there.
- **All three of ADR-1160's layouts, through the real machinery.** Layouts A and
  B each refuse on exactly the `natural-find-greatest` disclosure and nothing
  else; the three-free-families control still refuses with `R5 the refill adds 1
  held-out families`. The live sweep is byte-identical to ADR-1160's despite the
  four extra declarations.

`propose-nursery-refill.py` was not used as a candidate space, per ADR-1160.

## Decision: layout A

    Batteries.Data.Nat.Bisect                   natural-avg-pair          held-out
    Init.Data.Nat.MinMax                        natural-minmax            development
    Mathlib.Combinatorics.Enumerative.Stirling  natural-stirling-numbers  train
    Mathlib.Data.Nat.Find                       natural-find-greatest     held-out

The assignment is the mechanical `held-out, development, train` cycle over the
lexicographic primary-module order; only the SET is a judgement, and it was made
against already-published partitions with no target outcome consulted.

**The reason the choice looked important is wrong, and that is the finding.**
The two layouts differ only at index 2, and the hypothesis was that layout B's
`natural-fib-and-bitwise` would publish `Nat.bit` / `Nat.bitwise` vocabulary into
`train` and eat screening margin from the existing held-out `natural-bit-decode`
(draw 11), which is about `Nat.bit` and `Nat.size`. Measured by re-running
`screen_family` over every held-out family under baseline, A and B:

    layout A: existing held-out families whose topic or vocabulary count MOVED: 0
    layout B: existing held-out families whose topic or vocabulary count MOVED: 0

Neither layout costs any blind population anything. The hypothesis is recorded
because it is what made the decision feel consequential, and it is not.

**What actually separates them is dispatch supply**, measured over each drawn
ten with `is_closed_evaluation` and the environment snapshot:

| index-2 family (train) | pool | closed-eval in drawn ten | already in-env |
| --- | --- | --- | --- |
| `natural-stirling-numbers` | 16 | **1** (`Nat.stirlingFirst_zero`) | **0** |
| `natural-fib-and-bitwise` | 20 | **4** (`Int.fib_{neg_one,one,two,zero}`) | **1** (`Nat.fib_add`) |

Both sit in `train`, where contamination is ADR-0653's fast-closure feature
rather than the ADR-0542 leak, so neither is unlawful — layout A simply buys
nine rows of real work where B buys five. `natural-fib-and-bitwise` remains
available for a later draw.

**The index-3 family is `Mathlib.Data.Nat.Find` alone, deliberately.** Combining
it with any other module reshuffles the alphabet and would pull
`findGreatest_succ` / `findGreatest_zero` into the drawn ten; such a combination
must re-run the screen.

## The two disclosure reviews

ADR-1100 and ADR-1115 both refused to write these rows on the grounds that a
review asserting diligence nobody performed is the checker-that-cannot-fail
defect with a paper trail. This lane performed them. Both are recorded in
`artifacts/autogenesis/holdout-adjacency-review-v1.json` under `reviews` (a
licence to draw), not `refused` (which `load_reviews` ignores by construction).

### `natural-find-greatest`

Sweep, reproduced live and recorded verbatim:

    [["decidable", "Decidable", 20], ["greatest", "Int.gcd_greatest", 2],
     ["decidablepred", "DecidablePred", 1], ["find", "Nat.findGreatest", 1]]

All 24 declarations were enumerated and read by name against the drawn ten.
`decidable` is the logic prelude's decidability plumbing plus `Rat.decidable_le`
and three string-prelude equality deciders; `greatest` is `Int.gcd_greatest` —
an unrelated function sharing a word, the same false-positive class
`natural-square-root`'s accepted review names — and `Nat.findGreatest` itself.

**Nothing settles any drawn row**, and two mechanical checks say so rather than
a count: the environment dump contains the string `findGreatest` exactly once
and it is the `Definition`, and `shape_search --const Nat.findGreatest` is
`ABSENT`.

**Two findings the sweep does not surface, and no gate reports.**

1. **This kernel has a BOUNDED least-element search over a decidable
   predicate.** `Nat.lnp_bounded_search : ∀ (Q : Nat → Prop), (∀ n, Or (Q n)
   (Not (Q n))) → ∀ n, Or (∀ k, Lt k n → Not (Q k)) (∃ m, And (Lt m n) (And
   (Q m) (∀ k, Lt k m → Not (Q k))))` — bounded, decidable, **with the
   extremality clause**, which is the structural dual of what
   `findGreatest_eq_iff` and `findGreatest_eq_zero_iff` characterize. Siblings:
   `Nat.lnp_decidable`, `Nat.lnp_of_pointwise_decision`,
   `Nat.lnp_unrestricted_implies_em`, `Nat.em_implies_lnp`. It reached the sweep
   only through the `decidable` stem, incidentally.
2. **`Nat.exists_most_significant_bit : ∀ n, Not (Eq n zero) → ∃ i, And (Eq
   (testBit n i) one) (∀ j, Lt i j → Eq (testBit n j) zero)`** is the nearest
   thing in the environment to `findGreatest_is_greatest`'s content — a greatest
   satisfying index with everything above it failing. The stem sweep cannot
   reach it at all.

Neither states any drawn row: both are free-standing existence statements about
the LEAST element or about `testBit` specifically, not characterizations of a
defined function, and neither can mention `Nat.findGreatest`, which was declared
the day before. But a producer arriving at `findGreatest_eq_zero_iff` has
`lnp_bounded_search`'s induction-on-the-bound skeleton available, and
`msb_exists_of_le_fuel`'s fuel induction besides. **The family is materially
less blind than a sweep of four stems suggests, and a held-out result here
should be read knowing that.** Recorded as a disclosure and not a refusal, on
ADR-0654's stated rule: a blind family must be allowed to use developed tools or
nothing could ever be held out. The bar for refusal is a MIRROR — the same
statement under another name, which is what refused `Mathlib.Data.Nat.Count` —
and there is none.

Also enumerated by hand and cleared: `Nat.sqrt` (only `sqrt_zero`, `sqrt_one`,
`no_rational_sqrt_two`), `Nat.nthRoot`/`nthRootAux` (no theorem),
`Nat.nth`/`nthAux` (ascending selector, no theorem), `Nat.countRange` and its
25 lemmas (every one concludes about `countRange`), `Nat.least_divisor_search`,
`Nat.leastResidue`, `Nat.least_residue_*`.

**The reduction reading, which is the part R12 cannot do.** R12 reports 0 of 10,
and that is true but weak — `is_closed_evaluation` is binder-free by
construction, so a `∀`-quantified defining equation is invisible to it
(ADR-1160). Reading the ten instead: none is a boundary equation of
`Nat.findGreatest`. The nearest is `findGreatest_of_not : ¬P (n+1) →
findGreatest P (n+1) = findGreatest P n`, the else-branch of the recursion gated
on a hypothesis — **not** `refl`, because the construction branches through
`Decidable.byCases` on `dp (succ m)`, a variable applied to a term, which never
ι-reduces at a symbolic argument.

### `natural-avg-pair`

Sweep `[["avg", "Nat.avg", 1]]`, unchanged. **This review was REDONE rather than
carried forward from ADR-1115**, and the row supersedes it, because that review
predates ADR-1160's finding that R12 cannot see a quantified defining equation.
Applying that reading: none of the ten is a boundary equation of `Nat.avg` or
`Nat.pair` — there is no `avg 0 b`, no `avg a a`, no `pair 0 b` among them — and
the nearest candidate, `Nat.avg_comm : a.avg b = b.avg a`, is **not** `refl`,
because `Nat.add` recurses on its right argument, so `div (add a b) 2` and
`div (add b a) 2` are not definitionally equal at symbolic `a`, `b`; it needs
`Nat.add_comm` under the division.

`--const Nat.avg` and `--const Nat.pair` are both `ABSENT`. The `pair` hand
sweep still reads 16 declarations at env=2629 and resolves as ADR-1115 recorded:
`Nat.pair` the Cantor-style `Definition`, the unrelated `Nat.Pair` inductive
type from `binary_rec.rs`, `Nat.restrict_pair_*` index reindexing, and four
unrelated hits across `Int`/`CPoint`/`CReal`/`Rat`.

## A control failure worth its own paragraph

The first mechanical absence checks used `shape_search --concl Nat.avg`,
`--concl Nat.pair` and `--concl Nat.findGreatest`, all three `ABSENT`. Then the
positive control — `--concl Nat.countRange`, over a family with 25 lemmas in
this kernel — **also returned `ABSENT`**. `--concl` indexes the conclusion
HEAD, which for an equation is `Eq`, so the query could never have matched and
three confident negatives proved nothing.

Re-run with `--const` (the constant occurs anywhere in the type), the control is
`FOUND 21` and the three subject queries are genuinely `ABSENT`. This is exactly
the trap CLAUDE.md names — *an empty result from a tool that was never pointed at
your subject is indistinguishable from a strong negative result* — arriving
through a flag that reads like the right one. **Pair every `shape_search`
absence with a positive control that must produce output, using the same flag.**

## Verification

    gen-autogenesis-nursery-refill.py            GUARD PASSED, entries 380 -> 420
                                                 development 150->160, held-out 130->150,
                                                 train 100->110, env=2629
    gen-autogenesis-nursery-refill.py --check    OK
    check-autogenesis-nursery.py                 OK, ready=true, blockers=0
    create-autogenesis-nursery-dispatch-baseline.py --check
                                                 OK, tripwire literal UNMOVED
                                                 (candidates=198 dispatchable=0
                                                  declined=22 established=176)
    check-holdout-closed-evaluation.py           PASS, held_out=166 closed_shaped=0
                                                 violations=0 snapshot=2629
    check-autogenesis-holdout-isolation.py       PASS, held_out 146 -> 166,
                                                 settled=0, references=0
    check-holdout-adjacency.py                   16 held-out families, 0 refused,
                                                 both new ones `reviewed`
    validate-facts.py                            OK, 40 new facts
    check-settled-fact-statements.py --write     wrote 2214 pins, 0 existing fact
                                                 files modified (the 40 new rows are
                                                 `open`, so not settled)
    check-settled-fact-statements.py             PASS, drifted=0

**Blind-evaluation integrity.** No fact moved partition, `nursery-v1.json` was
never touched, and `settled` stays 0. The held-out count rises 146 → 166 because
two new held-out families were registered, which is the point of the draw. The
generator wrote exactly 40 fact files, one per drawn row — checked before
staging, because `gen-kernel-facts.py`'s lack of a per-declaration filter has
cost a lane 135 spurious facts this session; this generator does not have that
defect.

## Consequences

- **The five-draw drought is over**, and it was one authorable row, exactly as
  ADR-1160 predicted. The four declines were each correct and each narrowed the
  cause; none of them was wasted.
- **A disclosure review can find something without refusing.** Both prior
  refusals to write these rows were right, and the payoff is concrete: the
  `Nat.lnp_bounded_search` and `Nat.exists_most_significant_bit` findings are
  invisible to every gate we have, would not have surfaced from a stem count,
  and change how a `natural-find-greatest` result should be read. A review that
  only ever says "nothing adjacent" is not measuring anything.
- **`--concl` is not `--const`, and `shape_search` absence needs a same-flag
  positive control.** Recorded above; the general form is already in CLAUDE.md
  and this is a fresh instance of it costing real confidence.
- **`natural-fib-and-bitwise` stays available** as a pre-screened index-2
  candidate, along with ADR-1160's three remaining index-3 candidates
  (`Factorization.Root`, `MaxPowDiv`, `Factorization.LCM`), all of which need
  the boundary-equation reading before use.
- **The layout-margin hypothesis is refuted and should not be re-derived.**
  Adding a development/train family did not move any existing held-out family's
  screen. A future draw choosing between index-2 candidates should compare
  dispatch supply, not adjacency spend.

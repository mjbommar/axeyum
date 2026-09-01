# ADR-1450: The counting-predicate family is not blind, draw 17 is refused, and the refusal that was already on record bound nothing

Date: 2026-09-01
Status: Accepted
Lane: `nursery-draw-17`

Index-summary: Draw 17 is mechanically authorable in exactly one coherent
shape and that shape needs `Mathlib.Data.Nat.Count` in held-out. It is not
blind: `Nat.count` is a definitional alias of `Nat.countRange`, four of the ten
drawn rows are the same proposition term-for-term and a fifth is entailed by a
stronger declared equation, and by the divergence registry's own standard the
mirrors are unclosable anyway. Exhaustively, every viable held-out family at
<= 3 modules contains `Count`, `MaxPowDiv` or `FactorisationProperties`; the
last is already `do-not-draw-held-out` and one module cannot anchor the two
held-out families R5 demands, so R5 cannot be satisfied honestly. The sharper
finding: a `do-not-draw-held-out` verdict for exactly this module was ALREADY
in the review file from ADR-1100, and nothing read `refused` at all --
`screen_family` looks up `reviews[family]`, so a refusal keyed by a MODULE name
was unreachable. That is now enforced, with four mutation-verified guards.

Index-status: Accepted

## Context

`check-dispatchable-frontier.py` fails at G7 with **2** dispatchable `ml430`
mirrors against a floor of 10 (ADR-1420 measured 3 at `a6c531eab`; re-measured
here at `b558d9b5a`). ADR-1420 established that a refill draw needs four fresh
families because R5 demands two NEW held-out ones and `_with_cycle` restarts the
`held-out, development, train` cycle per draw. ADR-1430 declared `Nat.count` and
`Nat.divMaxPow` to open two modules and reported the draw authorable up to two
R11 disclosure reviews, naming `natural-counting-predicate`'s as substantive.

This lane was sent to write those reviews and author the draw.

## Re-measurement, before anything

Each gate run bare, exit status captured before any grep.

| gate | exit | headline |
| --- | ---: | --- |
| `gen-autogenesis-nursery-refill.py --check` | 0 | `entries=460 env=2829 development=170 held-out=170 train=120 screen_drift=31` |
| `check-autogenesis-holdout-isolation.py` | 0 | `held_out=186 files_scanned=1110 PASS` |
| `check-holdout-adjacency.py` | 0 | 18 held-out families, 0 refused, 4 undisclosed (advisory) |
| `check-dispatchable-frontier.py` | **1** | G7, **2** dispatchable |
| `validate-facts.py` | 0 | — |
| `check-autogenesis-nursery.py` | **1** | pre-existing cross-population component |

Two corrections to what was inherited, both re-derived:

- The frontier is **2**, not 3.
- `--check` is **green**. ADR-1430 recorded it red at `46bc65cc4`; ADR-1445's
  membership freeze is what returned it to green, and `screen_drift=31` is that
  thinning, published rather than discarded.

And one correction to ADR-1430's own draw: **it does not run as stated.** With
the single-module families its table lists, `select()` raises —
`Mathlib.Data.Nat.MaxPowDiv` yields **7** and `Mathlib.Data.Nat.Factorization.Basic`
yields **5**, against `PER_FAMILY` 10. Both must be bundles, which its table
does not say. (Its lane's status document does record `MaxPowDiv` "pool 7 alone
and 11 bundled with `Mathlib.NumberTheory.Bertrand`"; the ADR dropped it.)

## The draw is mechanically authorable

One coherent arrangement clears everything except the disclosures. Run against
the real `select()` / `assign_partitions()` / `screen_family()` / `guard()`:

```
  [0] Mathlib.Data.Nat.Count               natural-counting-predicate   -> held-out
  [1] Mathlib.Data.Nat.Factorization.Basic natural-prime-factorization  -> development
  [2] Mathlib.Data.Nat.Log                 natural-logarithm-base       -> train
  [3] Mathlib.Data.Nat.MaxPowDiv           natural-max-power-dividing   -> held-out
  pools 22 / 10 / 17 / 13      select OK: 500 entries, 40 new
  R9 CLEAN   R12 CLEAN   R11 topic 0, vocabulary 0/10 and 4/10
  CHURN over the 460 already-drawn rows: NONE
  only refusal: R11 disclosure, both new held-out families
```

So the question is entirely whether the disclosures can honestly be written.

## Review 1 — `natural-counting-predicate`. REFUSED.

Live sweep: `[('count', 'CReal.le_meshLevelCount', 46), ('decidable',
'Decidable', 20), ('decidablepred', 'DecidablePred', 1)]`.

`Nat.count dec n := Nat.countRange dec n` is a **definitional alias**
(`nat_prelude/count_and_div_max_pow.rs`), and the environment snapshot carries
**22** `countRange` lemmas — re-counted from the declaration list, not from the
module doc, which says 19. Kernel types read from `nat_theorem_inventory`,
Mathlib statements from the pinned inventory:

| drawn row | kernel declaration | verdict |
| --- | --- | --- |
| `count_add` — `count p (a+b) = count p a + count (fun k => p (a+k)) b` | `countRange_split` | **the same proposition, term for term** |
| `count_le` — `count p n ≤ n` | `countRange_le` | **the same proposition** |
| `count_mono_left` — `(∀ k<n, p k → q k) → count p n ≤ count q n` | `countRange_le_of_subset` | **the same proposition** — its hypothesis `Nat.Subset p q n` is *defined* in `finite_set.rs` as `∀ k, k < n → p k = true → q k = true` |
| `count_monotone` — `Monotone (count p)` | `countRange_le_of_le` | **the same proposition**, unbundled |
| `count_lt_count_succ_iff` — `count p n < count p (n+1) ↔ p n` | `countRange_succ` | **entailed** by a strictly stronger declared equation; one `Bool.rec` on `p n` decides both directions |
| `count_iff_forall` | `countRange_congr_lt` ∘ `countRange_const_true` | easy direction declared |
| `count_ne_iff_exists`, `count_iff_forall_not` | `countRange_succ_of_true`, `countRange_ge_two_of_two_witnesses` | the same counting-witness argument, already run |
| `count_add'` | mirror of `countRange_split` | not declared |
| `count_injective` | — | **genuinely untouched** |

**R9 reports 0 of 10 and that is R9 working as designed.** It compares the drawn
Mathlib NAME against the environment, and the names differ (`count` versus
`countRange`). R11's vocabulary screen reports 0 of 10 one remove out, because
`Nat.countRange` is *kernel development* and the vocabulary map contains only
the subject constants of nursery development/train FAMILIES — nothing in it can
reach a lemma the kernel proved outside the nursery. The stem sweep is the only
signal in the whole guard that sees this, which is exactly the shape ADR-0768
built the disclosure for.

The precedent this is measured against is the review file's own: it accepts
`natural-square-root` as held-out beside our declared `Nat.sqrt`,
`Nat.sqrt_zero`, `Nat.sqrt_one` because "draw 8 compared all four by hand and
none is a mirror". Here four are mirrors. And the file's `how_to_add_a_row` is
explicit: *"If you found a mirror, do not write a row — the family is not blind
and must not be drawn."*

### The second reason, which is independent and worse

Mathlib's `Nat.count : (ℕ → Prop) → [DecidablePred p] → ℕ → ℕ`; ours is
`(Nat → Bool) → Nat → Nat`. That is the **same** type divergence
`mirror-divergence-registry.json` records for `Nat.nth` — *"Bool vs Prop domain
… the mirror is a different proposition per the mirror-flip criterion's own
'different types' clause"* — and a **larger** one than `Nat.findGreatest`'s,
which is registered on explicit-versus-instance-implicit `DecidablePred` alone
and whose family `natural-find-greatest` sits at pool 0 because of it.

By the registry's own standard applied consistently, every
`Mathlib.Data.Nat.Count` mirror is unclosable here. Unclosable rows in held-out
are the dead weight ADR-1445 measured at 31 rows across four families, not blind
population.

Either reason disqualifies the family on its own, and they are different
reasons. If the alias route is honest the rows are predictable; if it is not the
rows are unclosable. Held-out is wrong in both branches.

### Two corrections to `count_and_div_max_pow.rs`'s module doc

- It says the kernel has "no `List` and no `DecidablePred`". `List` is genuinely
  absent from the environment snapshot; **`DecidablePred.{u}` is declared**
  (`prelude.rs:356`) and is in the snapshot as a real declaration, not a bridge
  alias. All ten drawn rows mention it.
- It says 19 `countRange` lemmas. The snapshot has **22**.

## Review 2 — `natural-max-power-dividing`. Clean on the evidence.

Live sweep for the `MaxPowDiv + Multiplicity + Bertrand` bundle:
`[('prime', 'Int.Coprime', 110), ('max', 'CReal.evt_approx_max', 44),
('divmaxpow', 'Nat.divMaxPow', 2)]`.

- `divmaxpow` (2) is `Nat.divMaxPow` and `Nat.divMaxPowAux`, the ADR-1430
  definitions, with **no theorem stated about either** — the ADR-0653 discipline
  visible in the sweep. `maxPow`, `ordCompl`, `padic` and `multiplicity` return
  **zero** declarations; `bertrand` returns **zero**.
- `max` (44) is `CReal.evt_approx_max` and its neighbours: word collision across
  a different carrier.
- `prime` (110) is dominated by `coprime`, which merely contains the substring.
  The one genuine near miss is real and is not one: `Nat.prime_dvd_choose`
  (`p prime → 0 < k → k < p → p ∣ choose p k`) against the drawn
  `Nat.Prime.dvd_choose_pow` (`p prime → k ≠ 0 → k ≠ p^n → p ∣ (p^n).choose k`).
  Ours is the `n = 1` case of a strictly stronger prime-power statement.

**No `reviews` row is written**, because a `reviews` row is a licence to draw
and this family is not being drawn. The measurement is recorded here so the next
lane does not repeat it; it must be re-run against whatever bundle that lane
chooses, since the sweep is computed from the drawn ten.

Note also that `Nat.divMaxPow`'s type matches Mathlib's `ℕ → ℕ → ℕ` exactly, so
unlike `Nat.count` it carries no type divergence — its mirrors are statable and
genuinely open. The two constructions ADR-1430 landed are not in the same
position, and only one of them opened a usable family.

## Can the assignment be repaired?

**No, and this is the part that decides the draw.** The partition rule is
preregistered: families sort by the lexicographic path of their primary Mathlib
module, and partitions follow the cycle. Held-out is cycle index 0 and 3 for any
`n` in 4..6. Index 0 is always the lexicographically first family, so moving
`Count` out of held-out requires a **held-out-safe family whose primary module
sorts before `Mathlib.Data.Nat.Count`**.

Exhaustively, over all subsets of the 10 unowned modules that do (real
`select()` row screen, real `screen_family`, real `is_closed_evaluation`, R9
against the snapshot):

```
  unowned modules sorting before Mathlib.Data.Nat.Count: 10, 35 rows
  subsets reaching the ten-row floor: 902
  VIABLE: 0
```

Only two of those subsets reach ten rows without assembling a grab-bag — the
bitwise bundle (17 rows, refused: topic `Bitwise` twice, vocabulary 9/10) and
the binomial bundle (12 rows, refused: topic `Choose`/`Dvd`, vocabulary 10/10) —
reproducing ADR-1420's measurement at a universe that now includes `Nat.count`.

So `Count` cannot appear in this draw except as held-out, and it must not be
held-out. It is therefore **not drawn**, and it is not spent: it becomes
drawable as `development` or `train` the day any held-out-safe family's primary
sorts before it.

## Can a draw be built without `Count` at all?

Also no. Over every unowned module (28 with at least one screened row, 124 rows)
there are **240** viable held-out families at up to 3 modules, and **every one**
contains `Mathlib.Data.Nat.Count`, `Mathlib.Data.Nat.MaxPowDiv` or
`Mathlib.NumberTheory.FactorisationProperties`. Of those three anchors:

- `Count` — refused above.
- `FactorisationProperties` — already `do-not-draw-held-out` (ADR-1115), on R12
  plus the observation that `Nat.sumDivisors_prime` makes three of its drawn
  rows cheap. Bundling it *does* move the two R12 rows out of the drawn ten —
  measured, `[FactorisationProperties, PythagoreanTriples, IntervalCases]`
  screens clean — but that is bundling to displace the rows a screen names,
  which is the mechanism the ADR-1115 review says the generator has no lawful
  form of. Not taken.
- `MaxPowDiv` — clean, and a module belongs to exactly one family, so it can
  anchor **one** held-out family, not the two R5 demands.

Widening to 4 modules over the universe with all three anchors removed: **0
viable of 9,129 subsets**. At up to 6 modules there are **4**, and all four are
the same shape — exactly 10 rows, `Factorization.Basic`'s 5 plus single rows
scavenged from `PythagoreanTriples`, `SumTwoSquares`, `IntervalCases` and one
filler, landing at vocabulary exactly 5 of 10, the allowance. The coherent
`Factorization.Basic + Induction + PrimePow + Factors` bundle, also exactly 10
rows, is refused at vocabulary 9/10; swapping two factorization modules for
three unrelated ones is a vocabulary-count manoeuvre and not a family. One was
screened as a full arrangement to be sure and is **refused anyway**, on topic.

`Mathlib.Tactic.IntervalCases` appears in all four, which is ADR-1420's own
artefact: its two `Int.*` order lemmas are vocabulary-clean and sort ahead of
almost everything, so they supply free clean rows to any bundle that needs them.

## Decision

1. **Do not author draw 17.** R5's two held-out families cannot both be honest
   from today's modules.
2. **Record `natural-counting-predicate` as `do-not-draw-held-out`** in
   `holdout-adjacency-review-v1.json`, with the live sweep and the row-by-row
   comparison. Do not write a `reviews` licence for it.
3. **Make a recorded refusal bind** (below). This is the part that outlasts the
   draw.
4. Do not weaken R5, do not reorder a family's module tuple to move a partition,
   and do not bundle to displace the rows a screen names. All three are edits to
   the rule made to obtain a preferred outcome.

## The finding that outlasts the draw: `refused` bound nothing

While recording the refusal, the review file turned out to **already contain**
one for this exact module, from ADR-1100 and restated by ADR-1115:

> `"family": "Mathlib.Data.Nat.Count"`, `"verdict": "do-not-draw-held-out"` —
> *"`Nat.countRange` is already in this kernel … and `Nat.count p n` IS that
> function — so `count_zero`, `count_succ`, `count_le`, `count_true` and
> `count_monotone` are already proved here under other names. That is R11's
> documented shape-2 blindness, which no name-based screen can see."*

The conclusion this lane reached independently was on record before `Nat.count`
was declared. ADR-1430 then declared it to open exactly that module for a
held-out draw, and every screen in `guard()` stayed green.

**Nothing read `refused`.** `load_reviews()` returns the `reviews` object;
`screen_family` looks up `reviews[family]`. The refusal was keyed by a MODULE
name — necessarily, since the family did not exist when it was written — so no
lookup the guard performed could reach it. A `do-not-draw-held-out` verdict on
record, enforced by nothing, is the checker-that-cannot-fail defect with a paper
trail, which this repository treats as worse than no checker at all.

So `assert_draw_lawful` now reads it: a NEW HELD-OUT family drawing a module
recorded `do-not-draw-held-out` is refused, naming the row's authority.

Scoped exactly like the disclosure demand, and both halves matter:

- **Draw time only.** A family an earlier draw preregistered is history
  (ADR-1445); refusing one retroactively would red the gate on `main` for a
  decision nobody is making now. Inert on today's manifest — no drawn family
  owns either barred module — and verified so: `--check` and
  `check-holdout-adjacency.py` are unchanged and green.
- **Held-out only.** The argument is about blindness, and blindness is what
  held-out buys. `Mathlib.Data.Nat.Count` as development or train is 22 rows of
  ordinary work; a bar that applied everywhere would delete that pool for a
  reason that does not apply to it.

Four guards, each mutation-verified in a scratch copy to kill **exactly one**
test, and each a different one — registered in
`scripts/tests/mutation_controls.py` under the existing `holdout-adjacency`
suite:

```
  KILLED  a recorded do-not-draw-held-out verdict bars the draw
          -> test_a_held_out_family_drawing_a_barred_module_is_refused
  KILLED  the bar is scoped to held-out families
          -> test_a_barred_module_in_a_DISPATCHABLE_family_is_allowed
  KILLED  only a do-not-draw-held-out verdict bars, not any recorded note
          -> test_a_row_that_is_not_a_refusal_verdict_bars_nothing
  KILLED  an unreadable `refused` list is not 'nothing has been refused'
          -> test_an_unreadable_refused_list_is_not_read_as_nothing_refused
```

Two of the four aim at the opposite failure, which is the live risk once a bar
exists: a bar that caught dispatchable families, or that read any recorded note
as a veto, would refuse more than it should — and three consecutive declined
draws is already the state this project is in.

A sixth test asserts the join against the real file rather than a fixture
(`Mathlib.Data.Nat.Count` is in `barred_modules(load_refusals())`), so the
finding is in force rather than merely expressible.

## Consequences

The frontier stays at 2. The unblock is ADR-1420's Route 1 for the third time,
and this lane can state its requirement exactly rather than in general:

> **Declare a construction opening a module whose path sorts lexicographically
> before `Mathlib.Data.Nat.MaxPowDiv`, that is topic-clean and
> vocabulary-clean, and that leaves room for two families between it and
> `MaxPowDiv` in the sort order.**

`Mathlib.Data.Nat.Factorization.LCM` behind `Nat.factorizationLCMLeft` /
`…Right` remains ADR-1430's measured, unspent spare and sorts in the right
place. Its window arithmetic is different from the one ADR-1430 checked — that
was the `Count`/`LCM` pair, and the relevant one now is `LCM`/`MaxPowDiv`,
holding `Factorization.PrimePow` (2), `Factors` (2) and `Log` (17) — so the next
lane must re-derive it rather than inherit either number.

Two smaller consequences worth carrying:

- **A construction declared to open a family must be screened against the
  review file's `refused` list before it is written, not after.** ADR-1430's
  lane did the R9/R11/R12 screens faithfully and the one signal that would have
  stopped it was in a file no screen read.
- **`Nat.count` is not wasted.** It is a correct, tested definition, and the
  module it opens is 22 rows of dispatchable work the moment a held-out-safe
  family sorts ahead of it.

## Verification

Every number is from a command run in this lane's worktree at `b558d9b5a`.

```
python3 scripts/gen-autogenesis-nursery-refill.py --check      exit 0  entries=460
python3 scripts/check-autogenesis-holdout-isolation.py         exit 0  held_out=186
python3 scripts/check-holdout-adjacency.py                     exit 0  18 families, 0 refused
python3 scripts/check-dispatchable-frontier.py                 exit 1  G7, 2 dispatchable
python3 scripts/validate-facts.py                              exit 0
python3 -m unittest scripts.tests.test_check_holdout_adjacency exit 0  31 tests
```

`check-autogenesis-nursery.py` exits **1** on a cross-population `depends_on`
component spanning development / train / longitudinal. It is red on `main`,
predates this session, and is unrelated to this lane; ADR-1420 and
`unblock-draw-16.md` record the same failure.

The zero-diff invariant over already-drawn rows holds trivially and is asserted
rather than assumed: no draw was authored, `FAMILY_MODULES` is unchanged, and
`--check` re-derives the whole manifest and every fact file from it and reports
byte-identical output. All 460 extension entries keep their partition
(development 170, held-out 170, train 120). The churn probe that WOULD have
detected a move was run anyway, against arrangement A and against three
alternatives, and reported `churned=NONE` in each — so the instrument exists and
was exercised rather than merely available.

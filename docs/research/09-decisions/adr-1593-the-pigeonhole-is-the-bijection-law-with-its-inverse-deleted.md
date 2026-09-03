# ADR-1593: the pigeonhole principle is the bijection law with its inverse deleted, and the colliding pair is computed rather than extracted

Date: 2026-09-03
Status: Accepted
Lane: `finset-pigeonhole`

Index-summary: ADR-1577 landed `Nat.Finset` and measured the one thing standing
between it and the pigeonhole principle: `countRange p n ≤ countRange q m` from
an INJECTION between two selected sets, reported ABSENT by
`shape_search --hyp Nat.injectiveOn --concl Nat.le`. Six theorems close it,
every one admitted on the first attempt with `Kernel::axiom_footprint = []`.
The route chosen is `Nat.countRange_bij`'s own induction with the inverse `τ`
and the two round-trip equations DELETED — the base case collapses to
`Nat.zero_le` and the selected branch closes through `Nat.succ_le_succ` instead
of an equality — which reuses `count_range_bij.rs`'s single-point removal
apparatus and pays for the removal with the same
`Nat.countRange_point_change`. The rejected route (the RANGE pigeonhole in
`finite.rs` plus a rank/enumeration of a Finset's members as `[0, card s)`) was
measured, not guessed: every enumeration name is ABSENT, so it pays for a new
`Definition` plus its injectivity and surjectivity before reaching the same
place. TWO strengths of the pigeonhole land, and the distinction is the point:
`Nat.Finset.pigeonhole` REFUTES injectivity, while
`Nat.Finset.exists_collision` produces the explicit pair — and since this kernel
has no `funext`, no `propext` and no classical choice, the pair cannot be
extracted from the refutation but is COMPUTED by a bounded double search whose
`true` branch reflects back to injectivity and whose `false` branch yields the
witnesses through the new `Nat.Finset.allBelow_false_witness`. The consumer is
`Rat.rankCols_le_rank`, an UNCONDITIONAL bound where the bijection could only
give a conditional equality.
Index-status: Accepted

## Context

ADR-1577's own "what did not land" section is the brief for this one, and its
measurement stood up on a freshly rebuilt binary:

```text
shape_search --hyp Nat.injectiveOn --concl Nat.le          ->  ABSENT
shape_search --const Nat.countRange --concl Nat.le         ->  FOUND 4
   Nat.countRange_le                (a count is at most its bound)
   Nat.countRange_le_of_le          (bound moves, predicate fixed)
   Nat.countRange_le_of_subset      (predicate moves, bound fixed)
   Nat.countRange_ge_two_of_two_witnesses
shape_search --const Nat.Finset.memB --concl Nat.lt        ->  ABSENT
shape_search --const Nat.Finset.allBelow --concl Exists    ->  ABSENT
shape_search --name-like nthtrue|enumerate|rankof
             |selectIndex|indexOfNth|nthMember             ->  ABSENT (all six)
```

with `declarations=2622` on the nat-only build and `3496` with
`--include-constructed`, and the freshness control `AlgS.mul_zero` (which landed
on 2026-09-03, the same day, after this lane's merge base) returning `FOUND 1`.
A stale binary reports a false ABSENT in every direction, so the control has to
postdate the question; this one does.

The four `FOUND` rows say precisely what was missing. Every `countRange`
inequality in the tree moves ONE of the two arguments: the bound with the
predicate fixed, or the predicate with the bound fixed. Nothing related
`countRange p n` to `countRange q m` for independent `p, n` and `q, m` except
`Nat.countRange_bij` (ADR-1558's cross-bound EQUALITY), and that law needs a
constructive bijection — an explicit inverse `τ` with its own `MapsInto` and two
round-trip equations.

## Decision, part 1: the inequality is the bijection law with `τ` deleted

```text
Nat.countRange_le_of_injOn :
  ∀ (p q : Nat → Bool) (σ : Nat → Nat) (n m : Nat),
    (∀ i j, Lt i n → p i = true → Lt j n → p j = true →
       Eq Nat (σ i) (σ j) → Eq Nat i j) →
    (∀ i, Lt i n → p i = true → And (Lt (σ i) m) (q (σ i) = true)) →
    Le (countRange p n) (countRange q m)
```

Two hypotheses where `countRange_bij` has five, and the two it keeps are
`countRange_bij`'s own `H1` and `H2` verbatim. It lives in
`count_range_bij.rs` rather than in a new module, and that is the decision
rather than a filing convenience: **the proof is that file's induction with
three hypotheses struck out**, so every device it needs is already a few hundred
lines above it — `drop_pred` and its three defining equations (the
`Bool`-valued single-point removal), `weaken_inj`, `sel`, `lift_lt`,
`drop_eq_of_ne` — and the removal is paid for by the same
`Nat.countRange_point_change`.

Exactly two branches change, and both get SIMPLER:

- **`n = 0`** was the bijection's hardest case: with no index selected on the
  left, it had to refute every selected `j < m` by pushing it through `τ` into
  `[0,0)`. There is no `τ` here, and `countRange p 0` is `0`, so `Nat.zero_le`
  closes it with neither hypothesis used.
- **`succ n`, `p n = true`** ends at `Le (succ (countRange p n))
  (succ (countRange q' m))` through `Nat.succ_le_succ` rather than at an
  equality, and `countRange_point_change` then moves `succ (countRange q' m)`
  to `countRange q m`.

The second of those is where the arithmetic could have gone wrong and did not,
and it is worth recording why no lemma was needed. `countRange_succ` states the
step as `countRange p (succ j) = countRange p j + sel (p j)`, so the two
spellings that have to be reconciled are `add _ (sel true)` against `succ _`
and `add _ (sel false)` against `_`. **Both hold by ιδ**: `sel true` reduces to
`1`, `Nat.add` recurses on its RIGHT argument so `add x 1` reduces to `succ x`,
and `add x 0` reduces to `x`. So `Nat.succ_le_succ` applies to the `add`-shaped
goal directly and the two transports along the `countRange_succ` chain are the
whole of the assembly. Had `Nat.add` recursed on the left, each of those would
have cost an `add_comm`.

The step generalizes over `q` ALONE — one binder fewer than the bijection's
`q, σ, τ` — because `σ` never moves; only the codomain's selected set shrinks.

## Decision, part 2: the carrier level, and dropping the bound premises

```text
Nat.Finset.lt_bound_of_memB : ∀ s i, memB s i = true → Lt i (bound s)

Nat.Finset.card_le_of_injOn : ∀ s t g,
  (∀ i j, memB s i = true → memB s j = true → g i = g j → i = j) →
  (∀ i, memB s i = true → memB t (g i) = true) →
  Le (card s) (card t)

Nat.Finset.pigeonhole : ∀ s t g,
  Lt (card t) (card s) →
  (∀ i, memB s i = true → memB t (g i) = true) →
  (∀ i j, memB s i = true → memB s j = true → g i = g j → i = j) →
  False
```

`card s` IS `countRange (memB s) (bound s)` by δ, so the lift adds no counting
content. What it adds is the **shape of the hypotheses**, and that is a decision.
The loose form has to carry `Lt i n` premises because a `(predicate, bound)`
pair is exactly a pair — nothing connects the two. On the carrier they are
unnecessary in both positions:

- on the DOMAIN, because a caller with `memB s i = true` in hand can always
  recover `Lt i (bound s)`, so demanding it as well is a tax;
- on the CODOMAIN, because the obligation `Lt (g i) (bound t)` is DERIVED from
  `memB t (g i) = true` rather than demanded.

Both go through `lt_bound_of_memB`, which is the contrapositive of ADR-1577's
`memB_of_bound_le` — and that theorem exists with no side condition only
because `memB` truncates inside its own definition. **This is design choice 1
paying for itself a fourth time**, after the three ADR-1577 counted.

`pigeonhole` is then three lines: `card_le_of_injOn` gives `card s ≤ card t`,
`lt_of_lt_of_le` chains it with `card t < card s` to `card t < card t`, and
`lt_irrefl` closes.

## Decision, part 3: TWO strengths, and why the pair cannot be extracted

`Nat.Finset.pigeonhole` REFUTES injectivity. It does not produce the colliding
pair, and the gap between those is not a matter of effort:

> `¬ P` and `∃ witness` are different propositions in a kernel with no
> `funext`, no `propext` and no classical choice. Nothing turns the first into
> the second **by logic**. What can turn it into the second is a DECISION
> PROCEDURE — and injectivity on the members of a `Nat.Finset` has one, because
> the domain is bounded and equality on ℕ is decidable.

So the strong form is a theorem about a bounded double search:

```text
Nat.Finset.exists_collision : ∀ s t g,
  Lt (card t) (card s) →
  (∀ i, memB s i = true → memB t (g i) = true) →
  ∃ a b, memB s a = true ∧ memB s b = true ∧ a ≠ b ∧ g a = g b
```

The search is `allBelow` over `[0, bound s)` twice, at the body

```text
if memB s a then (if memB s b then
                    (if beq (g a) (g b) then beq a b else true)
                  else true)
            else true
```

and is written INLINE rather than as a named `Definition`. That is deliberate,
and it is `count_range_bij.rs`'s own convention: a named `Prop`- or
`Bool`-valued definition could be well-typed and mean something else, and the
kernel could not tell; an inline term appearing only inside a proof cannot
mislead a reader of the statement, because the statement does not mention it.
Nothing in `exists_collision`'s type refers to the loop.

Both directions of the loop are used, one each way, and this is the shape of
the argument:

- **`true`** — `Nat.Finset.allBelow_true_at` (ADR-1577's reflection lemma)
  reads it back as the `Prop` injectivity that `pigeonhole` refutes, so this
  case is impossible and `False.rec` closes it.
- **`false`** — the new `Nat.Finset.allBelow_false_witness` reads it back as an
  index, twice, and the three `Bool` guards are then peeled to give the four
  components of the pair.

```text
Nat.Finset.allBelow_false_witness : ∀ f n,
  Eq Bool (allBelow f n) false →
  Exists (fun i => And (Lt i n) (Eq Bool (f i) false))
```

This is `allBelow`'s third law and it did not exist:
`allBelow_of_all_true` BUILDS the loop, `allBelow_true_at` reads a `true` loop
back pointwise, and neither says anything at all about a `false` one — which is
exactly what a refuted decision hands you. `shape_search --const
Nat.Finset.allBelow --concl Exists` reported ABSENT, and the nearest existing
thing, `Nat.lnp_decidable`, takes a witness as its own hypothesis, which is the
thing that is missing. It is an ordinary induction on the bound whose witness is
COMPUTED by the recursion — at `f j = false` the top index is the answer, at
`f j = true` the guard reduces to the shorter loop and the induction
hypothesis's index is re-introduced at the widened bound — so no choice
principle appears anywhere.

`Nat.beq`'s two reflection lemmas close the peel in opposite directions:
`eq_of_beq_eq_true` on the images, `ne_of_beq_eq_false` on the indices.

**The strongest form this kernel can state is therefore the one that landed**,
and the weaker one is kept rather than superseded: `pigeonhole` is what a
consumer wants when it is deriving a contradiction, and it has three hypotheses
instead of two plus a witness to eliminate.

## The route that was rejected, and its measured cost

The brief named the alternative: `Nat.pigeonhole` (the two-bound RANGE form,
`cardinality.rs`) plus a rank/enumeration identifying a `Nat.Finset`'s members
with `[0, card s)`. It was rejected on a measurement rather than a preference.

`Nat.pigeonhole`'s domain is `[0, n)` and its codomain `[0, m)`. To use it, a
`Nat.Finset`'s members must first be indexed — a function `nth s : Nat → Nat`
enumerating them in order, together with its injectivity on `[0, card s)`, its
`MapsInto` and a proof that its image is exactly the members. Every name that
could hold such a thing is ABSENT (`nthtrue`, `enumerate`, `rankof`,
`selectIndex`, `indexOfNth`, `nthMember`), so all of it is new: a `Definition`
(with the evaluation tests every `Definition` here needs, because the kernel
cannot tell one is wrong), plus an induction for injectivity, plus an induction
for surjectivity onto the members — and the surjectivity half is the same
"remove one point and recount" argument the chosen route uses DIRECTLY.

So the rejected route pays for the enumeration and then still has to do the
work the chosen route does, and it arrives at the range pigeonhole rather than
at the inequality, which is the weaker statement. The chosen route reached
`countRange_le_of_injOn` by deleting three hypotheses from a proof already in
the tree.

**The general form, since it will recur:** when a bijection law exists and an
inequality is wanted, check whether the inequality is the SAME induction with
the surjectivity half struck out before building anything. Here it was, exactly,
and the two branches that changed both got shorter.

## The consumer: an unconditional bound where the bijection gave a conditional
## equality

```text
Rat.rankCols_le_rank : ∀ M rows cols,
  Le (rankCols M rows cols) (rank M rows cols)
```

**No hypothesis at all**, and it is the point of the whole ADR in one line.

`rank_bridge.rs` (ADR-1562) relates `Rat.rank` — a `countRange` over ROWS — to
`Rat.rankCols` — a `countRange` over COLS — through `Nat.countRange_bij` with
the columns on the left. Its own module doc tabulates which of the five
hypotheses cost what: `H1` (injectivity of `σ = pivotRowOfCol`) and `H2` (`σ`
sends a pivot column to a nonzero row) are discharged from the two SEARCHES
alone and know nothing about echelon form, while `H5` — the round trip
`σ (τ r) = r` — is the residue, and it is taken as the *section hypothesis*, the
weakest surviving form of ADR-1554's obligation 4. Everything downstream
(`rank_le_cols_of_pivotSection`, `rank_nullity_rows_of_pivotSection`) inherits
that hypothesis.

`countRange_le_of_injOn` takes exactly `H1` and `H2` and nothing else. So the
inequality in that direction is FREE — the two hypotheses are re-derived
verbatim from `leadingIndex_pivotRowOfCol` and `pivotRowOfCol_lt_rows`, `τ`
never appears, and neither does the section hypothesis.

The asymmetry is real and this lemma does not paper over it. The REVERSE
direction, `rank ≤ rankCols`, is what bounds `rank` by `cols`, and it still
needs the section: in that orientation the injectivity obligation is
injectivity of the LEADING INDEX on the nonzero rows, which IS obligation 4.
Two rows sharing a leading index really can make `rank` exceed `rankCols`, and
nothing can be said about that without the echelon property.

## Every statement is instantiated, and two controls refuse to discharge

No new `Definition` is introduced here, so the "a `Definition` can be well-typed
and mean the wrong thing" hazard does not apply directly. The same hazard
applies to a THEOREM whose statement is not what its name says, and that is what
`nat_prelude/finset_pigeonhole_tests.rs` measures. A `card_le_of_injOn` with its
two `card`s transposed, an `exists_collision` whose pair need not be DISTINCT, a
`pigeonhole` whose strict inequality points the other way: each would be
admitted by the trusted gate, carry an empty axiom footprint, and pass every
sweep in this repository.

Each positive is paired with the specific wrong statement it rules out:

- `card_le_of_injOn` at `({1,2}, range 4, id)` concludes `2 ≤ 4` and NOT
  `4 ≤ 2`, with both `card`s checked independently against their numerals;
- `pigeonhole` at `({1,2}, {7}, const 7)` concludes `False` and NOT `True`;
- `allBelow_false_witness` at `(3 ≤ ·, 5)` states an index where the predicate
  is FALSE, and NOT one where it is true;
- `exists_collision` states a pair that is DISTINCT, and the weakened statement
  with that conjunct dropped — which is trivially true at `a = b` — is required
  not to match;
- `countRange_le_of_injOn`'s whole declared type is rebuilt independently, so an
  inverse, a round trip, or an `Eq` conclusion fails rather than passes.

Three controls are the sharper kind, where a hypothesis cannot be DISCHARGED
rather than a conclusion merely being false: `lt_bound_of_memB` at an index
above the bound, and both `pigeonhole` and `exists_collision` at `range 3` as
the codomain, where `3 < 2` is not provable by `Nat.le_refl 2`.

**The "every declaration" check was rewritten to derive its population from the
kernel.** `finset_tests.rs`'s sibling enumerates a hand-written array of 28
names, which measures the maintainer's memory: a declaration added to
`finset.rs` and forgotten there is checked by nothing. The new one walks
`Kernel::environment()` and takes every declaration rendering under
`Nat.Finset`, then asserts the five names this ADR adds are AMONG them — so a
derivation that silently returned an empty population cannot pass.

## Consequences

- `Nat.Finset` now carries the three cardinality laws a finite-set carrier is
  expected to have: monotone under inclusion (`card_le_of_subsetB`, ADR-1577),
  inclusion–exclusion (`card_union_add_card_inter`, ADR-1577), and cardinality
  of an injection with its pigeonhole corollary (this ADR).
- `Nat.Finset.allBelow` now has all three laws, and the third is the one that
  makes a `Bool`-valued decision usable in the FAILING direction. Anyone adding
  a bounded decision over this carrier should reach for it rather than rebuild
  the search.
- `Nat.countRange_bij` and `Nat.countRange_le_of_injOn` are the two cross-bound
  counting laws, and the choice between them is now a choice about what the
  consumer can supply: an inverse buys equality, an injection buys `≤`.
  `Rat.rankCols_le_rank` is the first consumer to take the second.
- The `finite.rs` range pigeonhole `Nat.pigeonhole` is unchanged and remains the
  right tool for a statement about `[0,n)`; nothing here supersedes it, and the
  enumeration bridging the two is still absent and still unbuilt.

## Alternatives considered

- **The range pigeonhole plus an enumeration.** Rejected on the measurement
  above: it pays for a new `Definition` and two inductions before reaching a
  weaker statement, and one of those inductions is the argument the chosen route
  uses directly.
- **Deriving the inequality from `countRange_bij` by constructing the image
  predicate.** The image of a selected set under `σ` is decidable — it is a
  bounded search — but stating it needs that search built, and applying
  `countRange_bij` to it needs an explicit INVERSE, which is a second search
  plus its correctness. That is strictly more than the direct induction, and it
  reaches the same place.
- **Carrying the `Lt i (bound s)` premises on the carrier-level statements.**
  Rejected: they are recoverable from membership, so demanding them makes every
  consumer prove something twice. The loose `countRange` form keeps them because
  there is nothing there to recover them from.
- **Stating only `exists_collision` and deriving the refutation from it.** The
  derivation would go through the witness and an `Exists.rec` into `False`,
  which works, but it makes the cheap statement depend on the expensive one and
  gives a consumer deriving a contradiction a witness it has to eliminate. Both
  are declared; the refutation is not derived from the pair.
- **Naming the decision loop as a `Nat.Finset.injOnB` definition.** Rejected: a
  named definition would need its own evaluation tests and could mean something
  other than its name, while nothing in either statement mentions the loop.

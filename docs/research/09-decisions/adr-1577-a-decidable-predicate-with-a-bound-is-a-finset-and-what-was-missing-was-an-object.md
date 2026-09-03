# ADR-1577: a decidable predicate with a bound is a `Finset`, and what was missing was an object rather than a proof

Date: 2026-09-03
Status: Accepted
Lane: `finset-role`

Index-summary: Mathlib's `Finset` is a quotient of lists by permutation and
needs `Quot.sound`, which this kernel refuses on purpose. ADR-1520 answered the
same problem for multisets by COMPUTING the carrier instead of extracting it;
this does the same for sets. `Nat.Finset` (`nat_prelude/finset.rs`) is a
one-constructor inductive `mk : (Nat → Bool) → Nat → Finset` — a decidable
membership predicate together with a bound — with `memB` truncating inside its
own definition, `card s := countRange (memB s) (bound s)` and
`sum s f := sumRangeIf (memB s) f (bound s)`. Twelve theorems landed, every one
admitted on the first attempt with `Kernel::axiom_footprint = []`, including
inclusion–exclusion, cardinality monotonicity under decided inclusion, the
disjoint-union sum split, and the reflection lemma for a bounded `Bool`
universal that ADR-1520 explicitly declined to claim about
`Nat.Multiset.eqBelow`. Nothing in the kernel changed and no quotient, `propext`
or `List` appears. THE PIGEONHOLE PRINCIPLE DID NOT LAND and the obstruction is
measured, not guessed: it needs `countRange p n ≤ countRange q m` from an
injection between two selected sets, which `shape_search --hyp Nat.injectiveOn
--concl Nat.le` reports ABSENT; `Nat.pigeonhole` exists but is the RANGE form.
The consumer is `Nat.Finset.card_totatives`, and the survey behind it is the
finding: no site in the tree gets a SHORTER proof from the carrier, because the
predicate-level algebra (`finite_set.rs`) already exists — what was missing was
an OBJECT.
Index-status: Accepted

## Context

Two things `Finset` gives Mathlib had no counterpart here.

**Sums over an arbitrary finite set.** Every sum in this prelude was
`Nat.sumRange f n` over `[0,n)` or `Nat.sumRangeIf p f n` at a predicate spelled
out at the call site. There was no object "the sum of `f` over `{i < n | p i}`",
so a statement about such a sum had to re-spell the predicate and the bound
every time it mentioned the set.

**Cardinality arguments.** `nat_prelude/finite_set.rs` already has the two-set
counting laws at the level of bare predicates —
`Nat.countRange_union_add_inter`, `Nat.countRange_le_of_subset`,
`Nat.countRange_compl` — over `Nat.setUnion`/`setInter`/`setDiff`/`setCompl` and
the `Prop`-valued `Nat.Subset`. What it does not have is a set: `countRange p n`
takes a `(predicate, bound)` PAIR, and nothing carries the two together.

The obvious route is Mathlib's, and it is closed here on purpose: `Finset` is a
`Multiset` with a nodup proof, `Multiset` is a quotient of `List` by `Perm`, and
the quotient needs `Quot.sound`. This kernel has no `List` and admits no
`Quot.sound`.

## Decision

**Represent a finite set over ℕ as a decidable membership predicate together
with a bound past which nothing is a member.**

```text
inductive Nat.Finset : Type
  | mk : (Nat → Bool) → Nat → Nat.Finset

Nat.Finset.memB s i := if i < bound s then pred s i else false
Nat.Finset.card s   := countRange (memB s) (bound s)
Nat.Finset.sum  s f := sumRangeIf (memB s) f (bound s)
```

Order is never represented, so there is nothing to quotient by. That is
ADR-1520's argument transposed, and it is why the axiom footprint of every
declaration below is `[]` — read from `Kernel::axiom_footprint`, not from a
list.

Three design choices carry the whole thing, and each is a decision rather than a
detail.

### 1. `memB` truncates inside its own definition

The alternative is a well-formedness predicate — "this predicate is false above
this bound" — carried as a hypothesis on every downstream statement and as a
proof obligation on every use of `mk`. Truncating instead makes

```text
Nat.Finset.memB_of_bound_le : ∀ s i, Le (bound s) i → Eq Bool (memB s i) false
```

a THEOREM about every `Nat.Finset` with no side condition. `Nat.Finset.mk`
applies to any predicate at any bound.

This is ADR-1520 §1 verbatim, and it pays for itself three separate times below:
in `card_eq_countRange_add` (the tail of the range split is unconditionally
zero), in `sum_eq_sumRangeIf_add` (the tail is zero-VALUED, not merely
zero-counted), and in `card_le_of_subsetB` (at an index outside `s` the `Subset`
obligation is vacuous because its premise is refuted).

The cost is that `pred` is not observable at or above the bound, and that is the
correct semantics rather than a compromise: two sets that agree below their
bounds and disagree above them ARE the same set. The test file pins this in both
directions (`memB (singleton 2) 5 = false` through the truncation branch, while
`memB (singleton 2) 1 = false` through `beq`), so a `memB` that forgot the
truncation fails while a `memB` that always truncated also fails.

### 2. `card` folds `memB`, not `pred`

`Nat.countRange` only reads its predicate below the fold's own bound, so at a
set's OWN bound the two agree. But `union`'s bound is larger than either
operand's, and there `countRange (pred s)` would read `s`'s raw stored predicate
at indices outside `s`. Folding `memB` is what makes `card (union s t)` mean
what it says.

### 3. `union` and `inter` take the SUM of the two bounds, not the maximum

ADR-1520 made the same choice for `Nat.Multiset.add` and gave the reason that
`Nat.max` lives in the `Max` namespace with its comparison lemmas. Here there is
a sharper one, and it is the reason to keep the choice rather than a
rationalisation of it:

> **`Nat.countRange_split` is stated at `countRange f (add m j)`.** With a SUM
> bound it applies LITERALLY — no `Le`-to-`Exists` step through `le_dest`, no
> case analysis on which bound is larger, no `Max` lemma.

That is `Nat.Finset.card_eq_countRange_add`, the workhorse every two-set law
comes back through:

```text
Nat.Finset.card_eq_countRange_add :
  ∀ s j, Eq Nat (countRange (memB s) (add (bound s) j)) (card s)
```

Fold both sets over the common bound `bound s + bound t`, then collapse each
side to its own `card`. The `t` side needs one `add_comm` to put its own bound
in front; that is the entire price of the choice.

## What landed

Twelve theorems, every one admitted on the FIRST attempt, every one with
`Kernel::axiom_footprint = []`.

| theorem | what it says |
| --- | --- |
| `memB_of_lt` | below the bound, membership is the stored predicate |
| `memB_of_bound_le` | at or above it, membership is `false` — no premise |
| `card_eq_countRange_add` | counting past the bound changes nothing |
| `card_union_add_card_inter` | inclusion–exclusion, stated ADDITIVELY |
| `allBelow_of_all_true` | a pointwise fact makes the bounded loop `true` |
| `allBelow_true_at` | **the reflection direction** |
| `card_le_of_subsetB` | cardinality is monotone under decided inclusion |
| `sum_eq_sumRangeIf_add` | summing past the bound changes nothing |
| `sum_union_disjoint` | a sum over a disjoint union splits |
| `sum_congr_of_beq` | sums agree when the decided membership does |
| `card_filter_range` | an ad hoc `countRange` IS a `Finset` cardinality |
| `card_totatives` | …and Euler's totient is one |

Eight facts, one per distinct statement, all `epistemic_status: proved`.

`allBelow_true_at` is worth naming separately. ADR-1520 says of
`Nat.Multiset.eqBelow` — the same bounded-loop shape, specialised to equality of
two `Nat` functions — that `beq_refl` and `beq_comm` are the only two facts
claimed about it and that reflection "is a real theorem and it is not asserted
here". It is asserted here, because without it a `Bool`-valued `subsetB` or
`beq` on this carrier would be decoration: nothing downstream could consume
`subsetB s t = true` as a hypothesis. `card_le_of_subsetB` and
`sum_congr_of_beq` both go through it.

## What this carrier deliberately does NOT provide

- **No `List` and no permutation quotient.** As above. No `propext`, no
  `Quot.sound`, nothing added to the trusted surface.
- **No `Finset.image`.** Mathlib's needs decidable equality on an arbitrary
  type. Here the element type is ℕ, so the image of a bounded set under a
  bounded map is expressible — but nothing needs it and it is not declared.
- **No polymorphism: ℕ only.** `Nat.Multiset` made the same restriction and for
  the same reason: this prelude's fold machinery
  (`countRange`/`sumRange`/`sumRangeIf`) is ℕ-indexed throughout.
- **No extensional equality of sets.** `Nat.Finset.beq` is a `Bool`-valued
  bounded loop. Two sets with the same members but different stored predicates
  above their bounds are NOT `Eq` at type `Nat.Finset`, and nothing here
  pretends otherwise — `sum_congr_of_beq` is the statement that does the work
  extensional equality would have done, and it takes the decided agreement as
  its hypothesis precisely because this kernel has no `funext`.

## What did NOT land, and the measurement

**The pigeonhole principle.** The brief asked for it, stated constructively as
an explicit colliding pair. It did not land, and the obstruction is a missing
independent lemma rather than anything about this carrier:

> A pigeonhole over two `Nat.Finset`s needs
> `countRange p n ≤ countRange q m` **from an injection between the two selected
> sets**. That lemma does not exist.

Measured, not assumed, on a freshly built `shape_search` (`declarations=3095`,
so not a stale artefact reporting a false absence), with the positive control
`Rat.rank_eq_rankCols` returning `FOUND 2`:

```text
shape_search --hyp Nat.injectiveOn --concl Nat.le   ->  ABSENT
   (positive control: any-kind=3095 ns Nat=1088)
shape_search --const Nat.injectiveOn --const Nat.countRange
   ->  FOUND 1: Nat.countRange_permute   (an EQUALITY under a self-map
       permutation of ONE range, not an inequality across two sets)
shape_search --name-like nthtrue / enumerate / rankof   ->  ABSENT (all three)
```

`Nat.pigeonhole` DOES exist —
`∀ m n g, Lt m n → (∀ k, Lt k n → Lt (g k) m) → InjectiveOn g n → False` — and
is the RANGE form: its domain is `[0,n)` and its codomain `[0,m)`, not the
members of two sets. Bridging it to the carrier needs an ENUMERATION of a
`Nat.Finset`'s members as `[0, card s)` — a rank function plus its injectivity —
which the last three searches above report is also absent.

Sizing for whoever takes it, so it is not re-derived: the missing lemma is an
induction on the domain's bound that peels one member at a time and removes its
image from the codomain set, so it needs a "removing one member decreases
`countRange` by exactly one" step. `Nat.countRange_point_change` is the closest
existing piece. This is comparable in size to everything else in this ADR put
together, which is why it was not attempted here rather than attempted badly.

## The consumer, and why it is a bridge

```text
Nat.Finset.card_filter_range : ∀ q n, card (filter q (range n)) = countRange q n
Nat.Finset.card_totatives    : ∀ n,
  card (filter (fun k => beq (gcd k n) 1) (range n)) = totient n
```

The brief asked for a site that "fakes a finite set with an ad hoc `countRange`
over a predicate" to be REWRITTEN through the carrier, projection unchanged. I
surveyed for one and did not find a site where the substitution makes an
existing proof shorter. **That is the finding, and it is a finding about the
tree rather than about this lane.** Every such site already has the
predicate-level algebra it needs, because `finite_set.rs` landed
`setUnion`/`setInter`/`setDiff`/`Subset` with their counting laws before this
carrier existed. Those proofs are already as short as `Nat.Finset` could make
them.

What was missing was not a shorter proof. It was an OBJECT: a way to say "this
set" once instead of respelling a `(predicate, bound)` pair at every mention,
and a way to sum over it.

So the consumer shows the identification instead. `Nat.totient` is DEFINED as
`countRange (fun k => beq (gcd k n) 1) n`, and `nat_prelude/totient.rs`'s own
module doc reads that as `|{k < n : p k = true}|`. `card_totatives` makes that
reading a theorem, with `Nat.totient` and every theorem already proved about it
UNCHANGED. Any future totient argument may now be a set argument —
inclusion–exclusion, monotonicity under inclusion, a sum over the totatives —
and reach `Nat.totient` through this one equation.

## Every definition is evaluated, and one hand computation was wrong

The kernel cannot tell a `Definition` is wrong. A `card` computing the wrong
number would have the right type, an empty axiom footprint, and would pass every
sweep in this repository including both of this ADR's ledger checkers.
`nat_prelude/finset_tests.rs` reduces every operation to a numeral or a `Bool`
at tiny discriminating arguments (the largest bound any fold runs over is 14)
and pairs each positive with the specific wrong formula its negative control
rules out:

- `card ({1,2} ∪ {2,3}) = 3`, not `4` — a multiset-flavoured union;
- `sum {1,3} id = 4`, not `15` — a `sum` that ignored membership and folded
  `[0, bound)`;
- `card (filter (k ≤ 7) (range 5)) = 5`, not `8` — a `filter` that widened the
  bound to its predicate's reach;
- `beq (range 3) {0,1,2} = true` — different bounds, same members.

Two hypotheses are MEASURED to be load-bearing rather than asserted to be:
`sum_union_disjoint`'s, because at the overlapping pair `({1,2}, {2,3})` the two
sides evaluate to `6` and `8`; and `sum_congr_of_beq`'s, because at
`(range 3, range 4)` they evaluate to `3` and `6`.

**One hand-computed expectation was wrong and the test caught it.** The first
draft asserted `bound {0,1,2} = 9`. `union` takes the SUM of its operands'
bounds, so `{0,1,2}` is `(1 + 2) + 3 = 6`, not `3 + 3 + 3`. That is the whole
argument for writing these tests, arriving unprompted.

## Consequences

- `Nat.Finset` adds a fifth non-`Prop` inductive to this prelude (`Nat`,
  `Nat.Fin`, `Nat.Pair`, `Nat.Multiset`, `Nat.Finset`) and the second carrying a
  FUNCTION field. Positivity is trivial (`Nat → Bool` does not mention the
  carrier) and large elimination is available, so `pred` and `bound` are
  ordinary `Finset.rec` projections.
- `Nat.Finset.allBelow` is this prelude's first `Bool`-valued bounded UNIVERSAL
  with a reflection lemma. `Nat.Multiset.eqBelow` is the same shape without one;
  anyone wanting reflection for `eqBelow` should transport `allBelow_true_at`'s
  induction rather than rebuild it.
- `docs/formalized-math-2026-08/09-the-dominance-claim-verified-across-three-domains.md`
  §6's "no `Finset`" is now false as written in the same way ADR-1520 made "no
  multiset" false. Neither ADR edits that document; whoever next revises §6
  should read both.
- The ledger's `depends_on` for all eight facts was completed by
  `check-fact-depends-derived.py --fix`, which DERIVES the edges from the proof
  term. It found nine this lane's hand-written lists had missed.

## Alternatives considered

- **Add `List` plus a `Perm` quotient and follow Mathlib.** This is the route
  the concession assumes is required. It is a much larger change — a new
  inductive family, a permutation relation, a quotient, and `Quot.sound` in the
  trusted surface — and it buys no statement stronger than the ones above for
  these purposes.
- **Keep working at the predicate level and add no carrier.** This is what the
  tree did until now, and it is why `finite_set.rs`'s laws exist. It is
  perfectly sound and it does not give you an object to sum over or to name; the
  moment a statement mentions the same set twice, the `(predicate, bound)` pair
  has to be respelled.
- **Take the MAXIMUM bound for `union`/`inter`.** Rejected under §3: it forces a
  `Le`-to-`Exists` step and a case analysis on which bound is larger at every
  two-set law, in exchange for a tighter bound nothing needs — `card` is
  unchanged by a larger bound, which is exactly what
  `card_eq_countRange_add` says.
- **Carry boundedness as a hypothesis instead of truncating.** Rejected under
  §1, for ADR-1520's reasons and three more of this lane's own.

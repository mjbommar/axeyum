# ADR-1608: The graph carrier forces symmetry and irreflexivity, and R(3,3) = 6 follows

Status: accepted
Date: 2026-09-04
Index-summary: `Nat.Graph` is a decidable relation plus a vertex bound, the sibling of `Nat.Finset`, with symmetry and irreflexivity FORCED inside `adjB` rather than carried as side conditions — which is what lets `HasClique3` quantify over three bare naturals with no range or distinctness conjuncts, and what makes `R(3,3) = 6` a 32-leaf case tree plus one reflected search rather than an enumeration of 2^15 graphs. Hall's marriage theorem lands in its necessity direction only; the sufficiency direction's blocker is named and sized.
Index-status: accepted

## Context

The combinatorics reviewer's file
([07-combinatorics.md](../../math-department/07-combinatorics.md), 2026-09-04)
states the gap in one line: **"No graph carrier at all: no vertices and edges,
no degree, no paths, no trees, no colourings as a defined object. This is the
largest gap and it blocks most of the subject."** Items 2, 3 and 4 of their
Next Five are the graph carrier, Ramsey's theorem for two colours, and Hall's
marriage theorem — roadmap items **W1-6**, **W2-11** and **W2-12**.

A freshly rebuilt `shape_search` index (2,720 declarations; positive control
`Nat.Rado.IsRadoNumber`, landed the same day, FOUND) returns ABSENT for every
one of `graph`, `edge`, `vertex`, `degree`, `walk`, `path`, `reachab`,
`connect`, `ramsey`, `clique`, `independ`, `hall`, `matching`, `marriage` and
`neighb`. So this is genuinely new surface rather than a re-derivation.

Two carriers already existed and this ADR is built entirely on them:

- **`Nat.Finset`** (ADR-1577) — a decidable predicate plus a bound, with `memB`
  truncating **inside its own definition** so `mk` carries no well-formedness
  obligation, and `card` as `countRange`.
- **the pigeonhole family** (ADR-1593) — `Nat.Finset.card_le_of_injOn`,
  `Nat.Finset.pigeonhole`, and the constructive `exists_collision`.

## Decision

### 1. `Nat.Graph` is `Nat.Finset`'s sibling, and the guards live in `adjB`

`crates/axeyum-lean-kernel/src/nat_prelude/graph.rs`:

```text
inductive Nat.Graph : Type
  | mk : (Nat → Nat → Bool) → Nat → Nat.Graph

Nat.Graph.rel   g : Nat → Nat → Bool   -- the stored relation, raw
Nat.Graph.order g : Nat                -- vertices are [0, order)
Nat.Graph.adjB  g i j :=
  andB (andB (i < order g) (j < order g))
       (andB (neB i j) (andB (rel g i j) (rel g j i)))
```

The alternative designs, and why they were rejected:

**(a) Symmetry and irreflexivity as `Prop` fields of the constructor, or as
separate predicates hypothesised on every downstream statement.** Rejected for
ADR-1577's reason, sharpened by what this carrier is *for*: a graph produced by
an untrusted search is the whole point of having it, and under (a) that graph
cannot be transcribed into the kernel without also transcribing two proofs about
it. Under the chosen design `Nat.Graph.adjB_symm` and `Nat.Graph.adjB_irrefl`
are theorems about **every** graph with no premise, and
`Nat.Graph.ramsey33Witness` is a bare relation — exactly as
`Nat.Rado.schurSet` is a bare `Nat.Finset` (ADR-1596).

The payoff is not stylistic and it is measurable. `Nat.Graph.HasClique3` is

```text
HasClique3 g := ∃ a b c, adjB g a b ∧ adjB g b c ∧ adjB g a c
```

with **no** range conjuncts and **no** distinctness conjuncts, because
`Nat.Graph.lt_order_of_adjB` recovers `a < order g` from an edge and
`Nat.Graph.ne_of_adjB` recovers `a ≠ b`. Under (a) each of the three
existentials would carry six extra conjuncts, and every proof below would have
to pack and unpack them. Only the range half is consumed here — `ne_of_adjB` is
declared as a law of the carrier and no proof in this ADR calls it, because a
triangle's vertices being distinct is never needed downstream of the
existential; it is stated so that a consumer who does need it has it, and it is
covered by the axiom-freedom sweep like everything else.

**(b) Symmetrization by disjunction (the symmetric closure) instead of
conjunction.** Rejected because it silently promotes a one-sided entry to an
edge: a search emitting a directed adjacency table by mistake would get a graph
carrying edges it never asserted. With conjunction the failure direction is the
safe one — a malformed table yields FEWER edges, never more.
`graph_tests::a_one_sided_relation_is_not_an_edge` pins this with a deliberately
asymmetric relation, and states the number the disjunctive reading would give.

**(c) A `Nat.Finset` of edges (a set of pairs).** Not written down as a
candidate for long: `Nat.Finset` is `Nat`-indexed, so an edge set needs a
pairing function, and every adjacency query becomes a `Nat.pair`/`unpair` round
trip. The relation form is what the downstream proofs actually consume.

Neighbourhoods and degrees come free from the sibling relationship:
`neighbors g v := Nat.Finset.mk (adjB g v) (order g)` needs no conversion, and
because `adjB` truncates, `Nat.Graph.memB_neighbors` says membership in the
neighbourhood **is** adjacency at every index with no side condition.
`degree g v := Nat.Finset.card (neighbors g v)`, so
`Nat.Graph.degree_le_order` is one application of `Nat.countRange_le`.

### 2. `Nat` gets a named `Bool` algebra, filed under `Nat.Graph`

Every previous user of a `Bool` conjunction in this prelude spelled a `Bool.rec`
inline. `adjB`'s symmetry proof needs commutativity as a *named* lemma — the
inline form would be eight cases at every use — so `graph.rs` declares
`Nat.Graph.andB`, `orB`, `notB`, `neB` and the five `andB` laws
(`andB_comm`, `andB_false_right`, `andB_intro`, `andB_left`, `andB_right`).

**This is the "general infrastructure filed under its first consumer's module"
hazard from [finding-existing-lemmas.md](../../contributor-guide/finding-existing-lemmas.md),
entered deliberately and recorded here so the next lane finds it.** `hall.rs`
already imports `Nat.Graph.andB_intro`, which is the first evidence that the
names want to move to a `Nat.Bool` namespace. They were not moved now because
the move is a rename across two preludes and this ADR is already a large diff;
a lane that needs a third `Bool` combinator should do it.

### 3. `R(3,3) = 6`, both halves in the kernel

`crates/axeyum-lean-kernel/src/nat_prelude/ramsey.rs`:

```text
Nat.Graph.compl g            := mk (fun i j => notB (adjB g i j)) (order g)
Nat.Graph.Arrows33 n         := ∀ g, n ≤ order g → HasClique3 g ∨ HasClique3 (compl g)
Nat.Graph.IsRamseyNumber33 n := Arrows33 n ∧ ∀ k < n, ¬ Arrows33 k
Nat.Graph.ramsey_three_three : IsRamseyNumber33 6
```

A two-colouring of the edges of a complete graph **is** a graph — one colour
class is `g`, the other is `compl g` — so no colouring object is needed and the
statement is the classical one.

**`Arrows33` is stated with `Le n (order g)`, not `order g = n`.** An equality
hypothesis would force every vertex bound to be transported through it; with
`Le`, the bound `k < order g` is `le_trans` against a concrete `Le (succ k) n`,
and monotonicity (`Nat.Graph.arrows33_of_le`: a larger order is a *stronger*
hypothesis, hence a weaker statement) is three lines. Monotonicity is what makes
"least" and "false at the predecessor" the same statement, which is what
`Nat.Graph.isRamseyNumber33_of_succ` cashes in — the same reduction
`Nat.Rado.isRadoNumber_of_succ` provides, with `m` left a variable.

**The upper bound is a proof, not an enumeration, and it had to be.** There are
`2^15 = 32768` graphs on six vertices, but the number is not the obstacle: a
graph is a *function* stored in the carrier, so the kernel cannot case over "all
graphs" at all, and the `2^5`-colouring enumeration `Nat.Rado.schur_arrows_five`
uses has no analogue here. What is encoded instead is the textbook argument, as
a case tree over the **five edges at vertex 0** — 32 leaves — where each leaf
applies one of two shared four-leaf lemmas:

- `Nat.Graph.triangle_or_indep` — three neighbours of `v`: either two of them
  are adjacent (a triangle with `v`) or all three are pairwise non-adjacent (a
  triangle of the complement). The vertex bounds the complement branch needs are
  recovered from the three edges, not assumed.
- `Nat.Graph.antitriangle_or_indep` — the mirror image for three
  non-neighbours. Non-adjacency carries no bound, so this one does take the four
  bounds and the `v`-vs-`x` distinctness facts as hypotheses; at the 32 call
  sites they are `le_trans` against a concrete bound and `Eq.refl Bool false`.

The pigeonhole step ("three of five share a colour") is discharged by the
enumeration itself: the builder computes the majority class at each leaf, and a
Rust `assert!` fires if some leaf has fewer than three on both sides. So the
emitted term has 32 leaves rather than 256, and the two eight-line lemmas are
each proved once.

**The lower bound is a search, checked by reflection.**
`ramsey::search_ramsey_lower` enumerates the `2^10` graphs on five vertices and
returns the first with neither a triangle nor an independent triple:
`{0-3, 0-4, 1-2, 1-4, 2-3}`, the five-cycle relabelled, which is the unique such
graph up to isomorphism. Nothing about the search is trusted — the certificate
is transcribed as `Nat.Graph.ramsey33Witness` and the kernel *recomputes* both
refutations through `Nat.Graph.noClique3B`, a `Bool` triple loop over
`Nat.Finset.allBelow` whose `true` value `Nat.Finset.allBelow_true_at` reads
back at the three existential witnesses.

**The exit status depends on the finding.** If the search returned `None`,
`declare_lower_bound` declares nothing and `ramsey_three_three` names a theorem
that does not exist, so the kernel rejects it and the whole `Nat` prelude fails
to build. There is no path on which a failed search yields a green suite.

### 4. Hall's marriage theorem: necessity only, and the blocker is named

`crates/axeyum-lean-kernel/src/nat_prelude/hall.rs` declares `Nat.Hall.anyBelow`
(the bounded existential decision `Nat.Finset` lacked), `unionBound`,
`unionOver`, `IsMatching` and `HallCondition`, and proves

```text
Nat.Hall.hallCondition_of_isMatching : ∀ s nb f, IsMatching s nb f → HallCondition s nb
```

which is one application of `Nat.Finset.card_le_of_injOn` and **no new counting
machinery** — which is the point of the exercise the reviewer set ("the standard
test of whether a finite-set library is usable").

Two choices worth recording. `unionOver` computes its own bound as the
`Nat.sumRange` of the members' bounds, not their maximum, for ADR-1577's reason:
`Nat.le_sumRange_of_lt` is stated at `sumRange` and applies literally, with no
case analysis on which member's bound is largest. And inclusion in
`HallCondition` is spelled **pointwise** rather than through
`Nat.Finset.subsetB`, because `finset.rs` carries no reflection lemma taking
`subsetB s t = true` back to pointwise membership — only `card_le_of_subsetB` —
and every consumer has the pointwise fact already.

**The sufficiency direction is not proved, and it is not blocked by a missing
lemma.** Three pieces of machinery are missing, in increasing order of how much
they are actually new:

1. **Strong induction on `card s` with the family varying.** The textbook proof
   splits on whether some proper non-empty `t ⊂ s` is *critical*
   (`card t = card (unionOver nb t)`) and recurses on two strictly smaller
   families. This kernel's `Nat.rec` recurses on a numeral, so the motive has to
   be `∀ k, ∀ s nb, card s ≤ k → …`, quantifying over `Nat.Finset` and
   `Nat → Nat.Finset`. **There is no `Nat.strongInduction` here** — a
   `shape_search --name-like` sweep for `strong`, `strong_induction` and
   `le_induction` returns ABSENT, and `Nat.base_induction` is a different
   statement. What exists is `Nat.lt_well_founded : WellFounded` plus the
   generic `WellFounded.fix`, which is sufficient but unwrapped. Bookkeeping
   over machinery that exists, then, but the wrapper is part of the
   bookkeeping.
2. **Deleting from a family.** Both branches build
   `fun i => Nat.Finset.sdiff (nb i) (unionOver nb t)` and a new index set, and
   must transport Hall's condition across the change. `sdiff` and the counting
   laws exist; no lemma relates `unionOver` of a modified family to `unionOver`
   of the original. Bookkeeping, but more of it.
3. **Choosing the critical subfamily — this is the real one.** The split needs
   *some* critical `t` or a proof that none exists, which is a search over the
   `2^(bound s)` subsets of `s`. This kernel has no classical choice, so the
   subset must be COMPUTED, together with its own reflection lemma. Nothing of
   that shape exists. `Nat.Finset.allBelow_false_witness` is the
   one-dimensional analogue and is the model to copy; the work is the same kind
   `Nat.Finset.exists_collision` needed for the constructive pigeonhole
   (ADR-1593), and a lane should size that primitive first and treat items 1 and
   2 as consequences.

`Nat.Hall.anyBelow` is declared with its introduction rule only for the same
reason: the elimination rule (a `true` `anyBelow` yields a witness) is a
one-dimensional instance of exactly the missing primitive.

### 5. Walks and connectivity: deliberately not in this ADR

The reviewer's item 2 names "degree, walks, and connectivity". Degree and
neighbourhoods landed; **walks and connectivity did not**, and the reason is a
scoping judgement rather than an obstacle. The intended shape is an inductive
`Nat.Graph.Reachable (g) (u) : Nat → Prop` with `refl` and `step`, plus a
`Bool`-decidable `walkB g w n` over `Nat.Finset.allBelow` and a bridge
`walkB … = true → Reachable g (w 0) (w n)` by induction on `n`. Symmetry and
transitivity of `Reachable` are two further inductions over the new family
(symmetry needs a "prepend an edge" lemma first). Nothing in that plan is
blocked — `add_inductive` admits indexed `Prop` families here, and
`Nat.Finset.allBelow_of_all_true`/`allBelow_true_at` are exactly the two laws
the bridge consumes — it is simply a second lane's worth of proof terms, and
`R(3,3)` was the higher-value half of the same item.

## Consequences

**What this costs.** The `Nat` prelude's own test sweep went from roughly 18 s
to 35-55 s wall (`--release`, `--test-threads=4`; two runs on the same commit
gave 55 s under load 22 and 35 s under load 15, so read the spread rather than
either number, per the reference-frame rule), and essentially all of the
increase is the Ramsey proof terms — the 32-leaf case
tree and the two `noClique3B` reductions (125 triples each, twice, once through
`compl`). That is a real tax on every lane's gate and it should be watched: a
`R(3,4)` or `R(4,4)` attempt by the same method would multiply the tree, and the
right response would be to move the enumeration behind a feature gate rather
than to make the leaves cheaper.

**What it enables.** The reviewer's remaining items are now downstream of a
carrier rather than of nothing: Turán, Dilworth, colourings as a defined object,
and the tree/forest vocabulary all take `Nat.Graph` as given. `Nat.Rado`'s
colourings and `Nat.Graph`'s complement are the same idea at different arities,
and a lane unifying them would get van der Waerden's statement for free.

**What must not be inferred.** `R(3,3) = 6` is a *theorem here*, not a new
result — it is the canonical first theorem of the subject and its
`external_status` is `established`. The claim this ADR supports is about the
library's reach, not about mathematics.

## Mutation table

The general finding first, because it is the useful one: **almost every mutation
of a definition in this lane is caught by the kernel at prelude-build time, not
by a test.** Each definition is named by at least one theorem whose proof term
mentions its unfolding, so changing the definition makes that proof fail to
type-check and the whole `Nat` prelude fails to build — which is why the
evaluation tests were written for exactly the residue the kernel cannot see:
the pure *value* choices no theorem constrains.

| mutant | what happens | signal |
|---|---|---|
| `adjB` symmetrizes by **disjunction** instead of conjunction (`and_b(rij, rji)` → `orB`) | `Nat.Graph.adjB_symm` no longer type-checks — its proof runs on `andB_comm` and there is no `orB` counterpart — so the prelude fails to build. Run under `nat_prelude::` `--release --test-threads=4`: **40 FAILED, 0 ok** before it was stopped at 12 min (each test rebuilds the prelude, so a rejected declaration costs the whole sweep). | caught by the KERNEL, not by a test. The design choice is pinned by `adjB_symm` itself; `graph_tests::a_one_sided_relation_is_not_an_edge` is the *readable* pin, not the only one |
| any change to `degree`, `neighbors`, `compl`, `unionOver`, `unionBound`, `anyBelow`, `neB` | each is named by a theorem (`degree_le_order`, `memB_neighbors`, `adjB_compl_of_not_adjB`, `memB_unionOver`, `anyBelow_of_witness`, `adjB_irrefl`) whose proof supplies a term at the un-mutated type | caught by the kernel |
| a theorem's STATEMENT slid by one numeral | not visible to the kernel at all | caught by the accept/reject pairs: `ramsey_three_three` at `IsRamseyNumber33 5`, `ramsey33_arrows_six` at `Arrows33 5`, `ramsey33_not_arrows_five` at `Arrows33 6 → False`, and `hallCondition_of_isMatching` at the CONVERSE implication, are each offered to the trusted gate with the same proof term and must be REJECTED |
| a new declaration added and left unwatched | not visible to any test that lists its own subject | caught by `nat_prelude_tests::every_nat_declaration_is_checked_and_axiom_free`, which derives its subject from the live environment. It **failed on its first honest run against this diff**, naming all 22 `Nat.Graph` declarations, and that is a real observed failure rather than a hypothetical |

## Verification

- `nat_prelude::` — 491 passed, 0 failed (`--release`, `--test-threads=4`).
- `nat_prelude_tests::every_nat_declaration_is_checked_and_axiom_free` derives
  its subject from the live environment, not from a literal, and it FAILED on
  the first honest run against this diff, naming all 22 new `Nat.Graph`
  declarations. Every declaration here is now registered in `definition_names`
  or `theorem_names` and so is covered by the kind, determinism and
  axiom-footprint sweeps.
- Every new `Definition` has an evaluation test at concrete small arguments with
  a named wrong formula: `graph_tests.rs` (a triangle has every degree `2`, a
  path on three vertices has degrees `1, 2, 1`, a one-sided relation is not an
  edge), `ramsey_tests.rs` (the complement inverts adjacency and stays
  truncated; `noClique3B` is `true` on the witness and its complement and
  `false` on a graph that does have a triangle), `hall_tests.rs` (`anyBelow` is
  the existential and disagrees with `allBelow` on the same predicate;
  `unionOver` collects and does not intersect).

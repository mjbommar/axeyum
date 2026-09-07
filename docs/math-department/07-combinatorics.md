# 07 — Combinatorics

Reviewer: a combinatorialist — enumerative, extremal, Ramsey theory
Verdict, 2026-09-06: **a real first course, with the two shelves now joined at
two points — and the joins are the reason to keep reading**
Last measured: 2026-09-06 at `5fa2e3feb`

> "Two days ago your library proved the pigeonhole principle and separately
> computed a four-colour Rado number, and the two facts did not know about
> each other. Now Schur's number and R(3,3) are theorems whose existence
> halves came out of a search. That is the thing I came here to see."

> **AUDITED 2026-09-04.** Every absence claim in the 2026-09-04 reading was
> re-checked against a freshly rebuilt kernel index. See
> [AUDIT-2026-09-04.md](AUDIT-2026-09-04.md) for that evidence. Across the
> twelve files, 11 of 76 absence claims were false and 12 more overstated the
> gap; the cause is that the ledger characterises only 38% of its proved facts
> and does not cover 430 kernel theorems at all (ADR-1605) — **that 430 is not
> reproducible by its own method and is retired; the measured figure is 721 of
> 3,079 registered theorem names uncovered, ADR-1674**.
>
> **RE-MEASURED 2026-09-06** at `5fa2e3feb`, from a kernel index built the
> same day (4,765 declarations with `--include-constructed`; 3,311 in the
> default groups). The 09-04 audit still missed four things in this field —
> the binomial theorem, Vandermonde's convolution, the Catalan numbers and
> `Nat.multichoose` were all on `main` before that audit ran and were listed
> as absent anyway. Each correction is marked **[RE-MEASURED]** below.

> **Retired 2026-09-06 (ADR-1674):** the 430 is not reproducible by its own
> method - three later readings give 599, 620, 721 and 973 on three different
> denominators. The measured, gated figure is **721 of 3,079 registered
> kernel theorem names uncovered**, ratcheted by `gen-ledger-coverage`.

## The persona

Counts things, bounds things, and finds structure in large enough
configurations. Works with finite sets, multisets, generating functions,
graphs, and Ramsey-type existence results. Comfortable with computer search as
a proof technique and unusually receptive to machine-checked certificates,
because their subject already lives with results no human verified by hand.

## What the library has today

**The two shelves have met, twice.** The elementary carriers and the
search-produced results are no longer separate populations: Schur's number and
R(3,3) are kernel theorems whose existence halves came out of a search and
whose exhaustiveness halves are proof terms. The four-colour Rado numbers are
still on the other side of the line, and for a measured reason.

**Combinatorial carriers, counted from the kernel** (namespace census of a
`shape_search` build at `5fa2e3feb`; 241 declarations in six namespaces):

| namespace | declarations | detail |
|---|---|---|
| `Nat.Finset` | 77 | ADR-1577; a decidable predicate on a bounded range, `card` as `countRange`, `memB`, `allBelow`, union/intersection/difference counting laws, `filter`, `sum`, the empty/singleton shelf (ADR-1630), `encode`/`decode` subset search (ADR-1614) |
| `Nat.Subsets` | 41 | ADR-1624; sums indexed by subsets, a subset as a `Nat → Bool` predicate, `inclusion_exclusion`, `inclusion_exclusion_pos`, `inclusion_exclusion_two` |
| `Nat.Graph` | 39 | ADR-1608; a decidable adjacency table with symmetry and irreflexivity forced *inside* `adjB` by conjunction, `neighbors` as a `Nat.Finset`, `degree`, `compl`, and the R(3,3) apparatus |
| `Nat.Multiset` | 38 | ADR-1520; multiplicity, product, the two divisibility laws, and (2026-09-06, ADR-1658) `restrict`/`prodSel` with `prodSel_dvd_prod` and `prodSel_injective` |
| `Nat.Hall` | 30 | ADR-1645; `unionOver`, `HallCondition`, `IsMatching`, `criticalB`, the split lemmas, and `marriage_iff` |
| `Nat.Rado` | 16 | ADR-1596; `Sol`, `IsColouring`, `MonoSol`, `Arrows`, `IsRadoNumber`, `ofFinset`, and Schur's two halves (a 17th declaration, `Nat.boolSelect_lt`, is built by the same module outside the namespace, which is why the roadmap row says 17) |

**Elementary results, outside those namespaces:**

| item | detail |
|---|---|
| pigeonhole | both forms: the range form (`Nat.pigeonhole`) and the Finset form (`Nat.Finset.pigeonhole`, ADR-1593), with `card_le_of_injOn` and the constructive `exists_collision` witness pair |
| binomial coefficients | `Nat.choose` with Pascal's rule (`choose_succ_succ`), symmetry, "a coefficient above the diagonal is zero", "bounded by the corresponding power of two", "a prime divides the interior coefficients of its own row", the row sum `sum_choose_row` and the squared row sum `sum_choose_sq` |
| the binomial theorem | **[RE-MEASURED]** `Nat.add_pow` is a kernel theorem over ℕ (`nat_prelude/binomial.rs`), and `Complex.add_pow` states it over ℂ. Both were already on `main` on 2026-09-04 |
| Vandermonde | **[RE-MEASURED]** `Nat.choose_add_convolution` **is** Vandermonde's convolution, `choose (m+n) k = Σ_{i≤k} choose m i · choose n (k−i)` (`nat_prelude/vandermonde.rs`, landed `0fbe989bc` 2026-08-24). The 09-04 reading called it "the addition convolution (Pascal)" and then listed Vandermonde as missing; both halves of that were wrong |
| Stirling numbers | `Nat.stirlingFirst` and `Nat.stirlingSecond` with 10 theorems between them (8 and 2), landed `33cae3575` 2026-08-31 |
| Catalan numbers | **[RE-MEASURED]** `Nat.catalan` in closed form, `choose (2n) n − choose (2n) (n+1)`, with `Nat.catalan_mul_succ` (fact `F:nat-catalan-mul-succ`, `proved`). Never mentioned in the 09-04 reading |
| multiset coefficients | **[RE-MEASURED]** `Nat.multichoose` with its boundary lemmas, and `Nat.ascFactorial`/`Nat.descFactorial` (landed `771d2d23c` 2026-08-28) |
| `List` and `List.Perm` | ADR-1579/1583, extended `c1ed177ef` 2026-09-03: permutation as a `Bool` predicate with reflexivity, symmetry, reverse-invariance and append-commutativity, and per-element counts agreeing between a list and its multiset |
| lattice counting | `sumRange_split`, `sumRange_rect_eq_diag_add_corner`, `countRange_union_add_inter`, and a rectangle-of-lattice-points partition result |

**Results that came out of a search:**

- **Schur's number: `Nat.Rado.schur_two : IsRadoNumber 1 1 2 5`** — a kernel
  theorem with an empty footprint. The upper bound is a case tree over the 2⁵
  colourings; the lower bound reflects a `Nat.Finset` the search picked. Fact
  `F:rado-r2-schur-two`, `proved`/`proved`.
- **`Nat.Graph.ramsey_three_three` — R(3,3) = 6**, both directions. The upper
  bound is a 32-leaf case tree over the five edges at vertex 0; the lower
  bound is a search over the 2¹⁰ five-vertex graphs returning the five-cycle,
  re-checked by reflection. Fact `F:ramsey-r33-six`, `proved`/`proved`.
- **The four-colour Rado numbers of 5(x−y) = 3z (625) and 5(x−y) = 4z (741)**
  remain `epistemic_status: computed` — search plus a checkable certificate,
  not a kernel proof term. They are still genuine extremal results of the kind
  their field publishes.

**Ledger position, measured.** 59 facts match this field's pattern; 57 are
`proved` and exactly 2 are `computed` — the two four-colour Rado numbers.
Ledger-wide the count is 2,954 facts, 2,678 proved, 1,576 landmark
(`scripts/count-landmark-facts.py`).

## Their verdict

**The elementary shelf is no longer thin.** Six carriers, 241 declarations,
built in an order that holds up: `countRange` first, then `Finset` as a
decidable predicate over it, then the counting laws, then pigeonhole as a
consequence, then Hall on top of `card_le_of_injOn`, then graphs and Ramsey on
top of the `Finset` machinery. The Finset pigeonhole still delivers a *witness
pair* computed by bounded search, and by now three separate results
(`exists_memB_of_card_pos`, the subset search, the critical-subset decision)
use the same device, so it is a working method here and not a one-off.

**Hall's marriage theorem is the load-bearing item.** `Nat.Hall.marriage_iff`
is an iff, footprint empty, proved by strong induction on the size of the
index set with the critical-subset split decided by bounded search. It took
six lanes over two days, and the interesting part is that every one of them
estimated the remaining work at "assembly" and every one was short by exactly
one lemma nobody had measured. That is what a finite-set library costs when it
is honest about it.

**The Rado join is the result this reviewer would cite.** Determining a Rado
number is a large finite search with a colouring on one side and an
exhaustiveness argument on the other, and it is exactly the shape their field
farms out to SAT solvers. Here both halves land inside the kernel, against a
*defined* `IsRadoNumber`, for the two-colour case.

**Where the shelves have not met is now a measured boundary, not a gap in the
design.** `IsRadoNumber 5 3 4 625` type-checks — a `Prop` that mentions a
numeral never reduces it — so the unary-numeral objection in the 09-04 reading
was wrong and is retracted below. What blocks the four-colour cases is
combinatorial: `Arrows 5 3 4 625` quantifies over 4⁶²⁵ colourings, colourings
are *functions*, and the kernel cannot enumerate a function space. The same
wall is why R(3,3)'s upper bound had to be a case tree over the edges at one
vertex rather than a case split over all graphs, and why R(3,4) needs the
Ramsey recurrence rather than a bigger tree. Both `computed` facts are
correctly `computed`.

## What they would say is missing

- **Graph theory past the carrier.** `Nat.Graph` has adjacency, degree,
  neighbours and complement. Measured absent, in the same 4,765-row index that
  answers for all of those: walks, paths, connectivity, trees, and graph
  colourings as a defined object. `Nat.Rado.IsColouring` is a colouring of an
  integer range, not of a graph. This is now the largest gap in the field.
- **Ramsey theory as theory.** Two *numbers* are proved; no general theorem
  is. There is no Ramsey recurrence, no R(s,t) statement, and no van der
  Waerden (measured absent: zero matches for `waerden|arithProg|progression`
  in the full index). Schur's theorem in general form is likewise absent —
  only `R_2(x = y + z) = 5`.
- **Extremal results.** Hall's theorem landed; **Turán, Dilworth, Sperner,
  König and Menger are all still absent** (zero matches for any of those names
  in the 4,765-row index).
- **Generating functions.** Still absent — and the stated prerequisite is
  discharged. `AlgS.Poly` is now a full commutative ring over an abstract
  `AlgS.CommRing` — 26 declarations under `AlgS.Poly`, including the
  `AlgS.Poly.commRing` instance (ADR-1618) — so polynomials are no longer
  the blocker. What is missing is *formal power series*: infinite support, and
  a coefficient-extraction calculus. `CReal.powerSeries*` is analysis — a
  convergent real series with a radius — and is not this.
- **Enumerative identities beyond the ones listed.** The hockey-stick identity
  (Σ over i of choose i k = choose (n+1) (k+1)) is absent; `sum_choose_row`
  and `sum_choose_sq` are row sums, not it. The binomial theorem exists over ℕ
  and ℂ but **not over an abstract commutative ring** — `AlgS` has `sumRange`
  and its laws over `OrderedRing`, and `Alg.pow_add` is the exponent law, not
  the expansion.
- **Asymptotics.** No O-notation, no Landau symbols, no Stirling's
  *approximation* (distinct from the Stirling numbers, which are present).
  `Metric.TendsTo`/`TendsToAt` are the analysis-side limits and nothing
  connects counting to them.
- **Möbius inversion.** `Nat.moebius*` exists (ADR-1619) and the alternating
  sum over a non-empty ground set vanishes in one line, but the
  divisors-of-squarefree-*n* ↔ subsets-of-primes bijection is only half built:
  the injective half landed 2026-09-06 as `Nat.Multiset.prodSel_injective`;
  surjectivity and the sum transfer did not (ADR-1658).

## The blocker

**Very little, and one thing that is genuinely hard.** Everything on the list
except generating functions and asymptotics is finite, decidable and
constructive. A graph is already a decidable relation on a bounded range;
walks and connectivity are a bounded search over the same shape as the subset
search Hall needed.

The three real constraints, each measured:

- **Function spaces, not numerals.** The 09-04 reading blamed unary numerals
  for keeping the Rado numbers outside the kernel. That was checked and is
  false: a `Prop` mentioning `625` never reduces it. The real constraint is
  that a statement quantifying over *colourings* quantifies over functions,
  and the kernel has no way to enumerate them. Every "prove this specific
  Ramsey-type number" item runs into this, and the workaround each time is a
  case tree over a small structured set of decisions — the edges at a vertex,
  the values of a small colouring — rather than over the function space.
- **Unary numerals bound reduction, not statement.** Where a proof must
  *compute* with a large constant — a search re-checked by reflection at some
  width — cost is superlinear in the largest magnitude formed. This is why the
  R(3,3) lower bound could reflect over 2¹⁰ graphs and the four-colour Rado
  search cannot.
- **Formal power series need an infinite-support carrier**, which `AlgS.Poly`
  is not. That is a carrier decision the algebra shelf has not taken
  ([04-algebra.md](04-algebra.md)).

## The first five, all landed

- [x] **1. Define Rado numbers over `Nat.Finset` and connect the computed
      results to a kernel statement.** *Landed `de0cd02da` 2026-09-04:
      `Nat.Rado.schur_two : IsRadoNumber 1 1 2 5`, both halves from search;
      16 declarations under `Nat.Rado`, footprint 0 (ADR-1596).*
- [x] **2. A graph carrier.** *Landed `0a499a6d8` 2026-09-04: `Nat.Graph`, 39
      declarations under the namespace today, footprint 0 (ADR-1608). Walks
      and connectivity were deliberately out of scope and are still absent.*
- [x] **3. Ramsey's theorem for two colours.** *Landed `0a499a6d8`:
      `Nat.Graph.ramsey_three_three`, R(3,3) = 6 in both directions. The
      general theorem did not land and is back on the list below.*
- [x] **4. Hall's marriage theorem.** *Landed `2c9c666f8` 2026-09-05 as
      `Nat.Hall.marriage_iff`, six slices over two days, footprint 0
      (ADR-1614, 1623, 1630, 1644, 1645). 30 declarations under `Nat.Hall`.*
- [x] **5. General inclusion–exclusion.** *Landed `4858a75dc` 2026-09-05:
      `Nat.Subsets.inclusion_exclusion` and `…_pos`, 41 declarations,
      footprint 0 (ADR-1624); the two-set case is kernel-checked equal to the
      pre-existing `countRange_union_add_inter`.*

## The next five, chosen 2026-09-06

- [ ] **1. Walks, paths and connectivity on `Nat.Graph`.** Measured absent. A
      walk is a bounded list of vertices with a decidable adjacency check at
      each step, and connectivity is a bounded search of the same shape the
      subset search already provides. It gates every remaining graph result
      and it needs no new device.
- [ ] **2. The Ramsey recurrence, R(s,t) ≤ R(s−1,t) + R(s,t−1).** Two Ramsey
      numbers are proved and no Ramsey *theorem* is. The recurrence is the
      induction the subject actually uses, it is downstream of the degree
      counting `Nat.Graph` already has, and it is what makes R(3,4) reachable
      without a bigger case tree.
- [~] **3. Finish the divisors ↔ subsets bijection and land Möbius
      inversion.** *Half landed on `main`* (`236c37763`, `1718bad75`,
      `2e342d998`, 2026-09-06, ADR-1658): `Nat.Multiset.prodSel_injective` is
      the injective half. Surjectivity and the range-to-subset sum transfer
      are open. A follow-on lane (worktree `agent-a1091c1a778ac0d53`, three
      commits, a masked subset fold plus a divisor-valuation bound) is **not
      on `main`** and is not counted anywhere in this file.
- [ ] **4. Turán's theorem, or Dilworth's.** Both measured absent; both are
      the standard proof that a finite-graph or finite-order library is usable
      for extremal work rather than only for definitions. Turán is the more
      natural fit now that `degree` exists.
- [ ] **5. The binomial theorem over an abstract commutative ring.** It is
      proved over ℕ (`Nat.add_pow`) and over ℂ (`Complex.add_pow`).
      `AlgS.OrderedRing` already carries `sumRange` with its congruence and
      splitting laws, and `AlgS.Poly` is a `CommRing`, so this is a
      generalisation of an existing proof rather than a new one — and it is
      the first step toward the coefficient calculus generating functions
      need.

## Progress log

| date | change | evidence |
|---|---|---|
| 2026-09-04 | File created. Baseline: `Nat.Multiset`, `Nat.Finset`, pigeonhole in both forms, binomial coefficients with Pascal, `List.Perm`. Two four-colour Rado numbers `computed` and not connected to any kernel statement. No graphs. | ledger snapshot at `1856cdb3c` |
| 2026-09-04 | **Next Five item 1 landed** (roadmap W1-1), and it is the flagship: `nat_prelude/rado.rs`, 17 declarations with empty footprints, and **Schur's number `R_2(x = y + z) = 5` proved in-kernel with both halves discharged from search** — the upper bound by a case tree over 2⁵ colourings, the lower by reflection over a `Nat.Finset` colouring the search picked. `Nat.Finset` is shown to *be* a 2-colouring with no side condition. **The unary-numeral worry in this file was wrong**: `IsRadoNumber 5 3 4 625` type-checks, because a `Prop` that mentions a numeral never reduces it. The real residue is combinatorial — the four-colour proof term ranges over 4⁶²⁵ colourings, which are functions and not enumerable in-kernel — so both `computed` facts correctly stay `computed`. [AUDIT] Stirling numbers were already present. | `de0cd02da`; `nat_prelude::` 460 passed |
| 2026-09-04 | **Next Five items 2, 3 and half of 4 landed** (roadmap W1-6, W2-11, W2-12). `Nat.Graph`, 39 declarations, footprint 0, with symmetry and irreflexivity **forced inside the adjacency function by conjunction** so a malformed table under-counts rather than over-counts. **`R(3,3) = 6` proved in both directions**: the upper bound as a 32-leaf case tree, because a graph is a function and the kernel cannot enumerate all graphs; the lower bound from a search over the 2¹⁰ five-vertex graphs, the five-cycle, re-checked by reflection. Hall's theorem: necessity in one line from `card_le_of_injOn`; **sufficiency stopped** at computing the critical subfamily without choice, a bounded search over `2^(bound s)` subsets with no existing model. Cost worth knowing: the ℕ sweep went from ~18 s to 35–76 s, all Ramsey proof terms; `R(3,4)` needs the Ramsey recurrence over the degree counting this lane landed, not a bigger tree. (ADR-1608.) | `0a499a6d8`; `nat_prelude::` 495 passed |
| 2026-09-04 | **Item 4, the choice half of Hall sufficiency, closed** (roadmap W2-12, ADR-1614): a subset-search reflection primitive — `decode`/`encode` over `Nat.testBit`, exhaustiveness, and `existsSubset_of_search`/`forallSubset_of_search` — plus a named `Nat.strongInduction`. The search over `2^n` subsets never forms `2^n`. **Sufficiency still did not land, and the obstruction moved**: it is now a counting argument over `unionOver` under family modification, not a choice problem. A finding for every future finite-combinatorics lane: in this module the kernel is the mutation detector for every definition, so the evaluation tests are the readable pin rather than the load-bearing one. | `bc3eb38a5`; `nat_prelude::` 532 passed |
| 2026-09-05 | **Item 4, the counting half of Hall sufficiency, closed** (roadmap W2-12): 17 declarations. `unionOver` got its first two-sided characterisation, family modification turned out to be a quantifier commutation with one `Nat.Finset` counting law underneath, and matching glue landed without the textbook's disjointness hypothesis. **The obstruction moved again, to the empty set**: `Nat.Finset.singleton` has no lemmas at all and nothing turns a positive `card` into a member; Hall's base case is a singleton. A prediction refuted by measurement: exchanging `glue`'s branches was expected to be the first mutation the kernel misses here, and it killed all 18 tests. | `4c46ddb92`; `nat_prelude::` 610 passed |
| 2026-09-05 | **Item 5 landed** (roadmap W2-19, ADR-1624): sums indexed by subsets, with a subset as a `Nat → Bool` predicate so the split law is `Eq.refl`, and general inclusion–exclusion as two ℕ equations whose two-set case is kernel-checked equal to the existing `countRange_union_add_inter`. 41 declarations, footprint 0. The Next Five for this reviewer is now complete except the Hall statement itself, which waits on a `Nat.Finset.singleton` lemma shelf. | `4858a75dc`; `nat_prelude::` 602 passed in the lane |
| 2026-09-05 | **This reviewer's `Nat.Finset`↔Mathlib `Finset` "named bridge" now exists** (ADR-1665, `docs/math-department/14-lean-lang.md` Next Ten item 4): `CC:nat-finset-finset` and `CC:nat-multiset-multiset` both grade `different-object` — a computed bounded predicate whose own `Eq` is not set-extensional, against Mathlib's `nodup`-`Multiset` quotient whose `Eq` is — with `Nat.Finset.exists_memB_of_card_pos` (this shelf's search-based witness extraction) against `Finset.card_pos` as the witness pair. `CC:nat-graph-simplegraph` grades `Nat.Graph`↔`SimpleGraph` `different-object` the same way (adjacency forced by computation here, a Prop field with a default tactic proof there) and records a clean negative for `IsRamseyNumber33`: no finite Ramsey number is formalized anywhere in the pinned Mathlib checkout. A bonus row, `CC:nat-rado-partition-regularity`, grades `no-counterpart`: the one same-named Mathlib hit is Rado's *selection* lemma, a different theorem by the same mathematician, confirmed by reading its actual statement rather than trusting the name match. | `artifacts/carrier-correspondence/carrier-correspondence-v1.json`; `python3 scripts/check-carrier-correspondence.py --check` |
| 2026-09-05 | **Item 4, fourth slice** (roadmap W2-12, ADR-1630): `Nat.Finset.empty` and the singleton got their shelf — 13 declarations, with `exists_memB_of_card_pos` a bounded search rather than a choice — and Hall's base cases for the empty and one-element index sets are proved. The obstruction moved for the fourth time and is now a single named lemma (`allBelow_congr`, congruence of the bounded all-quantifier under pointwise equality) plus several hundred lines of routine term per branch. One admitted mutant (`empty` with an all-true predicate) was caught by exactly one assertion, the one saying `empty` is not `range 0`. | `ff6bfbaf5` |
| 2026-09-05 | **Item 4, fifth slice** (roadmap W2-12, ADR-1644): the one lemma the previous lane named, `Nat.Finset.allBelow_congr`, plus fixed-bound inclusion with its reflection and congruence, both branches of the critical-subset split, and `card_union_of_disjoint` found to be an existing sum lemma at weight one; 14 axiom-free declarations. Hall's sufficiency is still not stated: what remains is the strong-induction assembly and two descent-measure inequalities, which the lane did not attempt and correctly refused to call free. A rule for future lanes: a blocker list must say which entries were measured; one of this lane's three was false. | `7c15cd0fd` |
| 2026-09-05 | **Item 4 landed: Hall's marriage theorem** (roadmap W2-12, ADR-1645). `Nat.Hall.marriage_iff` is a kernel theorem with empty footprint, by strong induction on the size of the index set with the critical-subset split decided by bounded search. Six lanes over two days; each one's estimate of what remained was short by exactly one lemma nobody had measured, the last being that the descent needs the complement-count equation, not the inequality that already existed under a similar name. This reviewer's Next Five is now complete. | `2c9c666f8`; `nat_prelude::hall*` 47 passed in the lane |
| 2026-09-06 | **Möbius inversion, injective half** (roadmap W2-18, ADR-1658). A multiset is selected **by value**, not by list position — `Nat.Multiset` has no list, only a multiplicity function and a bound — so `restrict`/`prodSel` fold over `[0, bound m)`, the same index space `Nat.Subsets` uses. 14 declarations; the two that matter are `prodSel_dvd_prod` (hypothesis-free) and `prodSel_injective`, which together inject selections into divisors. `prodSel_injective` cost no new arithmetic: it is `count_eq_of_prod_eq` read through `prodSel_eq_prod_restrict`. Surjectivity and the range-to-subset sum transfer were not attempted; the transfer relates two different index shapes and carries an unmade width decision (`2^(bound m)` predicates against `2^(distinct primes)` divisors). | `236c37763`, `1718bad75`, `2e342d998`; `docs/plan/status/mobius-inversion-2026-09-05.md` |
| 2026-09-06 | **Re-measured the whole file against `main`; four false absences from the 09-04 audit corrected.** Kernel index rebuilt the same day: 4,765 declarations with `--include-constructed`, 3,311 in the default groups. Combinatorial namespace census: `Nat.Finset` 77, `Nat.Subsets` 41, `Nat.Graph` 39, `Nat.Multiset` 38, `Nat.Hall` 30, `Nat.Rado` 16 — 241 declarations. 59 field-matching facts, 57 `proved` and 2 `computed` (both four-colour Rado numbers). **Listed as missing and actually present since before the audit**: the binomial theorem (`Nat.add_pow`, and `Complex.add_pow`), Vandermonde's convolution (`Nat.choose_add_convolution`, `0fbe989bc` 2026-08-24 — the file had mislabelled it "Pascal" *and* listed Vandermonde as absent), the Catalan numbers (`Nat.catalan`, `Nat.catalan_mul_succ`) and `Nat.multichoose`. **Confirmed still absent**, each against a 4,765-row index that answers positively for neighbouring names: walks, paths, connectivity, trees, graph colourings, van der Waerden, the Ramsey recurrence, Turán, Dilworth, Sperner, König, Menger, the hockey-stick identity, formal power series, and O-notation. `AlgS.Poly` is now a 26-declaration `CommRing` instance, so the "generating functions need polynomial rings" blocker is discharged and replaced by the infinite-support carrier. **The `How to re-measure` grep was broken and is replaced**: it matched quoted string literals in Rust source, but this kernel builds names with `kernel.name_str(names.finset, "card")`, so it found 21 of the 115 `Nat.Finset` + `Nat.Multiset` declarations that exist. | `5fa2e3feb`; `shape_search --ns Nat`, `scripts/count-landmark-facts.py` |

## How to re-measure


**Standing caveat on every ABSENT claim in this file (added 2026-09-06).**
The retrieval index these measurements used builds 22 of the kernel's 31
prelude builders. It indexes **no** `FO.*` declaration, **no** `Metric.prod*`,
and no list prelude, so an ABSENT verdict in those three areas is a statement
about the instrument, not about the library. The same gap makes
`check-trust-closure.py` report 21 facts as having absent subjects when their
subjects exist. A partial-coverage tool does not merely fail to find things;
it produces false positives in every gate built on it. Absence claims here
outside those three areas are unaffected, and each was paired with a positive
control in the same invocation. Re-measure once ADR-1672's derived-coverage
gate has landed.
```sh
# 1. The facts this field owns, with their epistemic status.
python3 - <<'PY'
import json, glob, re
pat = re.compile(r'ramsey|hall|marriage|graph|inclusion.exclusion|schur|rado'
                 r'|catalan|stirling|multiset|finset|subset|pigeonhole'
                 r'|binomial|choose|permut', re.I)
for f in sorted(glob.glob('artifacts/facts/*.json')):
    d = json.load(open(f))
    t = d.get('title') or ''
    if pat.search(t) or pat.search(d.get('id') or ''):
        print(d.get('epistemic_status'), '|', t[:90])
PY

python3 scripts/count-landmark-facts.py

# 2. The carriers, read from the kernel -- NOT from source text. A grep for
#    quoted names undercounts by about 4x, because names are built with
#    `kernel.name_str(names.finset, "card")`, so only the last component is
#    a string literal. The census below is the number to quote.
cargo build --release -p axeyum-lean-kernel --example shape_search
target/release/examples/shape_search --ns Nat --limit 5000 \
  | awk '/^MATCH/{print $2}' | sed 's/\.[^.]*$//' | sort | uniq -c | sort -rn

# 3. Absence claims. Dump the WHOLE index once and grep that, so every
#    negative carries thousands of positive controls from the same run.
target/release/examples/shape_search --include-constructed \
  --name-contains '' --limit 20000 > /tmp/axeyum-index.txt
grep -c '^MATCH' /tmp/axeyum-index.txt      # the control: expect thousands
awk '/^MATCH/{print $2}' /tmp/axeyum-index.txt \
  | grep -iE 'turan|dilworth|sperner|walk|path|connect|waerden'
```

Note: `shape_search` does **not** build the list prelude group — its
`coverage:` line names the groups it did build, and `List` is not among them —
so `List.Perm` claims must be checked in
`crates/axeyum-lean-kernel/src/list_prelude/perm.rs` instead.

## Related

- [01-number-theory.md](01-number-theory.md) — multisets of primes, unique
  factorization, and the Möbius work `prodSel` feeds
- [04-algebra.md](04-algebra.md) — `AlgS.Poly`, and the infinite-support
  carrier generating functions would need
- [11-applied-and-computational.md](11-applied-and-computational.md) — the SAT
  core and DRAT checker that produced the Rado results
- ADR-1520 (Multiset), ADR-1577 (Finset), ADR-1593 (Finset pigeonhole),
  ADR-1596 (Rado numbers), ADR-1608 (the graph carrier), ADR-1614 (subset
  search), ADR-1624 (a subset is a predicate), ADR-1630 / ADR-1644 / ADR-1645
  (Hall), ADR-1658 (multiset selection by value)

# 07 — Combinatorics

Reviewer: a combinatorialist — enumerative, extremal, Ramsey theory
Verdict, 2026-09-04: **week three of a first course, with unusually good foundations — and one result nobody else has**
Last measured: 2026-09-04 at `1856cdb3c`

> "Your library proves the pigeonhole principle and computes a four-colour
> Rado number. Those are not adjacent shelves. The second one is why I am
> still reading."

> **AUDITED 2026-09-04.** Every absence claim in this file was re-checked
> against a freshly rebuilt kernel index. See
> [AUDIT-2026-09-04.md](AUDIT-2026-09-04.md) for the evidence, and the
> corrections marked **[AUDIT]** below. Across the twelve files, 11 of 76
> absence claims were false and 12 more overstated the gap; the cause is that
> the ledger characterises only 38% of its proved facts and does not cover 430
> kernel theorems at all (ADR-1605).

## The persona

Counts things, bounds things, and finds structure in large enough
configurations. Works with finite sets, multisets, generating functions,
graphs, and Ramsey-type existence results. Comfortable with computer search as
a proof technique and unusually receptive to machine-checked certificates,
because their subject already lives with results no human verified by hand.

## What the library has today

**Two shelves that have not met.** The elementary carriers landed in the last
two weeks; the computational results came from the solver side much earlier.

**Carriers and elementary results:**

| item | detail |
|---|---|
| `Nat.Multiset` | ADR-1520; multiplicity, product, "a multiset of primes carries exactly its recorded multiplicity", "a multiset's product is divisible by each element to its multiplicity" |
| `Nat.Finset` | ADR-1577; a decidable predicate on a bounded range, `card` as `countRange`, `memB`, `allBelow`, union/intersection/difference counting laws |
| pigeonhole | both forms: the range form (`Nat.pigeonhole`) and the Finset form (`Nat.Finset.pigeonhole`, ADR-1593), with `card_le_of_injOn` and the constructive `exists_collision` witness pair |
| binomial coefficients | `Nat.choose` with the addition convolution (Pascal), "a coefficient above the diagonal is zero", "bounded by the corresponding power of two", "a prime divides the interior coefficients of its own row" |
| `List` and `List.Perm` | ADR-1579/1583; permutation as reflexive, symmetric, reverse-invariant, with per-element counts agreeing between a list and its multiset |
| lattice counting | `sumRange_split`, `sumRange_rect_eq_diag_add_corner`, `countRange_union_add_inter`, and a rectangle-of-lattice-points partition result |

**Computational results, from the solver side:**

- **The four-colour Rado number of 5(x−y) = 3z is 625.**
- **The four-colour Rado number of 5(x−y) = 4z is 741.**

Both carry `epistemic_status: computed` — established by search with a
checkable certificate, not by a kernel proof term. These are genuine
extremal-combinatorics results of the kind their field publishes.

## Their verdict

**The elementary shelf is thin and correctly built.** Multiset, Finset,
pigeonhole in both forms, Pascal's rule: that is roughly week three. But the
carriers are the right ones and they were built in the right order —
`countRange` first, then `Finset` as a decidable predicate over it, then the
counting laws, then pigeonhole as a consequence rather than as an axiom. The
Finset pigeonhole in particular delivers a *witness pair*, computed by bounded
search, not merely the negation of injectivity, which is the constructively
strong form and the one that is actually usable.

**The Rado numbers are the interesting half.** Determining a four-colour Rado
number is a large finite search with a colouring on one side and an
exhaustiveness argument on the other, and it is exactly the shape their field
farms out to SAT solvers. That this project has a proof-producing SAT core and
a DRAT checker means the exhaustiveness half can carry a certificate rather
than a claim, which is more than most published computational Ramsey results
offer.

**The two shelves have not met, and that is the finding.** The Rado results
sit in the fact ledger as `computed`. The Finset and pigeonhole work sits
there as `proved`. Nothing connects them: there is no statement in the kernel
that says what a Rado number *is*, so the computed value is a number with a
certificate rather than a theorem about a defined object. Closing that gap —
defining Rado numbers over `Nat.Finset` and having the search discharge a
kernel-checkable statement — is the single most valuable thing this library
could do for their field, and it is the flywheel's own thesis applied to
combinatorics.

## What they would say is missing

- **Graphs.** No graph carrier at all: no vertices and edges, no degree, no
  paths, no trees, no colourings as a defined object. This is the largest gap
  and it blocks most of the subject.
- **Generating functions.** Needs formal power series, hence polynomial rings
  ([04-algebra.md](04-algebra.md)).
- **Ramsey theory as theory.** Ramsey's theorem itself, van der Waerden,
  Schur. The pigeonhole principle is its base case and nothing is built on it.
- **Inclusion-exclusion in general form.** The two-set case exists
  (`countRange_union_add_inter`); the n-set version needs sums over subsets.
- **Enumerative identities.** The binomial theorem as an identity in a
  commutative ring, Vandermonde, hockey-stick. **[AUDIT] Stirling numbers ARE
  present** — `Nat.stirlingFirst` and `Nat.stirlingSecond` with their
  recurrences and ten proved theorems, landed `33cae3575` 2026-08-31 (audit
  row A6). Stirling's *approximation* is a different item and is absent.
- **Extremal results.** No Turán, no Dilworth, no Hall's marriage theorem —
  the last of which is reachable now, since it is pigeonhole with structure.
- **Asymptotics.** No O-notation, no Stirling's approximation, nothing
  connecting counting to the analysis shelf.

## The blocker

**Almost nothing, which is why this reviewer is optimistic.** Every item on
the list except generating functions and asymptotics is finite, decidable, and
constructive — the most comfortable possible fit for this kernel. A graph is
an inductive type or a decidable relation on a bounded range, exactly like
`Nat.Finset`. Ramsey's theorem is an induction. Hall's theorem is a finite
argument.

Two real constraints:

- **Unary numerals.** Every `Nat` numeral in this kernel is unary, so cost is
  superlinear in the largest magnitude *formed*. Combinatorial statements that
  form large constants (a Rado number of 625, say) cannot be stated by
  computing the numeral. This is why the Rado results live outside the kernel,
  and connecting the shelves means stating them without forming the constant.
- **Generating functions need rings**, hence
  [04-algebra.md](04-algebra.md).

## Next five, in their priority order

- [x] **1. Define Rado numbers over `Nat.Finset` and connect the computed
      results to a kernel statement.** *Done 2026-09-04: Schur's `R_2(x=y+z)=5` both halves from search.* Their view: you already have the two
      hardest halves and they are not joined. This is also the clearest
      demonstration anywhere in the library of the untrusted-search /
      trusted-checking thesis on a *research-level* result.
- [x] **2. A graph carrier.** *Done 2026-09-04, `Nat.Graph`.* A decidable adjacency relation on a bounded
      vertex range, with degree, walks, and connectivity. The gate on most of
      the subject and a natural sibling of `Nat.Finset`.
- [x] **3. Ramsey's theorem for two colours** — *`R(3,3) = 6` both directions, 2026-09-04.*, by induction from the
      pigeonhole principle that just landed. The canonical first theorem of
      the subject and directly downstream of existing work.
- [~] **4. Hall's marriage theorem** — *necessity done 2026-09-04; choice half, counting half, and the singleton/empty shelf with both base cases all closed by 2026-09-05; the general statement needs one lemma, `Nat.Finset.allBelow_congr`, then a long but unobstructed induction.*, over `Nat.Finset` with the existing
      `card_le_of_injOn`. Finite, constructive, and the standard test of
      whether a finite-set library is usable.
- [x] **5. General inclusion-exclusion** — *done 2026-09-05, over subsets as predicates.*, generalizing
      `countRange_union_add_inter` to n sets. Needs sums indexed by subsets,
      which is itself a useful piece of infrastructure.

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

## How to re-measure

```sh
python3 - <<'PY'
import json, glob, re
pat = re.compile(r'binomial|choose|pigeonhole|multiset|finset|permut|Rado', re.I)
for f in glob.glob('artifacts/facts/*.json'):
    d = json.load(open(f)); t = d.get('title') or ''
    if pat.search(t): print(d.get('epistemic_status'), t[:90])
PY

grep -rhoE '"Nat\.(Multiset|Finset)\.[A-Za-z_]+"' crates/axeyum-lean-kernel/src/ | sort -u
```

## Related

- [01-number-theory.md](01-number-theory.md) — multisets of primes, unique
  factorization
- [11-applied-and-computational.md](11-applied-and-computational.md) — the SAT
  core and DRAT checker that produced the Rado results
- ADR-1520 (Multiset), ADR-1577 (Finset), ADR-1593 (Finset pigeonhole)

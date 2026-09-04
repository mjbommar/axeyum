# 07 — Combinatorics

Reviewer: a combinatorialist — enumerative, extremal, Ramsey theory
Verdict, 2026-09-04: **week three of a first course, with unusually good foundations — and one result nobody else has**
Last measured: 2026-09-04 at `1856cdb3c`

> "Your library proves the pigeonhole principle and computes a four-colour
> Rado number. Those are not adjacent shelves. The second one is why I am
> still reading."

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
  commutative ring, Vandermonde, hockey-stick, and Stirling numbers.
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

- [ ] **1. Define Rado numbers over `Nat.Finset` and connect the computed
      results to a kernel statement.** Their view: you already have the two
      hardest halves and they are not joined. This is also the clearest
      demonstration anywhere in the library of the untrusted-search /
      trusted-checking thesis on a *research-level* result.
- [ ] **2. A graph carrier.** A decidable adjacency relation on a bounded
      vertex range, with degree, walks, and connectivity. The gate on most of
      the subject and a natural sibling of `Nat.Finset`.
- [ ] **3. Ramsey's theorem for two colours**, by induction from the
      pigeonhole principle that just landed. The canonical first theorem of
      the subject and directly downstream of existing work.
- [ ] **4. Hall's marriage theorem**, over `Nat.Finset` with the existing
      `card_le_of_injOn`. Finite, constructive, and the standard test of
      whether a finite-set library is usable.
- [ ] **5. General inclusion-exclusion**, generalizing
      `countRange_union_add_inter` to n sets. Needs sums indexed by subsets,
      which is itself a useful piece of infrastructure.

## Progress log

| date | change | evidence |
|---|---|---|
| 2026-09-04 | File created. Baseline: `Nat.Multiset`, `Nat.Finset`, pigeonhole in both forms, binomial coefficients with Pascal, `List.Perm`. Two four-colour Rado numbers `computed` and not connected to any kernel statement. No graphs. | ledger snapshot at `1856cdb3c` |

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

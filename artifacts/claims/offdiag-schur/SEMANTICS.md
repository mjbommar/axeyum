# Family `offdiag-schur-colouring-L(k)` — encoding and faithfulness

## The claim family

For `k >= 3` write `L(k)` for the equation

```
x_1 + x_2 + … + x_{k-1} = x_k
```

over the **positive** integers (`L(3)` is Schur's `x + y = z`). For
`k = (k_1, …, k_r)` the generalized **off-diagonal** Schur number
`S(r; k_1, …, k_r)` is the least `N` such that every `r`-colouring of
`[N] = {1,…,N}` contains a monochromatic solution of `L(k_c)` in **some**
colour `c`. Each colour forbids its own equation, which is what "off-diagonal"
means, and `S` is symmetric under permuting the `k_c` because colour names are
just labels.

Ahmed and Schaal conjectured

```
S(3; s, t, u) = s·t·u − t·u − u − 1        for 4 ≤ s ≤ t ≤ u,
```

open as of arXiv:2604.11030 (Song and Mao, April 2026). The `≥` direction is a
theorem (Ahmed–Schaal Thm 2.11, restated as Theorem 3 there); the exact values
in this directory establish the matching `≤`.

A claim has parameters `{k: [k_1..k_r], r, n}` and is decided through a
propositional formula `F_n^k` emitted by
[`crates/axeyum-search/src/offdiag.rs`](../../../crates/axeyum-search/src/offdiag.rs):

- `F_n^k` **satisfiable** ⟺ some `r`-colouring of `[n]` avoids every colour's
  own equation ⟺ `S > n`;
- `F_n^k` **unsatisfiable** ⟺ `S ≤ n`.

## Solution enumeration

A solution of `L(k)` inside `[n]` is a multiset of `k − 1` positive parts whose
sum is at most `n`; the forbidden set is the set of **distinct values** among
the parts together with that sum. Two facts, both used below:

* for `k ≥ 3` the sum of `k − 1 ≥ 2` positive parts strictly exceeds every
  part, so the sum is always the **maximum** of the set and
  `|set| = (#distinct parts) + 1`;
* consequently the only **two-element** sets are `{a, (k−1)a}`, from all-equal
  parts, and there are exactly `⌊n/(k−1)⌋` of them.

## The CNF (variables `v(j,i) = (j−1)r + i`, "integer j has colour i")

1. **at-least-one** — each `j ∈ [n]` has a colour;
2. **negative** — for each solution set `S` of `L(k_c)` and **that colour `c`
   only**: not every member of `S` takes colour `c`. This is the off-diagonal
   difference: a set forbidden in colour 1 is *not* forbidden in colour 3
   unless it is also a solution set of `L(k_3)`;
3. **at-most-one** — each `j` has at most one colour;
4. **symmetry breaking, BLOCKED** — colour classes are ordered by least element
   only **within a block of colours carrying the same `k_c`**.

### Why group 4 is restricted, and what happens if it is not

The uniform families in this repository break colour symmetry across the whole
palette, justified by "colours are interchangeable". **That justification fails
here.** In `S(3;4,5,6)` colour 1 forbids `x_1+x_2+x_3=x_4` and colour 3 forbids
`x_1+…+x_5=x_6`; swapping them is not a symmetry of anything, and imposing the
ordering deletes genuine colourings.

This is not hypothetical. `S(3;3,4,5)` at `n = 41` is satisfiable — the
colouring is replayed by an independent enumerator — and encoding it with
whole-palette symmetry breaking returns **`unsat`**. That is a wrong `unsat`
produced by the encoding, and every downstream tool (solver, DRAT checker)
would certify it happily. The regression is
`crates/axeyum-search/tests/offdiag_schur.rs::whole_palette_symmetry_breaking_produces_a_wrong_unsat`.

Within a block of equal `k_c` the colours *are* interchangeable, so ordering
those classes by least element is sound in both directions in the usual way.

## Subsumption: what is actually emitted

If `S ⊆ S'` then "all of `S'` monochromatic" implies "all of `S` monochromatic",
so the clause over `S` implies the clause over `S'`; as literal sets,
`clause(S) ⊆ clause(S')`. The encoder therefore emits only the
**subsumption-minimal antichain** of each colour's solution sets. On `L(8)` over
`[1,87]` that is 75,433 sets out of 2,576,807 solution multisets.

Two consequences, and neither needs an extra argument:

* the emitted list is a literal **subset** of the full clause list, so a
  refutation of it refutes the full instance — the `≤` direction is sound;
* every dropped clause is implied by a retained one, so the two formulas have
  exactly the same **models** — the `>` direction is unaffected too.

The reduction is computed **per colour scope**. A minimal set of `L(4)` says
nothing about `L(8)`; sharing one antichain across colours forbidding different
equations would drop clauses that nothing implies. This is checked by
`tests/offdiag_schur.rs::subsumption_never_crosses_a_colour_scope`.

## Trust argument (untrusted search, trusted checking)

The searcher is **not** trusted. Every evidence row is re-checked by code that
did not produce it:

- **SAT side** — the artifact is the colouring. It is replayed by
  `OffDiagonalSchur::first_violation`, a layered reachability search over the
  defining equation that shares no code with the partition enumeration the
  encoder uses; then cross-checked against the **full, unreduced** solution-set
  list; then replayed a third time by
  [`scripts/check-claim-certificates.py`](../../../scripts/check-claim-certificates.py),
  in Python, from the equation. A wrong colouring cannot survive that
  regardless of encoding bugs.
- **UNSAT side** — the artifact is a DRAT proof produced by axeyum's own CDCL
  core and re-derived by axeyum's own `check_drat_backward`. The ledger checker
  additionally validates the deciding CNF **clause by clause**: every negative
  clause must forbid a genuine monochromatic solution of the equation *its
  colour actually carries*, and the structural clauses must be exactly the sound
  at-least-one / at-most-one / **blocked** symmetry set, rebuilt from the claim
  parameters.

  Clause-wise validation rather than byte-identity is deliberate. Byte-identity
  proves the certificate refutes the *intended* instance; clause-wise validity
  proves it refutes something *implied by* the intended instance, which is
  exactly what `S ≤ n` needs, and it does not force a second implementation of
  the subsumption reduction to agree bit for bit with the first. It also catches
  the symmetry trap directly: a CNF that ordered non-interchangeable colours
  fails the structural comparison.

No external solver and no external proof checker appears anywhere in this
family. There is no kissat, no cryptominisat, no z3, no drat-trim (ADR-0002).

## Validation of the encoding pipeline

The pipeline was validated against **all eleven** published exact values of
`S(3;s,t,u)` — `(4,4,4)=43`, `(4,4,5)=54`, `(4,4,6)=65`, `(4,4,7)=76`,
`(4,5,5)=69`, `(4,5,6)=83`, `(4,5,7)=97`, `(4,6,6)=101`, `(5,5,5)=94`,
`(5,5,6)=113`, `(6,6,6)=173` — in every case with `F_{N−1}` satisfiable with a
replayed witness and `F_N` unsatisfiable with a checked DRAT proof, zero
mismatches, 119 seconds total.

`(4,5,6)` and `(4,5,7)` are the load-bearing regressions: three *distinct*
equations, so those instances admit no colour symmetry at all and an over-strong
symmetry break shows up there first. Both run in
`crates/axeyum-search/tests/offdiag_schur.rs`.

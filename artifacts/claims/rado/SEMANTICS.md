# Family `rado-colouring-a(x-y)=bz` — encoding and faithfulness

## The claim family

For positive integers `a`, `b`, the equation `E: a(x−y) = bz` and a colour
count `k`, the Rado number `R_k(E)` is the least `n` such that **every**
k-colouring of `[n] = {1,…,n}` contains a monochromatic solution
`(x, y, z) ∈ [n]³` to `E` (Chang–De Loera–Wesley, arXiv:2210.03262, §1).

A claim in this family has parameters `{a, b, k, n}` and is decided through
the propositional formula `F_n^k(E)` emitted by
[`scripts/gen-rado-instance.py`](../../../scripts/gen-rado-instance.py):

- `F_n^k(E)` **satisfiable** ⟺ some k-colouring of `[n]` avoids a
  monochromatic solution ⟺ `R_k(E) > n`.
- `F_n^k(E)` **unsatisfiable** ⟺ `R_k(E) ≤ n`.

## Solution enumeration

With `g = gcd(a,b)`, `a′ = a/g`, `b′ = b/g` (so `gcd(a′,b′) = 1`), the
positive solutions of `a(x−y) = bz` are exactly

```
x − y = b′·t,   z = a′·t,   t = 1, 2, 3, …
```

*Why:* `a(x−y) = bz` ⟺ `a′(x−y) = b′z`; since `gcd(a′,b′) = 1`, `b′ | x−y`;
writing `x−y = b′t` forces `z = a′t`, and every such pair solves the
equation. Note `x ≠ y` always (`t ≥ 1`), but `z` may coincide with `x` or
`y`; the encoding treats each solution as its **set** of distinct members.

## The CNF (variables `v(j,i) = (j−1)k + i`, "integer j has colour i")

1. **positive** — each `j ∈ [n]` has at least one colour;
2. **negative** — for each solution's distinct-member set `{x,y,z}` and each
   colour `i`: not all members have colour `i`;
3. **at-most-one** — each `j` has at most one colour (not needed for
   equisatisfiability; makes models colourings bijectively);
4. **symmetry breaking** — integer 1 has colour 1, and integer `j` may take
   colour `i > 1` only if some `j′ < j` already has colour `i−1` (colour
   classes ordered by least element).

Symmetry breaking is sound for both answers: colours are interchangeable, so
every avoiding colouring can be renamed into one satisfying (4); hence (4)
preserves satisfiability, and any satisfying assignment still yields a
genuine avoiding colouring.

## Trust argument (untrusted search, trusted checking)

The searchers (kissat, the min-conflicts `lsearch`) are **not trusted**.
Every evidence row is re-checked independently:

- **SAT side** — the artifact is the colouring itself, replayed by
  [`scripts/check-claim-certificates.py`](../../../scripts/check-claim-certificates.py)
  against a direct `O(n²)` solution search that shares no code with the
  generator or any searcher. A wrong colouring cannot survive replay
  regardless of encoding bugs.
- **UNSAT side** — the artifact is a DRAT proof re-checked by an external
  checker (`drat-trim`), **and** the stored CNF must regenerate
  byte-identically from the claim parameters via the checker's own
  independently written encoder, so the certificate provably refutes the
  intended instance. The residual trust is the encoding-faithfulness
  argument above plus the DRAT checker.

## Validation of the encoding pipeline

The full pipeline was validated against all 34 published exact values of
`R_3(a(x−y)=bz)` (1 ≤ a,b ≤ 5) and `R_4(a(x−y)=bz)` (Tables 1 and 10 of
arXiv:2210.03262): in every case `F_{R−1}` was satisfiable with an
independently replayed witness and `F_R` was unsatisfiable, with zero
mismatches. Those 34 boundary pairs are retained as the
`published-value-replication` claims in this directory, each with a
checked witness and a drat-trim-verified certificate.

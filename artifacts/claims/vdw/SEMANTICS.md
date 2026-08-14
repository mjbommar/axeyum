# Family `vdw-colouring-AP(k)` — encoding and faithfulness

## The claim family

An **arithmetic progression** of length `k` inside `[n] = {1,…,n}` is a set
`{a, a+d, …, a+(k−1)d}` with `d ≥ 1`. Van der Waerden's theorem says that for
any lengths `k_1, …, k_r` there is a least `N` such that **every** `r`-colouring
of `[N]` contains, for some colour `c`, a monochromatic progression of length
`k_c`. That least `N` is the van der Waerden number `w(r; k_1,…,k_r)`; when
every `k_c` is the same `k` it is the *diagonal* number, written `W(r,k)`.

A claim in this family has parameters `{k, r, n}` and is decided through the
propositional formula `F_n(k)` emitted by
[`crates/axeyum-search/src/vdw.rs`](../../../crates/axeyum-search/src/vdw.rs)
(`VanDerWaerden::problem`, through the shared encoder
`ColouringProblem::encode`):

- `F_n(k)` **satisfiable** ⟺ some `r`-colouring of `[n]` has no colour `c`
  containing a monochromatic progression of length `k_c` ⟺ `w > n`.
- `F_n(k)` **unsatisfiable** ⟺ `w ≤ n`.

## Progression enumeration

The forbidden sets of colour `c` are all `{a, a+d, …, a+(k_c−1)d}` with `d ≥ 1`
and `a + (k_c−1)d ≤ n`, enumerated with `d` ascending and then `a` ascending.
There are exactly `Σ_{d≥1} (n − (k_c−1)d)` of them.

**No subsumption reduction applies to this family, and the claim checker relies
on that.** For `S ⊆ S'` the clause over `S` implies the clause over `S'`, which
is what lets the off-diagonal Schur family ship only a subsumption-minimal
antichain. Here every progression of length `k` is a set of *exactly* `k`
distinct points, so `S ⊆ S'` forces `S = S'`; and a progression is determined by
its set (its two least elements give `a` and `d`), so there are no duplicates.
The forbidden list is therefore already minimal, the clause count is exactly the
progression count, and
[`scripts/check-claim-certificates.py`](../../../scripts/check-claim-certificates.py)
checks that count per colour rather than only checking that each clause is
legitimate.

## The CNF (variables `v(j,i) = (j−1)r + i`, "integer j has colour i")

1. **positive** — each `j ∈ [n]` has at least one colour;
2. **negative** — for each colour `c` and each length-`k_c` progression `P`
   inside `[n]`: not all members of `P` have colour `c`. In an off-diagonal
   instance each such clause is scoped to the **single** colour whose length it
   belongs to;
3. **at-most-one** — each `j` has at most one colour (not needed for
   equisatisfiability; makes models colourings bijectively);
4. **symmetry breaking** — see below.

## Symmetry breaking is conditional, and getting it wrong gives a wrong `unsat`

Ordering colour classes by least element is sound **only between colours that
forbid the same sets**. This family therefore has two encodings and picks
between them explicitly:

* **Diagonal** (`k_1 = … = k_r`). The colours are interchangeable, so the
  uniform whole-palette break applies: integer 1 takes colour 1, and integer `j`
  may take colour `i > 1` only if some `j′ < j` takes colour `i−1`. This is the
  stock encoder path, byte-identical to the one the Rado certificates were
  produced with.
* **Off-diagonal**. Colour `c` forbids length `k_c`, so two colours are
  interchangeable exactly when their lengths are equal. The ordering is imposed
  only inside blocks of equal length. For `w(2;3,t)` with `t ≠ 3` the blocks are
  `{1}` and `{2}`, so **no symmetry clause is emitted at all**.

Using the whole-palette break on an off-diagonal instance deletes genuine
colourings. This is not a hypothetical: `w(2;3,4)` at `n = 17` is satisfiable
(`w(2;3,4) = 18`) and every good colouring gives integer 1 the colour that
avoids four-term progressions, so pinning integer 1 to colour 1 makes the
formula unsatisfiable — with a perfectly valid DRAT refutation of a formula that
should never have been built.
`crates/axeyum-search/tests/vdw.rs::whole_palette_symmetry_breaking_produces_a_wrong_unsat`
is that control, and the claim checker rebuilds the block structure from the
claim's own `k` so a stored CNF that ordered non-interchangeable colours cannot
pass.

The instance in the control is load-bearing: `w(2;3,5)` over `n ≤ 21` and
`w(2;3,6)` over `n ≤ 31` were both scanned and neither ever flips, so a control
built on either would have passed while testing nothing.

## Trust argument (untrusted search, trusted checking)

The searchers are **not trusted**. Every evidence row is re-checked
independently:

- **SAT side** — the artifact is the colouring itself. It is replayed three
  times by three different derivations: `VanDerWaerden::first_violation`, a
  dynamic program over *pairs of members of the colour class* that computes the
  longest progression and shares no code with the encoder; the encoder's own
  view (`ColouringProblem::first_monochromatic`), as a weaker cross-check; and
  `scripts/check-claim-certificates.py`, in Python, which grows progressions
  forward from every pair of same-coloured points. A wrong colouring cannot
  survive replay regardless of encoding bugs.
- **UNSAT side** — the artifact is a DRAT proof produced by axeyum's own
  proof-producing CDCL core (ADR-0381) and re-derived by axeyum's own backward
  DRAT checker (ADR-0382), in the same process, before anything was written.
  **No external solver and no external checker takes part** (ADR-0002): no
  kissat, no cryptominisat, no z3, no drat-trim. The claim checker additionally
  validates the deciding CNF clause by clause against an independent Python
  derivation of the semantics — every negative clause must be a genuine
  progression of the length its colour actually carries, the structural clauses
  must be exactly the sound at-least-one / at-most-one / symmetry set for this
  instance's block structure, and the per-colour clause counts must match the
  progression counts. The residual trust is the encoding-faithfulness argument
  above plus axeyum's CDCL core and checker.

A proof too large to carry in the repository is recorded with
`check_status: not-checked`, `distribution: regenerable`, its sha256 and its
byte count, plus the command that regenerates it. It is never reported as
re-checked here.

## Validation of the encoding pipeline

Every value in this directory reproduces a published one, both sides:
`W(2,3) = 9`, `W(3,3) = 27`, `W(2,4) = 35` (Chvátal 1970), `W(2,5) = 178`
(Stevens–Shantaram 1978), and `w(2;3,t)` for `t = 4..12` (Ahmed–Kullmann–Snevily,
arXiv:1102.5433, Table 1). Zero mismatches. The reproduction is the gate on the
encoder; the certification is the contribution.

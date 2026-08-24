# Ad hoc blocker sweep 2026-08-20 -- lane 04: p-adic cohomology, Newton polygons, Artin-Schreier-Witt towers

Agent: field specialist (p-adic geometry).  Scope: ad hoc research, OUTSIDE the
roadmap and gates.  Read-only on the repository except this file and scratchpad
files under the session scratchpad.

Epistemic labels used throughout: PROVED / REFUTED (with witness) / OPEN.
Finite computation is EVIDENCE, never a theorem.

Scratchpad: /tmp/claude-1000/-home-mjbommar-projects-personal-axeyum/f980d106-5a72-4c93-8c17-11101edf42d1/scratchpad

---

## 19:08Z -- orientation

Read, in order:

- `docs/research/10-cas/lemire-review-2026-08-20-reaim.md` (264 lines)
- `docs/research/09-decisions/adr-0559-reaim-the-odd-endpoint-at-normalized-two-adic-traces.md`
- `docs/research/10-cas/lemire-half-degree-irreducibles.md` lines 400-640
  (Carlitz compression, odd reduction, refuted `(C8)`, cyclotomic Newton audit)

Two corrections to my own brief, established before any new work:

1. The brief says "`I_n` mod 8 is recoverable from the curve trace mod
   `2^(ell+3)`" and treats a fixed-modulus congruence as live.  **The fixed
   congruence `(C8)` is already REFUTED in the repository**, witness
   `ell=27, n=55: N_n(1)=268616921, I_n(1)=4883944 = 0 mod 8, v_2(I_n(1))=3`
   (ADR-0560, quoted in the canonical note).  So the target cannot be a fixed
   residue mod 8.  It has to be an `ell`-dependent finiteness statement.
2. The brief says "the whole game is the slope spectrum near 1/2".  The
   repository's own exact cyclotomic Newton audit says otherwise: minimum
   primitive-character slopes are `1/2` (levels 2,3), `1/4` (4-7), `1/8`
   (8-10).  The minimum slope goes to ZERO like `1/j`, not to `1/2`.  I take
   this as the starting fact and re-derive the consequences below.

---

## 19:12Z -- literature, fetched not remembered

Every item below was fetched this session; the hypothesis quotes are from the
papers, not from memory.

1. **Joe Kramer-Miller, "p-adic estimates of abelian Artin L-functions on
   curves", arXiv:2006.04936** (single author -- the re-aim review at
   `lemire-review-2026-08-20-reaim.md` attributes this to "Kramer-Miller and
   Upton"; that is a misattribution worth correcting).
   <https://arxiv.org/abs/2006.04936>
   Standing hypothesis, quoted from the paper: **"Let p be a prime with p>=3
   and let q=p^a."**  What it proves: `NP_q(L(rho,s))` lies above a Hodge
   polygon `HP(rho)` built from the Swan conductor and local exponents.
   **Does NOT apply at p=2.**  PROVED-elsewhere, INAPPLICABLE-here.

2. **Kramer-Miller and Upton, "Newton Polygons of Sums on Curves I:
   Local-to-Global Theorems", arXiv:2110.08656** (published July 2024).
   <https://arxiv.org/abs/2110.08656>
   Standing hypothesis, quoted: **"Let p be an odd prime and let q be a power
   of p."**  Character order `p^n`, any `n`; base a smooth affine curve of any
   genus, so `A^1` with one wild point is in scope; base assumed ordinary for
   Theorem 1.1.  **Local Hodge polygon at a ramified point P with Swan
   conductor `d_P` has slope set `{1/d_P, ..., (d_P-1)/d_P}`**, and the global
   polygon concatenates the local ones with slope-0 and slope-1 segments.
   Theorem 1.1 (vertex contact): `HP` and `NP` share a terminal point at
   `r in [0,1]` iff the corresponding local polygons do, at each ramified
   point.  **Again p odd.**

3. **Kramer-Miller and Upton, "Newton Polygons of Sums on Curves II:
   Variation in p-adic Families", arXiv:2110.08657** (IMRN 2023).
   <https://arxiv.org/abs/2110.08657>
   Abstract, verbatim: "Fix an **ordinary** curve X ... By a **Z_p-tower**
   X_infty/X we mean a tower of covers ... with Gal(X_n/X) = Z/p^nZ ... if the
   ramification along the tower is **sufficiently moderate**, then the slopes
   ... are equidistributed in [0,1] as n tends to infinity."
   Rank-one tower; p odd.  **Not our Galois group.**

4. **Davis, Wan, Xiao, "Newton slopes for Artin-Schreier-Witt towers",
   arXiv:1310.5311** (Math. Ann.).  <https://arxiv.org/abs/1310.5311>
   `Z_p`-tower over `A^1` from a monic `f` of degree `d`.  L-function of a
   character of conductor `p^{m}` has **degree `d p^{m-1} - 1`**, and for
   `m >= m_0` the slopes are a union of `d p^{m_0-1}` arithmetic progressions
   with increment `p^{m_0-m}` (normalized: spacing `1/(d p^{m-1})`, i.e. the
   slopes are the equidistributed set `{i / Swan}`).  The abstract does not
   exclude `p=2`, but the tower is rank one.

5. **Ren, Wan, Xiao, Yu, "Slopes for higher rank Artin-Schreier-Witt towers",
   arXiv:1605.02254** (Trans. AMS).  <https://arxiv.org/abs/1605.02254>
   Galois group `Z_{p^ell}` = Witt vectors of `F_{p^ell}`, "abstractly
   isomorphic to `(Z_p)^ell`".  So: rank `ell`, but an **unramified
   coefficient extension** of a rank-one object.  Slopes asymptotically a
   finite union of arithmetic progressions.

6. **Booher, Cais, Kramer-Miller, Upton, "Higher a-numbers in Z_p-towers via
   counting lattice points", arXiv:2407.13969 / INTEGERS 26 (2026) #A78.**
   <https://arxiv.org/abs/2407.13969>  `Z_p`-towers totally ramified over one
   point of `P^1`, ramification invariant `d`, main theorem when **`d | p-1`**
   (so at `p=2` only `d=1`).  Computes higher **a-numbers** (an `alpha_p`
   invariant of the Jacobian), not point counts and not Frobenius traces mod
   `p^k`.  Shape of the answer -- `alpha(n) p^{2n} + beta(n) p^n + lambda n +
   nu` with periodic coefficients -- is the shape one would want for `Delta`,
   but the invariant is the wrong one.  ADJACENT.

7. **Denef and Vercauteren, "An extension of Kedlaya's algorithm to
   Artin-Schreier curves in characteristic 2", ANTS-V, LNCS 2369 (2002),
   308-323.**
   <https://link.springer.com/chapter/10.1007/3-540-45455-1_25>
   Running time `O(g^{5+eps} log^{3+eps} q)`, storage `O(g^3 log^3 q)`.
   Relevant because it is the *only* p-adic-cohomology point counter that runs
   at `p=2`; see the complexity comparison at 19:40Z below.

Net literature verdict, matching the lane's own note at
`lemire-half-degree-irreducibles.md:595-601`: **there is no published
Newton-over-Hodge theorem at `p=2`.**  Every candidate fixes `p` odd in its
first paragraph.  So anything in this direction is conjecture plus
computation, not citation.

---

## 19:20Z -- setting up the geometry properly (this fixes the frame)

The Carlitz cyclotomic field `K_j` of conductor `t^{j+1}` over `F_2(t)` is
ramified at the single finite place `t` and, because `q=2` makes the tame part
`q-1=1`, **split (hence unramified) at infinity**.  Put `u = 1/t`.  Then the
only ramified place sits at `u = infinity`, and every Carlitz character is a
character of `pi_1(A^1_u)` of 2-power order, wild at one point.

**That is exactly the Davis-Wan-Xiao / Kramer-Miller frame**, at `p=2`.  The
lane's documents call this "the Carlitz curve"; it is more usefully described
as an abelian, infinite-rank Artin-Schreier-Witt cover of `A^1` ramified at one
point.  Concretely (PROVED, standard):

- a character of exact conductor `x^{j+1}` has Artin conductor exponent `j+1`,
  hence (rank one) a single break and **Swan conductor `s = j`**;
- Grothendieck-Ogg-Shafarevich on `A^1` gives `deg L(chi) = s - 1 = j - 1`,
  which is exactly the degree the canonical note records;
- the Galois group at level `j` is `(F_2[t]/t^{j+1})^*`, of order `2^j` and
  **exponent `2^{ceil(log2(j+1))}`** (since `(1+t)^{2^r} = 1 + t^{2^r}`).  So a
  character has order `2^a` with `a <= ceil(log2(j+1))`, its values lie in
  `Q(zeta_{2^a})`, where 2 is totally ramified with `e = 2^{a-1}`, and **every
  Newton slope of `L(chi)` lies in `(1/(e * run))Z`** -- the value group is
  coarse, and coarser than the Hodge lattice `(1/j)Z`.

Consequence, before any computation: the minimum attainable positive slope for
a level-`j` character is `1/e <= 2/j`.  The lane's measured minima
(`1/2` at levels 2-3, `1/4` at 4-7, `1/8` at 8-10) are **exactly
`1/2^{ceil(log2(j+1))-1}`** in every row.  So the observed spectrum is not
exotic: the Newton polygon is sitting as low as the ramification lattice
allows.  This is the `p=2` analogue of DWX equidistribution, coarsened.

**This contradicts the framing in my brief** ("the whole game is the slope
spectrum near 1/2").  The minimum slope goes to zero like `1/j`.  Whatever
produces the `2^ell` divisibility of the trace, it is not the slopes.

## 19:22Z -- the reformulation that actually matters (PROVED, elementary)

Start from the lane's exact odd reduction `N_(2ell+1)(1) = 1 + (2ell+1)
I_(2ell+1)(1)` and `N_n(1) = 2^(n-ell) + Delta_(ell,n)`.  With `n = 2ell+1`:

```text
I_n(1) = (2^(ell+1) + Delta_(ell,n) - 1) / n,        n odd.
```

Because `n` is odd, `v_2(I_n(1)) = v_2(2^(ell+1) + Delta - 1)`.  Hence:

- **(R1) PROVED.**  Lemire's odd endpoint at `n = 2ell+1` holds
  **iff `Delta_(ell,2ell+1) != 1 - 2^(ell+1)`**, i.e. iff
  `Delta_(ell,2ell+1) !== 1 (mod 2^(ell+1))`.  One forbidden residue class.
- **(R2) PROVED.**  `v_2(I_n(1)) = v_2(Delta_(ell,n) - 1)` whenever that is
  `<= ell`.  In particular **if `Delta_(ell,2ell+1)` is EVEN then `I_n(1)` is
  ODD, hence nonzero, hence Lemire holds at `n`.**
- **(R3) PROVED (restating R1 on the curve).**  With `#C_ell(F_(2^n)) =
  1 + 2^ell N_n(1)`, the odd endpoint is exactly
  `#C_ell(F_(2^(2ell+1))) !== 2^ell + 1 (mod 2^(2ell+1))` -- "the point count is
  not exactly its forced minimum".

(R2) is the useful one: it converts an existence theorem into a **single bit**.
Checked against the ledger rows `ell=13..24` and against my own recomputation
at `ell=2..18` (19:30Z below): `Delta` even in 10 of 17 computed rows, and in
every such row `I_n(1)` is odd, exactly as (R2) says.

The fixed congruence `(C8)` that ADR-0560 refuted is a *stronger* statement
than (R1) needs.  (R1) only forbids one residue class whose modulus grows with
`ell`; `(C8)` demanded a fixed modulus.  The `ell=27` counterexample
(`v_2(I_55(1))=3`) kills `(C8)` and says nothing against (R1).

---

## 19:24Z -- EXPERIMENT 1: exact 2-adic Newton polygons per exact conductor

Tooling.  `crates/axeyum-cas/src/gf2_hayes.rs` already exposes
`hayes_conductor_two_adic_newton_report(level, degree, limits)` (added by
ADR-0559) and `conductor_layers(ell, degree, limits)`.  Both are `pub`.  I did
not modify any repository file.  I built a throwaway crate in the session
scratchpad with a path dependency on `axeyum-cas`:

```sh
S=/tmp/claude-1000/-home-mjbommar-projects-personal-axeyum/f980d106-5a72-4c93-8c17-11101edf42d1/scratchpad
mkdir -p $S/newton/src/bin           # Cargo.toml: axeyum-cas = { path = ".../crates/axeyum-cas" }
cd $S/newton && CARGO_TARGET_DIR=$S/target cargo build --release      # 20s
$S/target/release/newton-probe 13 12   > $S/run-L13-ell12.txt          # 10s total
$S/target/release/layers      2  18    > $S/layers-2-18.txt            # 26s total
$S/target/release/rhp         15       > $S/rhp-2-15.txt               # ~3 min
```

Source and output SHA-256:

```text
2a878a13291b272ea90eb81485276cf5ba57f9bd7aaa42d041b28cb9087a2733  newton/src/main.rs
1c71bce345e53060533a2a84bbc5ccbc8728f3d2b2a7718d8665555de3d1d33b  newton/src/bin/layers.rs
b4446802cdfb203adbd218567ff6439323bf08dbc5216cec855b097589b38df8  newton/src/bin/rhp.rs
f45706bcb066e7720a3b3b3428d3a3181ac30dd31042ae664b0b6b5729a206a0  run-L13-ell12.txt
2279d6e337f71dde492c94bde06a1397aa505b16cb078a8a53b8c8ee2ea8ce2c  layers-2-18.txt
```

Peak RSS stayed under 1 GB; total compute for everything in this diary is under
five minutes.

**Reproduction check.**  The min-slope/multiplicity row of ADR-0559 is
reproduced exactly (levels 2-10: minima `1/2 1/2 1/4 1/4 1/4 1/4 1/8 1/8 1/8`,
multiplicities `2 8 8 8 64 80 128 128 256`), and extended:

```text
level  11      12      13
min    1/8     1/8     1/8
mult   512     4096    5120
```

**New: the FULL slope spectrum per conductor level** (aggregated over all
`2^(L-1)` primitive characters; `a/b:m` means slope `a/b` with total root
multiplicity `m`):

```text
L=2   1/2:2
L=3   1/2:8
L=4   1/4:8  1/2:8  3/4:8
L=5   1/4:8  1/2:48 3/4:8
L=6   1/4:64 1/2:32 3/4:64
L=7   1/4:80 1/3:48 3/8:32 1/2:64 5/8:32 2/3:48 3/4:80
L=8   1/8:128 1/4:128 3/8:128 1/2:128 5/8:128 3/4:128 7/8:128
L=9   1/8:128 1/4:288 1/3:48 3/8:160 5/12:48 1/2:704 7/12:48 5/8:160 2/3:48 3/4:288 7/8:128
L=10  1/8:256 1/4:1536 3/8:256 1/2:512 5/8:256 3/4:1536 7/8:256
```

Two structural facts fall straight out.

- **At `L = 2, 4, 8` (powers of two) every single primitive character has the
  fully equidistributed spectrum `{1/L, 2/L, ..., (L-1)/L}`** -- i.e. exactly
  the Hodge/DWX prediction `{i/Swan}`, with no rounding needed, for all
  `2 + 8 + 128 = 138` characters.  This is `p=2` DWX equidistribution,
  observed.
- At non-powers of two the value group `(1/e)Z` with `e = 2^(ceil(log2(L+1))-1)`
  is coarser than `(1/L)Z`, and the spectrum is a rounded-up version of
  `{i/L}`.  Slopes with non-dyadic denominators (`1/3`, `5/12`, `7/12`) appear
  precisely as long hull segments compensating for that rounding.

## 19:30Z -- EXPERIMENT 2: is `NP = ` the lattice-rounded Hodge polygon?

Definition used.  For a primitive level-`L` character `chi` of order `2^a`, set
`e = 2^(a-1)` (ramification of 2 in `Q(zeta_(2^a))`), take the Kramer-Miller
local Hodge polygon with Swan conductor `s = L`, whose ordinate at abscissa `m`
is `m(m+1)/(2L)`, round each ordinate **up** to the lattice `(1/e)Z`, and take
the lower convex hull.  Call the result `RHP(chi)`.  Trivially
`RHP >= HP`, so `NP >= RHP` implies `NP >= HP`.

Result over **every primitive character at levels 2..14** (`2^1 + ... + 2^13 =
16382` characters, each polygon computed from exact `Z[zeta_(2^r)]` coefficient
valuations, no floating point):

```text
L      chars   NP == RHP        NP strictly below RHP
2      2       2/2              0
3      4       4/4              0
4      8       8/8              0
5      16      16/16            0
6      32      32/32            0
7      64      40/64            0
8      128     128/128          0
9      256     40/256           0
10     512     512/512          0
11     1024    256/1024         0
12     2048    2048/2048        0
13     4096    1024/4096        0
14     8192    5120/8192        0
```

- **EVIDENCE (not a theorem): Kramer-Miller's Newton-over-Hodge bound holds at
  `p = 2` for this tower.**  No character in 16382 violates `NP >= HP`, and none
  violates the strictly stronger lattice-rounded bound.  This is the first
  quantitative evidence in the lane's ledger that the `p >= 3` hypothesis in
  arXiv:2006.04936 / 2110.08656 is an artefact of method rather than of truth
  *for this family*.  It is 16382 rows, not a proof.
- **REFUTED: `NP = RHP` as a universal law.**  Witness at `L=9`, character
  index 257, order 16: `NP = [1/8, 1/4, 3/8, 1/2, 1/2, 5/8, 3/4, 7/8]` while
  `RHP = [1/8, 1/4, 3/8, 3/8, 5/8, 5/8, 3/4, 7/8]`; the polygons agree at every
  vertex except abscissa 4, where `NP` is exactly one lattice unit (1/8) high.
  My earlier guess that the law holds exactly at even levels also fails: `L=14`
  is even and gives 5120/8192.
- What survives: `NP` and `RHP` share their *first* segment in every computed
  row, so **the minimum slope is `1/e` on the nose** (vertex contact at the
  first vertex, in KMU's language).  The deviations are isolated interior
  vertices.

## 19:35Z -- EXPERIMENT 3: what the slopes actually buy, per conductor layer

This is the decisive measurement.  The lane's telescoping identity is
`Delta_(ell,n) = 2^(-ell) sum_(j=1)^ell T_(j,n)`, with
`T_(j,n) = 2^(j-1) (C_0 - C_1)` an exact-conductor layer trace.  So there are
two competing lower bounds on `v_2(T_(j,n))`:

- **the trivial counting floor `j-1`**, immediate from `T_j = 2^(j-1)(C_0-C_1)`
  -- no cohomology, no geometry;
- **the p-adic floor `ceil(n * lambda_min^(j))`**, the best bound obtainable
  from *any* Newton-polygon theorem, where `lambda_min^(j) = 1/e_j` is the
  measured (and lattice-forced) minimum slope.

Measured at the odd endpoints `n = 2ell+1`, top layer `j = ell`
(`layers-2-18.txt`; the `Delta` column reproduces the fleet rows `ell=13..18`
exactly: `-345, -896, 340, 2744, -1988, 928`, and `I_n mod 8` reproduces every
entry of the ADR-0559 residue list for `ell = 2..18`):

```text
ell   n    v2(T_ell)   p-adic floor   trivial floor   p-adic deficit
 2    5        3            3               1              0
 3    7        5            4               2             +1
 4    9        4            3               3             +1
 5   11        5            3               4             +2
 6   13       11            4               5             +7
 7   15        7            4               6             +3
 8   17        8            3               7             +5
 9   19        8            3               8             +5
10   21        9            3               9             +6
11   23       10            3              10             +7
12   25       11            4              11             +7
13   27       12            4              12             +8
14   29       15            4              13            +11
15   31       14            4              14            +10
16   33       15            3              15            +12
17   35       17            3              16            +14
18   37       18            3              17            +15
```

Read the two middle columns.  **The p-adic floor is pinned at 3-4 for every
`ell`, because `lambda_min ~ 1/ell` while `n ~ 2ell`, so `n * lambda_min -> 2`.
The trivial counting floor grows like `ell`.  They cross at `ell = 4`.**  For
every `ell >= 4` in the computed range, the strongest conceivable
Newton-polygon input about the top conductor layer is *weaker than a one-line
counting identity*, and the gap grows linearly.  Adding the Galois-trace gain
(`Tr: Z[zeta_(2^r)] -> Z` on an element of valuation `1/e` lands in
`2^(r-1) Z`, a further `r-1 = O(log ell)` bits) does not change this.

The same table also shows where p-adic information *is* nontrivial: the floor
`ceil(n/e_j)` beats `j-1` only for `j <~ sqrt(n) ~ sqrt(2 ell)`.  Those are
precisely the low-conductor levels the lane already discharges unconditionally
via exact Fourier inversion plus individual Weil (levels below
`ell - ceil(log2 ell)`).  **So the p-adic angle strictly under-covers the
existing classical near-endpoint theorem.**

Level 15 completed after the table above was written: `0/16384` characters
match `RHP` exactly, but again **`0/16384` fall below it**.  Running total for
the Newton-over-Hodge check at `p=2`: **32766 primitive characters, levels 2
through 15, zero violations.**

## 19:40Z -- THE OBSTRUCTION, stated as a theorem (PROVED) and refuted (witness)

**Theorem (trace-route slope dichotomy).**  Let `lambda_min` be the smallest
Frobenius slope on `H^1(C_ell)`, normalized by `v_2(2)=1`, and let
`n = 2ell+1`.  The only bound on `v_2(T_n)` obtainable from the Newton polygon
alone is `v_2(T_n) >= n * lambda_min`.  Then:

1. `Delta_(ell,n)` is even **iff** `v_2(T_n) >= ell+1`, since `T_n =
   -2^ell Delta_(ell,n)`.
2. `n * lambda_min >= ell+1` forces `lambda_min >= (ell+1)/(2ell+1) > 1/2`.
3. Poincare duality pairs `alpha <-> 2/alpha`, so the slopes are symmetric
   about `1/2` and `lambda_min <= 1/2` always, with equality **iff every slope
   is `1/2`, i.e. iff `C_ell` is supersingular**.
4. If `C_ell` is supersingular then `n * lambda_min = ell + 1/2`, and since
   `T_n` is a rational integer, `v_2(T_n) >= ell+1`.

So: **supersingularity of `C_ell` is the unique Newton-polygon hypothesis that
implies the odd endpoint through the trace valuation -- nothing weaker can, and
nothing stronger exists.**

**REFUTED, with an exact witness.**  `C_ell` is not supersingular for
`ell >= 4`: all eight primitive characters of exact conductor `x^5` have Newton
slope multiset exactly `{1/4, 1/2, 3/4}`, so `lambda_min(C_ell) <= 1/4` for
every `ell >= 4`.  (Computed exactly in `Z[zeta_8]` by repeated division by
`1-zeta`; no floating point.  Independent of, and sharper than, the lane's
existing refutation via `T_(10,22) = -5120`, which needed an even-degree trace
divisibility argument at level ten -- level four already does it, and gives the
whole spectrum rather than one bit.)

**Confirming the mechanism at the two levels where it does hold:** `C_2` and
`C_3` *are* supersingular (every slope `1/2`, all six characters), and
correspondingly `v_2(Delta_(2,5)) = v_2(Delta_(3,7)) = 1`, both even, both with
`I_n(1)` odd -- exactly as the theorem says.  The mechanism is real; it simply
dies at `ell = 4`.

**Corollary (the honest bottom line for this field).**  No Newton-polygon or
Hodge-polygon theorem -- including a hypothetical `p=2` extension of
Kramer-Miller / Kramer-Miller-Upton, and including exact determination of every
character's polygon -- can prove Lemire's odd endpoint by the trace-valuation
route.  Newton polygons produce **lower** bounds on valuations; the endpoint
needs an **upper** bound on the valuation of one specific integer combination
(`Delta - 1`).  Vertex-contact results (KMU Theorem 1.1) do give exact
valuations, but of individual `L`-polynomial *coefficients*, and the passage
from coefficients to the `n`-th power sum via Newton's identities destroys
exactness the moment more than one slope is present.

## 19:44Z -- dead end also on the computational side

Since the object is a point count, one might hope p-adic cohomology contributes
computationally (extend the verified range rather than prove a theorem).  It
does not:

- `genus(C_ell) = (ell-2) 2^(ell-1) + 1` (lane's identity, from
  `Z_(K_ell)(z) = D_ell(z)/((1-z)(1-2z))`).
- Denef-Vercauteren, the only p-adic point counter that runs at `p=2` for
  Artin-Schreier curves, costs `O(g^(5+eps) log^(3+eps) q)`, i.e. roughly
  `2^(5 ell)` here.
- The lane's existing Hayes NTT transform computes the same `Delta` in
  `O(2^ell * n)`.

So the exact Fourier route already in the repository beats p-adic point counting
by a factor around `2^(4 ell)`.  DEAD END, quantified.

## 19:46Z -- dead ends recorded

- **DWX / RWXY import.**  Their towers are rank one (`Z_p`) and rank `ell` over
  an *unramified* coefficient ring (`Z_(p^ell)`).  Ours is
  `(F_2[t]/t^(ell+1))^*`, a product of many cyclic 2-groups whose exponent
  grows only like `2^(log2 ell)` -- infinite rank in the limit.  Their theorems
  do not transfer.  What *does* transfer is the *prediction*: slopes
  equidistributed at spacing `1/Swan`.  Experiment 1 confirms it, exactly at
  power-of-two levels and up to lattice rounding elsewhere.  Confirming a
  prediction that the lane already measured is not a bridge.
- **`NP = ` lattice-rounded Hodge as a universal law.**  REFUTED (`L=9`,
  `chi=257`; and `L=15`, 0/16384).
- **"Power-of-two levels are exactly ordinary" as a proven law.**  OPEN;
  verified at `L = 2, 4, 8` only (138 characters).  `L=16` is out of the
  current work-cell guard and would cost ~10 minutes.
- **`p`-rank / Deuring-Shafarevich.**  Already correctly diagnosed in
  ADR-0559: `gamma(C_ell)=0` controls the zeta numerator mod 2 only.  My
  Experiment 3 quantifies exactly how far short that is: it fixes the
  slope-zero stratum, which is empty, while the needed precision is `ell+1`
  bits.
- **a-numbers / higher a-numbers (Booher-Cais-Kramer-Miller-Upton).**  Wrong
  invariant (`alpha_p`-torsion of the Jacobian, not the point count mod `2^k`)
  and wrong tower (cyclic `Z_p`, and `d | p-1` forces `d=1` at `p=2`).

## 19:50Z -- a measured probabilistic model for the residual

Restricting to the top three conductor layers (`j >= ell-2`, `j >= 4`), the
excess `v_2(T_(j,n)) - (j-1)` over the free counting divisibility, `n=2ell+1`,
`ell=2..18`, `N=42` samples:

```text
excess    0     1     2     3     5     6
count    14    15     7     3     1     2
frac   .333  .357  .167  .071  .024  .048
2^-(k+1) .500 .250  .125  .062  .016  .008
```

and the endpoint valuations themselves, `ell = 2..18`:

```text
v_2(Delta_(ell,2ell+1)):  0:7  1:4  2:3  3:1  5:1  7:1     (17 rows)
geometric expectation:    8.5  4.25 2.1  1.06 .27  .07
```

Both are consistent with "`Delta - 1` behaves 2-adically like a random
integer".  Under that model, (R1) fails at a given `ell` with probability
`2^(-(ell+1))`, which is summable: **Borel-Cantelli predicts finitely many
failures, and the verification through degree 400 already covers `ell` up to
about 200, leaving expected failures below `2^(-200)`.**  That is a heuristic,
not evidence for a proof technique -- but it is the right thing to print in the
paper of Move 2, because it explains why the conjecture is true without
suggesting that any slope theorem will prove it.

---

# FINDINGS

## (a) Sharpest reformulation

**PROVED, elementary, from the lane's own odd reduction.**  For `n = 2ell+1`:

```text
I_n(1) = (2^(ell+1) + Delta_(ell,n) - 1) / n,       n odd, so

  Lemire's odd endpoint at n   <=>   Delta_(ell,2ell+1) !== 1  (mod 2^(ell+1))
                               <=>   #C_ell(F_(2^n)) !== 2^ell + 1 (mod 2^(2ell+1))
  and                       v_2(I_n(1)) = v_2(Delta_(ell,n) - 1)   when <= ell.

  SUFFICIENT, one bit:  Delta_(ell,2ell+1) EVEN  ==>  I_n(1) ODD  ==>  I_n(1) != 0.
```

This is strictly weaker than the refuted `(C8)` (which demanded a *fixed*
modulus) and strictly stronger in usefulness than "`|Delta| <= 2^ell`" (which
needs the square-root-plus-log saving).  It reduces an existence theorem about
irreducible polynomials to **the parity of one integer**, in `10` of the `17`
computed rows `ell = 2..18`, and to at most 3 bits in all `17`.

Recommended ledger name: `odd endpoint <=> Delta !== 1 mod 2^(ell+1)`, with the
parity corollary as the cheap sufficient half.

## (b) Most promising technique in this field, with citations

Honestly: **there is no promising technique in this field for the endpoint
itself.**  The best available frame is Kramer-Miller's Newton-over-Hodge bound
(arXiv:2006.04936, `p>=3`) with the Kramer-Miller-Upton local-to-global vertex
criterion (arXiv:2110.08656, `p` odd; local Hodge slopes `{1/d_P,...,
(d_P-1)/d_P}` for Swan conductor `d_P`), applied to the tower recognized as an
abelian ASW cover of `A^1` wild at one point with Swan `= j` at exact conductor
`x^(j+1)`.  Both fix `p` odd in their first paragraph, verified by fetching the
papers.  DWX (arXiv:1310.5311) and RWXY (arXiv:1605.02254) are the right slope
*predictions* and the wrong Galois groups.

The one genuinely publishable p-adic item this lane can now claim is a
**spinoff, not a bridge**:

> **Conjecture (p=2 Newton-over-Hodge for the binary Carlitz tower).**  For
> every primitive character `chi` of exact conductor `x^(L+1)` over `F_2(t)`,
> `NP(L(chi))` lies above the Kramer-Miller Hodge polygon with Swan conductor
> `L`, and in fact above its round-up to the value group of `Q(zeta_ord(chi))`.
> **Verified for all 32766 primitive characters at levels `L = 2..15`,
> exactly, with zero violations.**  Moreover at `L = 2, 4, 8` every character
> attains the fully equidistributed spectrum `{1/L, ..., (L-1)/L}`.

Removing the `p >= 3` hypothesis from arXiv:2006.04936 is a real question that
an expert can evaluate, and this data is the strongest evidence for it that I
know of.  It is worth externalizing alongside the lane's Move-3 lemmas.  It
will **not** prove Lemire; see (c).

## (c) Decisive obstructions

1. **PROVED: supersingularity is the unique sufficient slope hypothesis, and it
   is false.**  `Delta` even `<=> v_2(T_n) >= ell+1`; the Newton polygon gives
   only `v_2(T_n) >= n * lambda_min`; `n*lambda_min >= ell+1` forces
   `lambda_min > 1/2`, impossible since duality makes the slopes symmetric about
   `1/2`; `lambda_min = 1/2` (supersingular) does suffice, by integrality.
   **REFUTED for `ell >= 4`** with an exact witness: all eight level-4
   primitive characters have slope multiset `{1/4, 1/2, 3/4}`.  Mechanism
   confirmed where it survives: `C_2`, `C_3` are supersingular and their
   `Delta` are even.
2. **MEASURED: the p-adic floor is beaten by trivial counting from `ell = 4`
   on.**  `v_2(T_(j,n)) >= j-1` for free from `T_j = 2^(j-1)(C_0-C_1)`; the best
   slope-derived floor is `ceil(n/e_j)`, pinned at `3-4` for all `ell` because
   `lambda_min ~ 1/j`.  At `ell = 18` the deficit is 15 bits.  Newton-polygon
   information is nontrivial only for `j <~ sqrt(2 ell)` -- strictly inside the
   range the lane already discharges unconditionally.
3. **Structural: polygons bound valuations from BELOW; the endpoint needs an
   upper bound.**  Vertex contact gives exact *coefficient* valuations, but the
   `n`-th power sum mixes coefficients through Newton's identities and its
   valuation is not determined by theirs whenever more than one slope occurs.
4. **Computational: p-adic point counting is `2^(4 ell)` times slower than the
   lane's existing transform** (Denef-Vercauteren `O(g^(5+eps) log^(3+eps) q)`
   with `g = (ell-2)2^(ell-1)+1`, versus `O(2^ell n)`).  There is no
   "extend the verified range with Kedlaya" move here.
5. The 2-adic divisibility that carries the whole problem (`2^ell | T_n`) comes
   from **character orthogonality**, i.e. from the group `(F_2[t]/t^(ell+1))^*`
   having order `2^ell` -- not from geometry.  p-adic cohomology of individual
   characters is structurally blind to it.

## (d) Concrete next experiments runnable here

Ordered by value per minute.  All use the scratchpad crate described at 19:24Z;
none requires touching the repository.

- **E1 (10 min, decides the cleanest conjecture).**  `rhp 16` with
  `limits.max_table_cells` raised to `4e10`: test whether every one of the
  `2^15` primitive characters at the power-of-two level `L=16` has spectrum
  exactly `{i/16}`.  Verified so far at `L = 2, 4, 8`.  A clean statement
  ("binary Carlitz layers at power-of-two conductor are ordinary") is a
  provable-looking target via Gauss sums / a Gross-Koblitz analogue over
  function fields (arXiv:2502.01109 is the nearest relative; note the lane
  already demoted Thakur's Gauss sums for living in characteristic `p`).
- **E2 (2 min).**  Tabulate, per character, the abscissae where `NP` exceeds
  the lattice-rounded Hodge polygon (levels 7, 9, 11, 13, 14, 15) and test
  whether the deviation set is determined by `(L mod ord(chi), ord(chi))`.
  This is the `p=2` shadow of KMU's vertex-contact criterion and is the piece
  a Newton-over-Hodge proof at `p=2` would have to explain.
- **E3 (5 min).**  Extend `layers` to `ell = 19..21` (cost quadruples per
  level; `ell=18` took 11 s) to widen the `v_2(Delta)` sample for the
  Borel-Cantelli table, and cross-check `Delta` against the fleet rows
  `ell=19..21` on a second code path.  My run already re-derived `ell=13..18`
  independently of the endpoint runner; extending that is cheap dual-implementation
  assurance for numbers the ledger currently rests on one path for.
- **E4 (bounded, negative-result value).**  Confirm computationally that the
  `sqrt(n)` crossover in (c2) is exact rather than incidental: for each `ell`,
  print the largest `j` with `ceil(n/e_j) > j-1`, and check it equals
  `floor(sqrt(n))` up to a bounded offset.  Turns a heuristic sentence into a
  measured law before it is written into a paper.

## (e) New to the ledger

1. The odd endpoint `<=>` `Delta_(ell,2ell+1) !== 1 (mod 2^(ell+1))`, and the
   one-bit sufficient form "`Delta` even `=>` done".  PROVED, elementary,
   cheap, and (as far as I can see) not stated anywhere in
   `lemire-half-degree-irreducibles.md` or the ADR chain, which discuss
   `I_n mod 8` but not the equivalence with a single forbidden class.
2. **The trace-route slope dichotomy theorem** in (c1): supersingularity is the
   unique sufficient slope hypothesis.  This upgrades the lane's existing
   "blanket supersingularity refuted at level ten (`T_(10,22) = -5120`)" from a
   refuted *guess* to a **closed classification**: the guess was not merely one
   candidate among many, it was the only one, and it is false already at level
   four.  This is the strongest form in which the p-adic route can be shut.
3. The exact minimum-slope law `lambda_min(level j) = 1/2^(ceil(log2(j+1))-1)`,
   i.e. the minimum slope equals the reciprocal of the ramification index of 2
   in `Q(zeta_(exponent))` -- so the observed minima are lattice-forced, not
   arithmetic accidents.  Extends the ADR-0559 table from `j<=10` to `j<=15`.
4. Full slope spectra per conductor level (`L = 2..10` tabulated at 19:24Z),
   and the observation that `L = 2, 4, 8` are **exactly ordinary**
   (`{i/L}` for every character).
5. **Newton-over-Hodge at `p = 2` verified for 32766 primitive characters,
   levels 2..15, zero violations** -- evidence that the `p>=3` hypothesis of
   arXiv:2006.04936 and the `p` odd hypothesis of arXiv:2110.08656 are
   artefacts of method for this family.  Publishable as a spinoff conjecture;
   explicitly NOT a bridge to Lemire, by (c1).
6. `NP = ` lattice-rounded Hodge polygon: REFUTED as a universal law
   (`L=9, chi=257`; `L=15`, 0/16384 exact matches), while `NP >= RHP` survives
   everywhere.  First segment contact (`lambda_min = 1/e`) holds in every row.
7. The complexity comparison in (c4): Denef-Vercauteren at `p=2` is
   `~2^(5 ell)` against the lane's `O(2^ell n)` transform.  Closes "use Kedlaya
   to extend the range" before anyone tries it.
8. Misattribution correction: arXiv:2006.04936 is **Joe Kramer-Miller alone**;
   the re-aim review credits it to "Kramer-Miller and Upton".  Upton is a
   coauthor on 2110.08656 / 2110.08657 only.
9. Cross-check value: my independent recomputation via `conductor_layers`
   reproduces `Delta_(ell,2ell+1)` for `ell = 13..18` (`-345, -896, 340, 2744,
   -1988, 928`) and every `I_n mod 8` entry of the ADR-0559 list for
   `ell = 2..18`, on a different code path from the endpoint runner.

## Closing epistemic note

Nothing above proves any case of Lemire's conjecture.  The positive content is
one PROVED reformulation (a), one PROVED classification of what the p-adic
route could ever deliver (c1), one REFUTED hypothesis with an exact witness at
level four, and 32766 rows of evidence for a `p=2` Newton-over-Hodge statement
that -- even if proved -- would not close the endpoint.  My angle was rated most
promising; the honest report is that it is the field best placed to say
*precisely why the endpoint is hard*, and worst placed to close it.

---

## 19:55Z -- provenance caveat (shared checkout)

This worktree moved under me while I worked, which matters for replay:

- `HEAD` was `9a49f2023` ("Ledger Wan Zhang Betti bounds") at 19:08Z and
  `39f723ba62b8b48335f3d7c7de18aa399b7a9b56` at 19:55Z -- another lane
  committed during the session.
- `crates/axeyum-cas/src/gf2_hayes.rs` carries another lane's uncommitted
  `+58/-1` diff, last written at **19:31Z**, i.e. *after* my binaries were
  compiled (layers ~19:15Z, rhp ~19:19Z).  I inspected it: it adds
  `fibre_correlation_square_sum` and friends to
  `BinaryDyadicAutocorrelationFibreReport`, which is untouched by
  `hayes_conductor_two_adic_newton_report`, `exact_character_l_coefficients`,
  or `conductor_layers`.  So it cannot have affected any number above, but a
  replay should pin `HEAD` and a clean tree rather than trusting that.

I wrote no repository file other than this diary, ran no mutating git command,
and created no worktree or branch.  All build artefacts and probe sources live
under the session scratchpad.

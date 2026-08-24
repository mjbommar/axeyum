# Ad hoc blocker sweep, agent 02: exponential sums to prime-power moduli

Lane: `agent/gf2/lemire-proof` worktree, ad hoc research challenge (outside
roadmap/gates).  Field assignment: **exponential sums to prime-power moduli**
(Postnikov, Salie, p-adic stationary phase, Blomer--Milicevic, sub-Weyl), and
the transfer of that technology to the wild function-field modulus
`x^(ell+1)` over `GF(2)`.

Epistemic labels used throughout: **PROVED** (a real theorem, with the source
that proves it), **REFUTED (witness)** (a finite exact counterexample kills a
stated claim), **OPEN** (conjectural / unproven / not established here).
Finite computation is evidence, never a theorem.

---

## 2026-08-20 T0 -- orientation

Read, in order: `lemire-review-2026-08-20-reaim.md` (264 lines),
`docs/plan/status/52-gf2-lemire.md` (746 lines, full), and targeted greps of
`lemire-half-degree-irreducibles.md` (3928 lines) and
`lemire-proof-unblocking-bridges.md` (1749 lines).

Blocker restated in my own field's language (checked against the ledger):

- Target: endpoint discrepancy `|Delta| <~ 2^ell` where `ell ~ n/2`.
- Available: Weil/RH per Hayes character, summed over the `~2^ell` wild
  characters of conductor dividing `x^(ell+1)`, giving `ell * 2^ell`.
- The lost factor is exactly `ell = log_2(modulus)`, i.e. the
  Polya--Vinogradov / completion logarithm at summation-length = modulus.

---

## 2026-08-20 T1 -- literature sweep (all links opened and read, not recalled)

### 1. The p^k escape hatch in Z: what it actually is

**Cochrane--Zheng, "A survey on pure and mixed exponential sums modulo prime
powers"** (Illinois J. Math.; PDF at
<https://www.math.ksu.edu/~cochrane/research/ill00p.pdf>, dated 2009-09-08).
Read in full (extracted to text; 1133 lines).  The decisive passages:

- Weil for prime moduli (their (2.2)): `S(f,p)=w_1+...+w_(d-1)`, each
  `|w_i|=sqrt(p)`, from rationality + RH of the associated `L`-function.
- **The prime-power analogue, their (2.6)--(2.8).**  Let `t=ord_p(f')`,
  `C(x)=p^(-t) f'(x)`, and `A={alpha in F_p : C(alpha)=0}` the *critical
  points*.  For `p` odd and `m>=t+2` (or `p=2` and `m>=3`), `S_alpha=0`
  unless `alpha in A`, so `S(f,p^m)=sum_(alpha in A) S_alpha(f,p^m)`, and for
  simple critical points

  ```text
  S(f,p^m) = sum_(alpha in A) e_(p^m)(f(alpha*)) p^((m+t)/2),           m-t even
  S(f,p^m) = sum_(alpha in A) (A_alpha/p) e_(p^m)(f(alpha*)) p^((m+t-1)/2) G_p,  m-t odd
  ```

  where `alpha*` is the unique lift of `alpha` solving
  `p^(-t) f'(x)=0 mod p^[(m-t+1)/2]` and `G_p` is the quadratic Gauss sum.
  Their own summary of the point: "*Since there are at most `d-1` critical
  points, we see from (2.8) that `S(f,p^m)` can be expressed as a sum of at
  most `d-1` complex numbers of moduli `p^((m+t)/2)`, and moreover the values
  of these numbers are explicit.*"

**This is the whole escape hatch, stated exactly.** For `m>=2` one gets
*the same shape as Weil* -- `<= d-1` terms of modulus `p^(m/2)` -- but with
the terms **explicitly evaluated**, by elementary `p`-adic Taylor expansion,
with no Deligne, no RH, no cohomology.  Cochrane--Zheng's Questions 1--3 are
precisely "why does the prime case not have this?"  (Q1: "Is there a general
formula for the values `w_i` in (2.2)?  This is a very deep and unyielding
problem."; Q3: "Is there a unified theory ... that yields both the results of
Weil for `m=1` and the formula stated here for `m>=2`?")

Genealogy of (2.8) per the survey: technique goes back to Salie (1931);
Kloosterman mod `p^m` for `m>=2` is Salie's classical formula (also
Whiteman, Estermann, Carlitz, Williams); higher-dimensional versions are
Katz and **Dabrowski--Fisher, "A stationary phase formula for exponential
sums over `Z/p^m Z`", Acta Arith. LXXX.1 (1997)**
(<http://matwbn.icm.edu.pl/ksiazki/aa/aa80/aa8011.pdf>).

### 2. The strongest savings at the boundary length ~ modulus -- and the
###    exact open question that matches the Lemire blocker

Cochrane--Zheng's upper-bound sections give the *best known uniform* bounds
for `m>=2`.  All of them retain a factor equal to the number of critical
points, i.e. the analogue of the `L`-degree:

```text
(5.3)  |S(f,p^m)| <= (sum_(alpha in A) lambda_alpha) p^(t/(M+1)) p^(m(1-1/(M+1))),
       lambda_alpha = min{nu_alpha, 3.06}
(6.1)  |S(f,p^m)| <= d p^(m(1-1/d*))     (rational f, p odd, m>=2)
```

and then, verbatim:

- **Question 9.** "Is it possible to replace `sum_alpha lambda_alpha` in
  (5.3) with an absolute constant?"
- **Question 10.** "Is it possible to replace the value `d` on the
  right-hand side of (6.1) with an absolute constant?"
- **Question 7.** "For any `eps>0` is there a constant `C(eps)` such that
  `|S(f,p)| <= C(eps)(dp)^(1/2+eps)` for any nonconstant `f`?  ... This type
  of upper bound is plausible if one believes that the `d-1` values `w_i` in
  (2.2) are randomly distributed on the circle of radius `sqrt(p)`."

**FINDING (decisive, and new to the ledger).**  The Lemire blocker -- "delete
the degree factor from `degree x sqrt(modulus)`" -- is *literally*
Cochrane--Zheng Questions 7/9/10, and those are **stated as open in the
classical prime-power setting where every ingredient is already explicit**.
So the `p^k` escape hatch does not supply the missing `log n`; the escape
hatch buys *explicitness of the `w_i`*, not *fewer* `w_i`.  Anyone proposing
"prime-power moduli are easier, so use that" must specify which of Q7/Q9/Q10
they intend to solve.  Label: **OPEN in Z, and therefore no import is
available.**

Caveat that keeps a door open (see T3 below): explicitness is not nothing.
It is exactly what lets Salie sums be *summed over a family with a second
square root of cancellation*, which for prime moduli would need Deligne +
Katz equidistribution and still would not be as strong.

### 3. Postnikov: what it is and the exact hypothesis it needs

Verified statement (as quoted in the sources below): for `p` odd, `beta>=2`,
every Dirichlet character `chi mod p^beta` satisfies

```text
chi(1+pt) = e_(p^beta)( l_chi * log_p(1+pt) ),
log_p(1+pt) = pt - (pt)^2/2 + (pt)^3/3 - ...
```

so `chi` restricted to principal units is an **additive** character composed
with a **polynomial phase**; Weyl/Vinogradov/van-der-Corput then apply.
Sources read:

- **Milicevic, "Sub-Weyl subconvexity for Dirichlet L-functions to prime
  power moduli"** (<https://arxiv.org/abs/1407.4100>, Compositio Math. 152
  (2016)).  Abstract verified: `L(1/2,chi) << p^r q^(theta+eps)` with
  `theta ~ 0.1645 < 1/6`, "breaking the long-standing Weyl exponent
  barrier", via "a general new theory of estimation of short exponential
  sums involving `p`-adically analytic phases, which can be naturally seen
  as a `p`-adic analogue of the method of exponent pairs", applying to
  "phases ... that arise from a stationary phase analysis of
  hyper-Kloosterman and other complete exponential sums".
- **Blomer--Milicevic, "p-adic analytic twists and strong subconvexity"**
  (Ann. Sci. ENS 48 (2015) 561--605) -- the GL(2) companion.
- **Gallagher, "Primes in progressions to prime-power modulus"**, Invent.
  Math. 16 (1972) 191--201
  (<https://link.springer.com/content/pdf/10.1007/BF01425492.pdf>): the
  log-free large-sieve density estimate near `sigma=1` for prime-power
  moduli, later refined by Bombieri.  This is the *prime-power-specific*
  improvement to primes in progressions.

**Why none of these transfers, stated at the mechanism level (PROVED
obstruction):** every one of them is a device for *replacing a missing
Riemann Hypothesis* by an explicit `p`-adic computation (zero-free regions,
log-free density, subconvexity, short-sum cancellation).  Over `F_q[x]` the
Riemann Hypothesis is a **theorem** and it is *sharp per character*: the
Hayes `L`-function is a polynomial of degree exactly `cond-1` all of whose
roots have absolute value `q^(1/2)`, so `|S_chi(n)| <= (cond-1) q^(n/2)`
cannot be improved by any method that only sees one character.  Postnikov
technology can at best reproduce it.  Formally: *the number of stationary
phase cosets equals the `L`-degree*, so stationary phase and RH agree here
to the last factor, and the missing `ell` is a **count of critical points /
zeros**, not slack in an inequality.

---

## 2026-08-20 T2 -- the equal-characteristic analogue of Postnikov EXISTS,
## and it is the Schmid--Witt residue formula (VERIFIED here)

### The structural obstruction to Postnikov, stated exactly

Postnikov needs the `p`-adic logarithm `log_p : 1+pZ_p -> pZ_p`, an
*isomorphism*.  It exists because `Z_p` has mixed characteristic and absolute
ramification one, so `p^k/k` is integral for `k>=2` (`p` odd).

In equal characteristic there is **no logarithm**: `F_2[[x]]` has
characteristic two, `u^2/2` is undefined, `exp` diverges (`n!=0` for
`n>=p`), and `1+xF_q[[x]]` is not isomorphic to `xF_q[[x]]` -- it is a
`Z_p`-module of infinite rank.  Truncated, that is exactly the lane's own
decomposition (`lemire-half-degree-irreducibles.md:1751`):

```text
E_ell = (1+x GF(2)[x])/(x^(ell+1)) = prod_(m odd, m<=ell) Z/2^(L_m),
L_m = #{ j>=0 : m 2^j <= ell },   (1+x^m)^(2^j) = 1 + x^(m 2^j).
```

So **PROVED (classical, Serre, _Local Fields_ II.5; matches the lane's
checked Witt blocks): Postnikov's linearization has no equal-characteristic
analogue in its literal form.**  Any brief that says "use Postnikov" must be
rejected at this line.

### But the *substitute* exists: `dlog` replaces `log`

The correct equal-characteristic replacement is not `log` but the
**logarithmic derivative plus a residue**, which is exactly what
Artin--Schreier--Witt theory uses.  Sources read and verified:

- **Schmid (1936)**, for degree-`p` Artin--Schreier extensions of a local
  field `K` of characteristic `p` with residue field `k`:

  ```text
  [x, y)_1 = Tr_(k/F_p)( res( x * dlog y ) ).
  ```

- **Witt (1936)** generalized this to `Z/p^n`-extensions via
  `[x,y)_n = pi_n( Tr_(W(k)/W(F_p))( res( g^(n-1)(X) * dlog Y ) ) )`
  (ghost-vector version).
- **Kosters--Wan**, "Genus growth in `Z_p`-towers of function fields",
  Proc. AMS 146 (2018) 1481--1494 (arXiv:1703.05420), and "On the arithmetic
  of `Z_p`-extensions" (arXiv:1607.00523), **simplified it to the form
  closest to Schmid's, avoiding ghost vectors**:

  ```text
  [x, y)_n = pi_n( Tr_(W(k)/W(F_p))( res( x~ * dlog y~ ) ) ).
  ```

- Both quoted from **M. Schmidt, "Schmid's formula for higher local
  fields", arXiv:1709.04559**, equations (1.1)/(1.2) and reference list
  [9],[10],[15],[19]; the paper was read in full (PDF -> text).

**This is the exact structural analogue of Postnikov**: a multiplicative
character of the local units is written as an *additive* character of an
explicit, `Witt`-linear expression in the argument.  `log` is replaced by
`dlog`, which exists in every characteristic.  Nothing in this repository's
3928-line canonical note, 1749-line bridges audit, or 746-line lane status
mentions Postnikov, Artin--Hasse, Shafarevich bases, Schmid, or the
Schmid--Witt symbol (grep, 2026-08-20).  **This is new to the ledger.**

### Written out at `r=1` for this problem, and VERIFIED numerically

Specialize: `K = F_2((x))`, `k = F_2`, `Tr = id`, `res = res_(x=0)`.  Take

```text
a = sum_(k=1..ell) c_k x^(-k)   (c_k in F_2),
chi_a(g) = (-1)^( res_(x=0)( a * dlog g ) )
         = (-1)^( sum_(k=1..ell) c_k * [x^(k-1)]( g'/g ) ).
```

Because `[x^(k-1)](g'/g) = p_k(g)`, the `k`-th Newton power sum of the
*inverse roots* of `g` (equivalently the power sums of the reciprocal
polynomial), this says: **every order-two wild Hayes character at level
`x^(ell+1)` is a parity of an `F_2`-linear combination of the first `ell`
power sums of the inverse roots.**  In char 2, `p_(2k) = p_k^2 = p_k`, so
only odd `k` survive -- the Artin--Schreier `wp`-reduction, visible as
Frobenius.

**Computation (exact, `exp04.py`, seconds, `ell=1..8`):** for every one of
the `2^ell` choices of `a`, `chi_a` was checked to be a group homomorphism
on `E_ell` (all pairs for `|E_ell|<=64`, else a `64x64` block), and the
distinct characters counted:

```text
ell : 1  2  3  4  5  6  7  8
#chi: 2  2  4  4  8  8 16 16     == 2^ceil(ell/2) == |E_ell / E_ell^2|
realized exact conductor exponents: {0, 2, 4, 6, 8}   (EVEN only)
```

Every value matches the order-`<=2` subgroup of the dual exactly, and the
conductor exponent is always `1 + (largest odd pole order of a after
wp-reduction)`.  **This independently reproduces, in closed form, the lane's
separately derived quadratic-character census** ("an odd primitive level `j`
contains only `2^((j-1)/2)` quadratic characters ... every even primitive
level contains none", status l.~"binary monomial power-sum characters"):
with the lane's `level j = conductor exponent - 1`, my even conductors
`2t` are their odd levels `2t-1`, with count `2^(t-1) = 2^((j-1)/2)`.  Agreement
is exact for `ell<=8`.

**PROVED (by citation, not by this computation): the full family, all
`2^ell` characters, is obtained the same way** -- characters of order
dividing `2^r` correspond to Witt vectors `a in W_r(F_2((x)))` modulo
`wp = F-1`, with `chi_a(g) = zeta_(2^r)^([a, g)_r)` and `[a,g)_r` the
Schmid--Witt residue above (Serre, _Local Fields_ XIV; Kosters--Wan).  So
the answer to charge item (2) is **yes: the whole wild family linearizes**,
and `Delta` becomes one Artin--Schreier--Witt exponential sum

```text
Delta = sum_(a != 0) sum_(deg g = n) Lambda(g) zeta_(2^r)^( res( a * dlog g ) ).
```

Whether that helps is charge item (3), answered in T4.

Reproduce: `python3 exp04.py` in the scratchpad (self-contained, ~2 s,
< 50 MB).  Nothing was written into the repository by it.

---

## 2026-08-20 T3 -- p=2 peculiarity, quantified: the char-2 critical
## equation is INSEPARABLE, so wild Kloosterman sums are BIGGER than
## square root; and the lane's proved bound is exactly Cochrane--Zheng (5.2)

Charge item (1) asked for `p=2` peculiarities.  The decisive one is not the
familiar `(Z/2^k)^x = Z/2 x Z/2^(k-2)` nuisance; it is this.

For `p` odd, the Kloosterman phase `f(u)=Au+B/u` has
`f'(u) = A - B/u^2`, whose critical congruence `Au^2-B=0 (mod p)` has **two
simple roots or none**.  Simple roots put Cochrane--Zheng (2.7)/(2.8) in
force: `S` is a sum of `<=2` explicit terms of modulus exactly `p^(m/2)`
(Salie's classical formula), i.e. **exact square-root size**.

In characteristic two, `f(u) = u^(-1)+cu` has

```text
f'(u) = c + u^(-2) = ( c^(1/2) + u^(-1) )^2,
```

a perfect square: the critical equation is **inseparable**, every critical
point has multiplicity `nu = 2`, and (2.7) is inapplicable.  The relevant
classical bound is then Cochrane--Zheng (5.2)

```text
|S_alpha(f,p^m)| <= lambda_alpha p^(t/(nu_alpha+1)) p^(m(1-1/(nu_alpha+1))),
```

which at `nu = 2` gives the exponent `p^(2m/3)`, **not** `p^(m/2)`.

That is *exactly* the exponent the lane proved independently: with
`m = ell+1`, `S = ceil((m-1)/3)`, its stationary-phase argument gives
`|K_2(c)| <= 2^(m-S) ~ 2^(2m/3)`
(`lemire-half-degree-irreducibles.md`, "A proved wild-Kloosterman amplitude
bound"; ledger `6e02ac7d6`; fact
`F:gf2-principal-unit-wild-kloosterman-bound`).

**Computation (exact, `exp05.py`, ~70 s, < 100 MB):** exhaustive
`max_(c in R^x) |K_2(c)|` for `R = F_2[x]/(x^m)`, `psi(z)=(-1)^([x^(m-1)]z)`:

```text
 m   |R^x|  max|K|   2^(m/2)   2^(m-ceil((m-1)/3))   max|K| / 2^(m/2)
 2      2       2      2.00           2                1.000
 3      4       4      2.83           4                1.414
 4      8       8      4.00           8                2.000
 5     16       8      5.66           8                1.414
 6     32      16      8.00          16                2.000
 7     64      32     11.31          32                2.828
 8    128      32     16.00          32                2.000
 9    256      64     22.63          64                2.828
10    512     128     32.00         128                4.000
11   1024     128     45.25         128                2.828
12   2048     256     64.00         256                4.000
13   4096     512     90.51         512                5.657
```

Two conclusions, both labelled honestly:

1. **The lane's proved bound `2^(m-ceil((m-1)/3))` is ATTAINED at every
   `m` in `2..13`** (right two columns equal in every row).  Finite
   evidence, not a theorem, but it is decisive evidence that the bound is
   sharp and cannot be tightened towards `2^(m/2)`.
2. **`max|K_2| / 2^(m/2) = 2^(m/2 - ceil((m-1)/3))` grows exponentially**
   (`1 -> 5.657` over `m=2..13`).  So in characteristic two the wild
   Kloosterman sums are *exponentially larger than square root*.

**FINDING (decisive obstruction, new framing for the ledger).**  The `p^k`
stationary-phase machinery, transplanted to `q=2`, moves in the WRONG
DIRECTION on the objects it applies to.  The Salie mechanism -- "two simple
critical points, hence exact `p^(m/2)`, hence explicit values, hence extra
cancellation when summed over a family" -- is destroyed by Frobenius: in
characteristic `p` every critical equation involving an inverse is a `p`-th
power, multiplicity `>= p`, and the exponent degrades from `1/2` to
`1 - 1/(p+1)` (= `2/3` at `p=2`).  This is *the* structural reason the
binary case is the hardest, and it is intrinsic, not an artefact of the
lane's argument.

Cross-reference value: the lane's amplitude theorem is now identified in the
classical taxonomy as the `p=2`, multiplicity-two case of
Cochrane--Zheng (5.2)/(5.10), with `nu=2`.  That also tells the lane exactly
which classical question would have to be solved to improve it:
**Cochrane--Zheng Question 9** ("replace `sum_alpha lambda_alpha` by an
absolute constant"), open since at least 2009.

---

## 2026-08-20 T4 -- the decisive measurement: EXACT |S_chi| summed over the
## family already exceeds the endpoint allowance, from ell=6 on

This is the main new result of this diary, and it is a *stopping test* for
an entire class of proposals (mine included).

### Setup (all exact, two independent implementations)

Reciprocal normalization, as the lane uses: `g(0)=1`, class group
`E_ell = (1+xF_2[x])/(x^(ell+1))`, `|E_ell| = 2^ell`, endpoint degree
`n = 2ell+1`.  With `Lambda` the Mangoldt weight on the monoid
`{g : g(0)=1}`,

```text
2^ell * N_n(1) = (2^n - 1) + Delta,       Delta = sum_(chi != 1) S_chi(n),
S_chi(n) = sum_(deg g = n) Lambda(g) chi(g).
```

Positivity therefore needs `|Delta| < 2^n - 1`, i.e. after the RH
normalization `|Delta| / 2^(n/2) < 2^(ell+1/2)`.  (The strict endpoint wants
`N_n(1) > 1`; the threshold shifts by `O(n)` and nothing below changes.)

Two structurally independent exact computations:

- `exp01.py`: sieve every irreducible of degree dividing `n`, tally the
  `Lambda`-weighted class populations, group-DFT.
- `exp03.py` (and `exp02.py`): build `A_j = sum_(deg g = j) [g]` in
  `Z[E_ell]` for `j <= ell`, DFT, obtain the **exact `L`-polynomial**
  `L_chi(u) = sum_(j=0..ell) chi(A_j) u^j` (`chi(A_j) = 0` for `j > ell`
  by orthogonality), then `S_chi(n) = -sum_i alpha_i^n` by Newton's
  identities.

Control 1: the two routes agree to 3 decimals on `|Delta|/2^(n/2)` at
`ell = 3,5,6,7` (`3.62`, `14.12`, `35.34`, `31.12`).
Control 2: for every `ell <= 14` and every one of the `2^ell - 1` nontrivial
characters, `deg L_chi` equals `(exact conductor exponent) - 1` with **zero
mismatches** -- an independent reproduction of the lane's proved Gao degree
distribution (ledger `1705eb688`) and a validation of the coordinate/FFT
indexing.

### The numbers (`exp03.py`, numpy, whole sweep ~90 s, < 400 MB)

`tgt = 2^(ell+1/2)` is the endpoint allowance;
`WeilD = sum_chi deg L_chi` is the Weil-triangle budget;
`L1 = sum_(chi != 1) |S_chi(n)| / 2^(n/2)` uses the **exact** values.

```text
ell    n      tgt        WeilD        L1        L1/tgt   |Delta|/2^(n/2)  |Delta|/tgt
 4     9      22.6          49       20.7        0.914        2.87          0.127
 5    11      45.3         129       38.6        0.854       14.12          0.312
 6    13      90.5         321       93.0        1.027       35.34          0.390
 7    15     181.0         769      236.8        1.308       31.12          0.172
 8    17     362.0        1793      512.8        1.416       34.65          0.096
 9    19     724.1        4097     1101.6        1.521       65.76          0.091
10    21    1448.2        9217     2505.1        1.730       36.77          0.025
11    23    2896.3       20481     5306.6        1.832      144.96          0.050
12    25    5792.6       45057    11242.4        1.941      253.14          0.044
13    27   11585.2       98305    24245.9        2.093      244.66          0.021
14    29   23170.5      212993    49609.2        2.141      634.27          0.027
```

### What this says

**(i) REFUTED, with an explicit witness, for every `ell >= 6` computed: the
endpoint cannot be reached by any argument that takes absolute values one
character at a time -- not even with the exact value of every `|S_chi(n)|`.**
`L1/tgt` crosses `1` at `ell = 6` (`1.027`) and increases monotonically to
`2.141` at `ell = 14`.  Fitting `L1 / 2^ell = c * ell^A` on the last rows
gives `A ~ 0.64` (between `1/2` and `1`), so the excess appears to grow
without bound.

This is strictly stronger than the ledger's standing statement of the
blocker ("Weil gives `ell 2^ell` where `2^ell` is needed").  It says the
`ell` is not slack in the Weil inequality that a better individual estimate
could recover: **the true `L1` norm of the family is itself over budget.**
In particular:

- Improving the individual bound from `(j-1) 2^(n/2)` to the conjectural
  square-root-in-the-degree `sqrt(j) 2^(n/2)` (the exact analogue of
  Cochrane--Zheng **Question 7**, and the very best any single-character
  method can aspire to) **still does not close the endpoint** -- the
  measured `L1` already assumes perfect individual knowledge and fails.
- Therefore every remaining route must be *signed*.  This corroborates,
  from a completely different direction, the lane's own repeated finding
  that phase-erasing steps (Cauchy across the family losing `304`/`633`,
  structural-support `L2` needing `1425`/`1483`, packetwise absolute values
  `6433280` vs signed `933888`) are not repairable by sharpening the
  ingredient being absolutely-valued.

**(ii) The good news, and the honest size of the target.**  Define the
achieved cancellation ratio `rho = |Delta| / (WeilD * 2^(n/2))`
(`rho = 1` is no cancellation, `rho ~ 2^(-ell/2)` is square root over the
root family).  Measured at `ell = 14`: `rho = 634.27/212993 = 0.00298`,
i.e. `log2(1/rho) = 8.4` against `ell/2 = 7`.  The needed
`rho_max = tgt/WeilD = 0.1088`.  So **the family exhibits slightly better
than square-root cancellation across its `~ell 2^ell` Frobenius roots, and
is a factor ~36 inside the requirement, while the theorem asks for only a
factor `~ell/sqrt(2)` of cancellation out of a plausible `2^(ell/2)`.**
The gap between what is true and what must be proved is enormous; the
difficulty is entirely that no mechanism produces *any* unconditional
cancellation across the wild family.

`|Delta|/tgt` decreases from `0.39` (`ell=6`) to `0.027` (`ell=14`),
consistent with the lane's degree-400 certification and with the conjecture
being comfortably true.  **Finite evidence; not a theorem.**

### T4b -- the sharper variant also fails: `sum_chi |Re S_chi|`

`Delta` is real (`Delta = 2^ell N_n(1) - (2^n-1)`) and
`S_(chibar) = conj(S_chi)`, so the *sharpest possible* absolute-value route
is `|Delta| <= sum_(chi != 1) |Re S_chi(n)|`.  Measured (`exp06.py`, same
run, same controls):

```text
ell        4      5      6      7      8      9     10     11     12     13     14
L1re/tgt 0.533  0.542  0.690  0.943  0.877  0.984  1.080  1.187  1.234  1.350  1.372
L1re/L1  0.585  0.635  0.672  0.721  0.619  0.647  0.624  0.648  0.636  0.645  0.641
```

**REFUTED for `ell >= 10` (witnesses above): even after using reality of
`Delta` and the exact value of every real part, the triangle inequality is
over budget, and the excess grows.**  (The ratio `L1re/L1 -> 0.64 ~ 2/pi`
is the signature of equidistributed phases -- one more indication that the
`~ell 2^ell` Frobenius angles are generic, so no structural sparsity or
alignment will be found to exploit.)

Combined statement, which I would put in the ledger:

> Any endpoint proof must produce cancellation **among characters**, at a
> stage where the individual character sums are still signed.  Bounding
> `|S_chi|` -- or even `|Re S_chi|` -- optimally, character by character, is
> insufficient from `ell = 6` (resp. `ell = 10`) onward, with exact
> witnesses.  This holds independently of any conjecture about individual
> sums, including the function-field analogue of Cochrane--Zheng Question 7.

---

## 2026-08-20 T5 -- the one bridge from my field that is not yet closed

Given T4, the only exponential-sum technology that can help is one that
produces *signed* information about the Frobenius eigenvalues of the whole
wild family.  In the classical `p^k` world, that technology exists and is
exactly the `p^k`-specific escape hatch: Cochrane--Zheng (2.8) makes the
`w_i` explicit, and explicitness is what allows a *second* summation over a
family (this is how Salie sums beat Kloosterman sums in applications).

The function-field incarnation of "make the wild local contribution
explicit" is **Laumon's principle of stationary phase and the local Fourier
transform**, together with the local epsilon factors it computes:

- G. Laumon, "Transformation de Fourier, constantes d'equations
  fonctionnelles et conjecture de Weil", Publ. Math. IHES 65 (1987) 131--210
  -- the stationary phase principle for `l`-adic sheaves, the origin of
  `FT^((0,infinity))`, `FT^((infinity,0))`, `FT^((infinity,infinity))`.
- A. Abbes and T. Saito, **"Local Fourier transform and epsilon factors"**,
  Compositio Math. 146 (2010); arXiv:0809.0180
  (<https://arxiv.org/abs/0809.0180>) -- verified by reading the abstract
  and the descriptive material: they *explicitly compute the local Fourier
  transform of monomial representations* satisfying a ramification
  condition, and deduce Laumon's formula relating the epsilon factor to the
  determinant of the local Fourier transform.

Why this is the right shape and why it is *not* the already-closed
root-number route (ledger `8b07f7a45`): the lane tested whether the global
**root number** (one scalar per character) determines the endpoint power
sums, and refuted it with distinct power sums inside a common root-number
fibre.  Laumon/Abbes--Saito give strictly more -- the determinant *and* the
break decomposition of the local Fourier transform at the wild point, i.e.
the local factorization that the Schmid--Witt linearization of T2 makes
explicit in coordinates.  Whether that is enough to see cancellation across
the family is **OPEN**, and I did not test it here.

Honest caveat: Abbes--Saito's explicit computation is for *monomial*
representations under a ramification condition.  Our characters at exact
conductor `x^j` are, in the Schmid--Witt coordinates of T2, exactly
"monomial-like" when the Witt vector `a` has a single pole term -- which is
a thin subfamily (T2's `r=1` census: `2^ceil(ell/2)` of `2^ell`).  So the
condition must be checked, not assumed.  That check is the natural next
literature task.

---

## FINDINGS

### (a) Sharpest reformulation in my field

The Lemire endpoint is, in the language of exponential sums to prime-power
moduli, the following statement about **one** modulus `M = x^(ell+1)` in
`F_2[x]` at the Polya--Vinogradov boundary:

> Let `E_ell = (1+xF_2[x])/M`, `|E_ell| = 2^ell`, `n = 2ell+1`.  For each of
> the `2^ell - 1` nontrivial characters, RH over function fields gives
> `S_chi(n) = -sum_(i=1..d_chi) alpha_(chi,i)^n` with `|alpha| = 2^(1/2)`
> and `d_chi = (conductor exponent of chi) - 1` **exactly** (verified here
> for all `2^ell-1` characters, all `ell <= 14`, zero mismatches).  Prove
>
> ```text
> | sum_(chi != 1) sum_(i=1..d_chi) alpha_(chi,i)^n |  <  2^n,
> ```
>
> a sum of `D = sum_chi d_chi = (ell-2)2^ell + 2` unit vectors scaled by
> `2^(n/2)`, where the trivial bound gives `D 2^(n/2) ~ ell 2^(ell) 2^(n/2)`
> and the target is `2^(ell+1/2) 2^(n/2)`.

The classical twin, stated exactly: this is **Cochrane--Zheng Question 9 /
Question 10** -- "can the factor counting critical points (equivalently the
degree) be replaced by an absolute constant?" -- posed for prime-power
moduli in `Z`, where every ingredient is already explicit, and **open there**.
It is also the function-field twin of "the least prime in an arithmetic
progression mod `q` is at most `q^2`", which is open in `Z` under GRH.

### (b) Most promising transferable technique

**Not** Postnikov, and not the `p`-adic exponent-pair machinery
(Milicevic, arXiv:1407.4100; Blomer--Milicevic, Ann. Sci. ENS 48 (2015)):
those exist to substitute for a missing RH, and RH here is a *sharp
theorem*.  See (c).

The transferable one is the **explicitness half of the `p^k` escape
hatch**: Cochrane--Zheng (2.8) (from Salie 1931, via Dabrowski--Fisher,
Acta Arith. 80 (1997)) makes each `w_i` explicit for `m >= 2`, and
explicitness -- not size -- is what permits a second, family-level
summation.  Its function-field incarnation is **Laumon's stationary phase /
local Fourier transform** (Publ. IHES 65 (1987)) with the explicit
computations of **Abbes--Saito, arXiv:0809.0180, Compositio 146 (2010)**,
combined with the **Schmid--Witt linearization** of the whole wild family
(Schmid 1936; Witt 1936; **Kosters--Wan, Proc. AMS 146 (2018) 1481--1494,
arXiv:1703.05420**, simplified ghost-free form; exposition and equations in
**M. Schmidt, arXiv:1709.04559**).  T2 verifies the `r=1` case of that
linearization exactly against this repository's own character census.

### (c) Decisive obstructions (each with its witness or its source)

1. **PROVED (structural).**  Postnikov's linearization
   `chi(1+pt) = e_(p^beta)(l_chi log_p(1+pt))` requires the `p`-adic
   logarithm, which does not exist in equal characteristic
   (`u^2/2` undefined, `exp` divergent, `1+xF_q[[x]]` not isomorphic to
   `xF_q[[x]]`).  The replacement is `dlog` + residue (Schmid--Witt), which
   *is* available -- but it is a change of coordinates, not an estimate.
2. **PROVED (by citation) + measured.**  The `p^k` machinery in `Z` buys
   *explicitness* of the `d-1` numbers `w_i`, never *fewer* of them.
   Deleting the degree factor is Cochrane--Zheng Questions 7/9/10, open in
   `Z`.  Over `F_q[x]` RH is a theorem and is sharp per character
   (`deg L_chi = cond-1`, verified for every character through `ell=14`),
   so no single-character method can gain anything at all.
3. **REFUTED with witnesses (this diary's main result).**  The exact
   `L1` norm `sum_(chi != 1) |S_chi(n)| / 2^(n/2)` already exceeds the
   endpoint allowance `2^(ell+1/2)` for every `ell in {6,...,14}`, with the
   ratio rising `1.027 -> 2.141`; the sharper `sum |Re S_chi|` exceeds it
   for every `ell in {10,...,14}`, ratio `1.080 -> 1.372`.  **Therefore no
   improvement to any individual-character estimate -- up to and including
   the optimal one -- can close the endpoint.**  Cancellation must be
   retained across characters.  (Finite evidence, decisive as a stopping
   test; not a theorem about all `ell`.)
4. **PROVED (mechanism) + measured sharp.**  In characteristic `p` the
   critical equation of an inverse phase is a `p`-th power
   (`d/du (u^(-1)+cu) = (c^(1/2)+u^(-1))^2`), so every critical point has
   multiplicity `>= p`.  Cochrane--Zheng (5.2) at `nu = 2` then gives
   exponent `2m/3`, not `m/2`.  Exhaustive computation confirms
   `max_c |K_2(c)| = 2^(m - ceil((m-1)/3))` for every `m in 2..13`, i.e.
   the lane's proved amplitude bound is **attained**, and exceeds the
   square-root scale by `2^(m/6)`.  So the Salie mechanism -- the single
   most useful `p^k` phenomenon -- is *destroyed by Frobenius* at `q=2`.
   This is the precise sense in which "the escape hatch dies".
5. **Measured, for calibration.**  The family does exhibit slightly better
   than square-root cancellation in practice (`log2(1/rho) = 8.4` vs
   `ell/2 = 7` at `ell=14`; a factor `36` inside requirement), and
   `|Re S_chi| / |S_chi| -> 2/pi`, the signature of equidistributed
   Frobenius angles.  The conjecture is very comfortably true; nothing
   unconditional produces *any* of that cancellation.

### (d) Concrete next experiments runnable here

All bounded, all replayable; none of them was run beyond what is recorded.

1. **Port the exact-family-`L1` sweep to `axeyum-cas`** as a bounded native
   report (suggested name `hayes_exact_family_l1_report`).  The cheap route
   is the one used here: build `A_j = sum_(deg g=j) [g]` in `Z[E_ell]` for
   `j <= ell` only (`chi(A_j)=0` beyond), one mixed-radix DFT, then
   Newton's identities on `L_chi` (degree `<= ell`).  Cost is
   `O(2^ell * ell^2)`, so `ell = 20..24` is reachable in Rust with exact
   cyclotomic arithmetic, versus `ell = 14` in Python here.  Deliverable:
   pin the growth exponent `A` in `L1 ~ c ell^A 2^ell` (measured
   `A ~ 0.64` on `ell in 10..14`) and decide whether `L1/tgt` grows like
   `sqrt(ell)` or faster.  That number is the honest price of every
   absolute-value step in the lane's ledger.
2. **Verify the Schmid--Witt formula at `r = 2`** (order-four characters):
   implement `W_2(F_2((x)))` and the Kosters--Wan residue
   `[a,g)_2 = pi_2(res(a~ dlog g~))`, and check it enumerates exactly the
   order-`<=4` characters of `E_ell` for `ell <= 8`, with exact conductors.
   If it does, the lane gains a **closed form for the entire wild family**
   (`r = ceil(log2(ell))` covers all of `E_ell`), replacing mixed-radix
   discrete logs by an explicit residue pairing.  My `r=1` verification
   (T2) is the base case and already matches the lane's quadratic-character
   census exactly.
3. **Test the Abbes--Saito applicability condition.**  Using the T2
   coordinates, classify which Hayes characters at exact conductor `x^j`
   correspond to *monomial* Witt vectors (single pole term).  If the
   fraction is `2^(ceil(j/2))/2^(j-1)`, the explicit local-Fourier-transform
   computation covers only a thin subfamily and the bridge is priced
   immediately; if larger, it is worth pursuing.
4. **Root-number/eigenvalue-sharing census.**  From the `L_chi` already
   computed, count distinct `L`-polynomials and distinct roots across the
   whole family, per conductor level.  Cheap.  Any repetition would be a
   handle on signed structure; the expected answer (all distinct, generic
   angles) is itself a useful negative datum given item (c5).
5. **`q > 2` control.**  Repeat the T4 `L1/tgt` measurement over `F_3[x]`
   and `F_4[x]` at the same relative endpoint.  If `L1/tgt` stays below `1`
   for larger `q` while diverging at `q=2`, that isolates numerically the
   same `q -> infinity` boundary that Sawin and Sawin--Shusterman need
   (`q > 29`), and would be a clean quantitative statement of why `q=2` is
   the hard case.

### (e) New to the ledger

1. The **exact-`L1` / exact-`|Re S|` stopping test** (T4, T4b) and its
   consequence: *no individual-character estimate, however sharp, can close
   the endpoint.*  I found no equivalent statement in
   `52-gf2-lemire.md`, `lemire-half-degree-irreducibles.md`, or
   `lemire-proof-unblocking-bridges.md`; the existing absolute-value
   refutations there are Cauchy--Schwarz / `L2` / packetwise losses, which
   are weaker (they leave open "sharpen the ingredient").
2. The identification of the blocker with **Cochrane--Zheng Questions 7/9/10**,
   open in `Z` for prime-power moduli, which prices any future "prime
   powers are easier" proposal at zero without further argument.
3. The identification of the lane's own proved wild-Kloosterman amplitude
   bound as the **`p=2`, multiplicity-two case of Cochrane--Zheng
   (5.2)/(5.10)**, plus exhaustive evidence (`m <= 13`) that it is
   **attained**, plus the mechanism (inseparability of the critical
   equation) that explains why characteristic two cannot have a Salie-type
   square-root evaluation.
4. **Schmid--Witt as the equal-characteristic Postnikov**, with the `r=1`
   identity written out and verified: `chi_a(g) = (-1)^(res(a dlog g))`,
   equivalently a parity of `F_2`-linear combinations of the inverse-root
   power sums; and the observation that this reproduces in closed form the
   lane's independently derived quadratic-character census.  No prior
   mention of Postnikov, Artin--Hasse, Shafarevich, Schmid, or Schmid--Witt
   anywhere in the lane's documents.
5. **Laumon / Abbes--Saito local Fourier transform** as the untried,
   correctly-shaped bridge (signed, family-wide, wild-ramification-native),
   distinguished from the already-closed root-number route.

### Dead ends recorded

- Postnikov / `p`-adic exponent pairs / sub-Weyl / Blomer--Milicevic:
  **dead by construction** (they replace a missing RH; ours is proved and
  sharp).  Do not spend further time.
- Gallagher's log-free density estimate for prime-power moduli
  (Invent. Math. 16 (1972) 191--201): **dead** for the same reason -- it is
  a zero-density statement, and over function fields all zeros are already
  known to be on the critical line.
- Salie-style exact evaluation of the char-2 wild Kloosterman sum:
  **dead as an amplitude improvement** (the sums are exponentially larger
  than square root; witness table in T3).  It remains alive only as an
  *explicitness* statement -- which is the T5 bridge, not an estimate.
- Sharpening `|S_chi|`, for any single `chi`, by any method:
  **dead by T4/T4b.**

### Files produced (scratchpad only; nothing written into the repository
### except this diary)

`exp01.py` (direct sieve + DFT control), `exp02.py`/`exp03.py`/`exp06.py`
(exact `L`-polynomial family sweep), `exp04.py` (Schmid residue formula
verification), `exp05.py` (binary wild Kloosterman amplitude), in
`$SCRATCH/`.  Peak memory under 400 MB; total runtime under 5 minutes.

---

## Appendix -- reproduction scripts (inlined so they survive the scratchpad)

### A1. Exact family sweep (T4/T4b): `L1`, `L1re`, `|Delta|`, degree control

Run: `python3 A1.py 14`.  Requires numpy only.  ~90 s, < 400 MB for
`ell <= 14`.  Prints one line per `ell`; `deg-mismatch` must be `0`
(it is the control that `deg L_chi = conductor exponent - 1`).

```python
import sys, math, numpy as np

def polmulmod(a,b,md):
    r=0; mask=(1<<md)-1
    while b:
        if b&1: r^=a
        b>>=1; a=(a<<1)&mask
    return r&mask

def setup(ell):
    L={m: max(j for j in range(0,ell+1) if m*(1<<j)<=ell)+1 for m in range(1,ell+1,2)}
    keys=sorted(L); dims=[1<<L[k] for k in keys]
    md=ell+1
    coord=np.zeros((1<<ell, len(keys)), dtype=np.int64)
    for t in range(1<<ell):
        u=1|(t<<1)
        d=[0]*len(keys); v=u
        for i in range(1,ell+1):
            if (v>>i)&1:
                m=i; j=0
                while m%2==0: m//=2; j+=1
                d[keys.index(m)]+=(1<<j)
                v=polmulmod(v,1|(1<<i),md)
        for a in range(len(keys)):
            coord[t,a]=(-d[a])%dims[a]
    return keys,dims,coord

def run(ell):
    keys,dims,coord=setup(ell)
    nax=len(dims)
    flat=np.zeros(1<<ell,dtype=np.int64)
    mul=1
    for a in range(nax):
        flat+=coord[:,a]*mul; mul*=dims[a]
    A=np.zeros((ell+1,1<<ell),dtype=np.complex128)
    A[0,flat[0]]+=1
    for n in range(1,ell+1):
        mids=np.arange(1<<(n-1),dtype=np.int64)
        polys=(mids<<1)|(1<<n)      # value of t where u=1|(t<<1); t = poly>>1
        t=(polys)>>1
        np.add.at(A[n],flat[t],1.0)
    A=A.reshape((ell+1,)+tuple(reversed(dims)))
    for a in range(nax):
        A=np.fft.fft(A,axis=len(dims)-a)   # axis order: last axis = dims[0]
    A=A.reshape(ell+1,-1)
    n=2*ell+1; sq=2**(n/2)
    # conductor levels
    lev=np.zeros(1<<ell,dtype=np.int64)
    for i in range(1,ell+1):
        gi=1|(1<<i)
        t=gi>>1
        c=coord[t]
        # character index decomposition: flat index -> mixed radix with dims[0] fastest
        idxs=np.arange(1<<ell)
        ph=np.zeros(1<<ell)
        rem=idxs.copy()
        for a in range(nax):
            tt=rem%dims[a]; rem//=dims[a]
            ph+= tt*c[a]/dims[a]
        nz=np.abs(ph-np.round(ph))>1e-9
        lev[nz]=i
    lev=np.where(lev>0,lev+1,0)
    # NOTE: fft index ordering must match. Verify via Parseval/degree check below.
    tot=0.0; l1=0.0; l1re=0.0; l2=0.0; mx=0.0; Delta=0j
    degs=np.zeros(1<<ell,dtype=np.int64)
    bad=0
    for ci in range(1<<ell):
        if lev[ci]==0: continue
        coef=A[:,ci]
        d=ell
        while d>0 and abs(coef[d])<1e-6: d-=1
        degs[ci]=d
        if d!=lev[ci]-1: bad+=1
        e=[((-1)**k)*coef[k] for k in range(d+1)]
        p=[0j]*(n+1)
        for k in range(1,n+1):
            s=0j
            for i2 in range(1,min(k,d)+1):
                s+= ((-1)**(i2-1))*e[i2]*p[k-i2]
            if k<=d: s+= ((-1)**(k-1))*k*e[k]
            p[k]=s
        S=-p[n]
        Delta+=S; a=abs(S)/sq; l1+=a; l1re+=abs(S.real)/sq; l2+=a*a; mx=max(mx,a)
    tgt=2**(ell+0.5)
    print(f"ell={ell:3d} n={n:3d} deg-mismatch={bad} target={tgt:12.1f} "
          f"WeilD={int(degs.sum()):8d} L1={l1:12.1f} L1/tgt={l1/tgt:6.3f} "
          f"L1/(ell*2^ell)={l1/(ell*2**ell):6.4f} L1/(sqrt(ell)*2^ell)={l1/(math.sqrt(ell)*2**ell):6.4f} "
          f"L1re={l1re:11.1f} L1re/tgt={l1re/tgt:6.3f} L2={math.sqrt(l2):9.2f} |Delta|={abs(Delta)/sq:9.2f}")
    sys.stdout.flush()

for ell in range(4,int(sys.argv[1])+1):
    run(ell)
```

### A2. Schmid residue formula for the order-two wild Hayes characters (T2)

Run: `python3 A2.py`.  Pure Python, ~2 s.  Checks that
`chi_a(g) = (-1)^(res(a dlog g))` is a homomorphism on `E_ell` for every
`a`, counts distinct characters (must equal `2^ceil(ell/2)`), and lists the
realized exact conductor exponents (must be even).

```python
import sys
# Schmid residue formula check: chi_a(g) = (-1)^{sum_k c_k * [x^{k-1}](g'/g)}, a = sum c_k x^{-k}
def dlog(g, ell):
    # g int bitmask, g(0)=1; return list of coeffs of g'/g for x^0..x^{ell-1}
    md=ell
    gp=0
    for i in range(1,ell+1):
        if (g>>i)&1 and i%2==1: gp|=1<<(i-1)
    # invert g mod x^ell
    inv=1
    for k in range(1,md):
        # Newton-free: solve (g*inv)=1 coefficientwise
        s=0
        for j in range(0,k):
            if ((inv>>j)&1) and ((g>>(k-j))&1): s^=1
        if s: inv|=1<<k
    # multiply gp*inv mod x^ell
    r=0
    for i in range(md):
        if (gp>>i)&1:
            r ^= (inv<<i)
    r &= (1<<md)-1
    return [(r>>i)&1 for i in range(md)]

def polmulmod(a,b,md):
    r=0; mask=(1<<md)-1
    while b:
        if b&1: r^=a
        b>>=1; a=(a<<1)&mask
    return r&mask

for ell in range(1,9):
    md=ell+1
    elts=[1|(t<<1) for t in range(1<<ell)]
    dl={g:dlog(g,ell) for g in elts}
    chars={}
    for c in range(1<<ell):   # bits: bit k-1 = c_k
        vals={}
        for g in elts:
            s=0
            for k in range(1,ell+1):
                if (c>>(k-1))&1: s^= dl[g][k-1]
            vals[g]=(-1)**s
        # homomorphism check
        hom=True
        for g in elts[:min(len(elts),64)]:
            for h in elts[:min(len(elts),64)]:
                if vals[polmulmod(g,h,md)]!=vals[g]*vals[h]: hom=False;break
            if not hom: break
        key=tuple(vals[g] for g in elts)
        chars.setdefault(key,[]).append(c)
        if not hom:
            print(f"  ell={ell} c={c:0{ell}b} NOT a homomorphism"); break
    # conductor per distinct character
    conds={}
    for key,cs in chars.items():
        d=dict(zip(elts,key))
        lev=0
        for i in range(1,ell+1):
            if d[1|(1<<i)]==-1: lev=i
        conds[key]=lev+1 if lev else 0
    # expected: number of order-<=2 characters of E_ell = 2^ceil(ell/2)
    import math
    print(f"ell={ell}: distinct chi_a = {len(chars)}   expected 2^ceil(ell/2) = {2**((ell+1)//2)}   "
          f"conductors={sorted(set(conds.values()))}  all-homomorphisms=True")
```

### A3. Binary wild Kloosterman amplitude (T3)

Run: `python3 A3.py`.  Pure Python, ~70 s through `m = 13`.  Compare the
`max|K|` column against `2^(m - ceil((m-1)/3))`.

```python
import sys,math
def mulmod(a,b,md):
    r=0;mask=(1<<md)-1
    while b:
        if b&1:r^=a
        b>>=1;a=(a<<1)&mask
    return r&mask
def inv(a,md):
    # Newton / brute for small
    r=1
    for _ in range(md.bit_length()+2):
        r=mulmod(r,(2 ^ mulmod(a,r,md)) if False else (1 ^ mulmod(a,r,md) ^ 1),md) if False else r
    # simple: solve by coefficient recursion
    x=1
    for k in range(1,md):
        s=0
        for j in range(k):
            if ((x>>j)&1) and ((a>>(k-j))&1): s^=1
        if s: x|=1<<k
    return x
print(" m   |Rx|   max|K|  2^(m/2)  2^(m-ceil(m/3))  ratio_to_sqrt   #c with |K|>2^(m/2)")
for m in range(2,14):
    units=[u for u in range(1<<m) if u&1]
    invs={u:inv(u,m) for u in units}
    top=m-1
    best=0; cnt=0
    for c in units:
        s=0
        for u in units:
            z=invs[u]^mulmod(c,u,m)
            s+= 1 if not ((z>>top)&1) else -1
        if abs(s)>best: best=abs(s)
        if abs(s)>2**(m/2)+1e-9: cnt+=1
    print(f"{m:3d} {len(units):6d} {best:8d} {2**(m/2):8.2f} {2**(m-((m+2)//3)):14d} {best/2**(m/2):13.3f} {cnt:8d}")
    sys.stdout.flush()
```

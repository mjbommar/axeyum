# AC-Bridge workstream B: the wild Hast--Matei program

Date opened: 2026-08-20.  Board: `10-angles-board.md`, workstream B.
Charge: equation-level read of Hast--Matei's proof of Theorem 1.4; locate every
use of `p > n`; determine what survives at `p = 2` for the endpoint family;
connect to sweep-06's localized trace formula; deliver the minimal wild
statement and an honest tractability verdict.

Everything below labelled PROVED / REFUTED (with witness) / OPEN.  Every paper
statement was fetched today and read from the fetched text; nothing is recalled.
Finite computation is evidence, never a theorem.

Source of record: **Hast, Matei, *Higher moments of arithmetic functions in
short intervals: a geometric perspective*, arXiv:1604.02067v2 (1 Dec 2016),
IMRN 2019 no. 21, 6554-6584**, fetched as PDF from
`https://export.arxiv.org/pdf/1604.02067` and read via `pdftotext -layout`.
arXiv carries v1 and v2 only; v2 is what is quoted here.  Section, lemma and
theorem numbers below are v2's.  Note the numbering shift a reader should
expect: the abstract-level statements are **Theorem A** (geometry) and
**Theorem B** (arithmetic); Theorem B is restated in Section 1.3 as
**Theorem 1.4**, which is the statement diary 02 translated.

Also fetched and read first-hand today:
- **Sawin, *A representation theory approach to prime number theory and the
  distribution of the divisor function*, arXiv:1809.05137** (Duke 2021),
  `https://export.arxiv.org/pdf/1809.05137` -- for Lemma 2.3, which turns out to
  be the published upper bound this workstream needs.
- **Bank, Bary-Soroker, Rosenzweig, *Prime polynomials in short intervals and in
  arithmetic progressions*, arXiv:1302.0625v3** (Duke 2015) -- for Lemma 3.2,
  which Hast--Matei cite inside their irreducibility proof and which had to be
  checked for a hidden characteristic hypothesis.

New code: `crates/axeyum-cas/examples/acb_whm_strata.rs` (new file; nothing
existing edited).

---

## Log

### 2026-08-20T19:40Z -- the architecture of the proof, in one page

The chain from geometry to Theorem 1.4 is short and every link is visible:

```text
Lemma 2.2  (determinant identity, over Z)
   |
Cor 2.4    (A^s_r full rank  <=>  #{x_i} >= s)
   |                                         Lemma 2.6  (char k > n)
   |                                              |
Prop 2.5 (m = 2 singular locus, codim 2h+3)  Thm 2.7 (m >= 2, codim 2h+3)
   |                                              |
Lemma 2.8 / Prop 2.10 (irreducibility)  --------->|
                                                  |
Thm 3.1 [Ghorpade--Lachaud Prop 3.3] -> Cor 3.3 (H^r = Q_l(-r/2) for r >= R)
                                        Prop 3.5 (S_n^m acts trivially for r >= R)
                                                  |
Lemma 4.2 (twisted point count, Grothendieck--Lefschetz)
                                                  |
Thm 4.4 (von-Mangoldt-type functions)  ->  Cor 4.9/4.10 (Lambda), 4.12 (mu)
                                                  =  Theorem 1.4
```

with the **triviality/vanishing threshold**

```text
R  =  2 dim X - (2h+3) + 2  =  2n + 2(m-2)(h+1) - 1 ,
dim X_(m,n,h) = n + (m-1)(h+1) - 1 ,   codim Sing X = 2h+3 .
```

Two verbatim quotes that fix the whole dependency question.

Remark 4.1: *"If `m >= 3`, we additionally restrict `q` to powers of primes
`p > n`.  We suspect that this restriction (due solely to the failure of
Lemma 2.6 in low characteristic) could be avoided by more refined reasoning
about the singular locus of `X_(m,n,h)`."*

Footnote 1 (attached to Remark 1.5): *"In contrast, the `m > 2` case of
Theorem A itself -- i.e., the statement about cohomology -- does not follow
formally from the `m = 2` case."*

So the authors themselves assert the tameness use is a **single point**, and
that the `m > 2` arithmetic bound (but not the cohomology) is formally weaker
than the `m = 2` one.  Both assertions check out below, with one caveat and one
correction.

### 2026-08-20T19:55Z -- charge 1: the complete dependency table

Every step of the proof, with its characteristic behaviour.  "Char-free" means
I read the proof and it uses no division by an integer `<= n`, no separability,
and no Newton identity.

| # | Step | Statement | Uses `p > n`? | What breaks at `p = 2` | Substitute available |
|---|------|-----------|---------------|------------------------|----------------------|
| 1 | Lemma 2.2 | `det B_(i1..is) = prod (x_ia - x_ib)` | **No** | -- (polynomial identity over `Z`; degree + divisibility + leading coefficient `C = 1`) | n/a |
| 2 | Cor 2.4 | `A^s_r` full rank iff `#{x} >= s` | **No** | -- | n/a |
| 3 | Prop 2.5 | `codim Sing X_(2,n,h) = 2h+3` | **No** | -- (the criterion `#(z_1 u z_2) <= n-h-2` is derived from Cor 2.4 alone) | n/a |
| 4 | **Lemma 2.6** | `dim{ #{w} <= s, e_j(w) = c_j (j<=t) } = max{s-t,0}` | **YES, twice** | (i) Newton's identities `e_j <-> p_j` need `1..n` invertible; (ii) the stratum Jacobian entry `alpha_i j v_i^(j-1)` needs `alpha_i j != 0` | **REFUTED at `p=2`** (19:40 below); replaced by a *quantified* bound `delta` |
| 5 | Lemma 2.8 | `Z_w` irreducible | **No** (cites [BBSR, Lem. 3.2]) | -- : BBSR Lemma 3.2 is stated for *any* algebraically closed `F` and proved by exhibiting the nonvanishing coefficient `g(alpha) A_1`; needs only `h >= 1`, which Thm 1.4 assumes | n/a |
| 6 | Lemma 2.9 / Prop 2.10 | `X_(m,n,h)` irreducible (flatness via EGA IV.2 6.1.5) | **No** | -- | n/a |
| 7 | **Thm 2.7** | `codim Sing X_(m,n,h) = 2h+3`, `m >= 3` | **YES**, only via step 4, only at `(s,t) = (n-h-2, n-h-1)`, only to get `T_(n-h-2) n Z_w` **finite** | the upper bound on `dim Sing` degrades by `delta = max_w dim(T_s n Z_w)` | **repaired here** (20:40 below), conditional on `2 delta <= h+1` |
| 8 | Thm 3.1 | [GL, Prop. 3.3] complete-intersection vanishing | **No** (GL is char-free) | -- | n/a |
| 9 | Cor 3.3 | `H^r = Q_l(-r/2)`, `r >= R` | inherits 7 | threshold `R` moves down by `delta` | via 7 |
| 10 | Lemma 3.4 | `S_N` acts trivially on `H^*(P^(N-1))` | **No** | -- | n/a |
| 11 | Prop 3.5 | `S_n^m` acts trivially on `H^r`, `r >= R` | inherits 7 (also uses [GL, Thm 2.4 / Prop 2.5] semi-regular pairs, char-free) | as 9 | via 7 |
| 12 | Lemma 4.2 | `#{Frob = sigma} = q^(n+(m-1)(h+1)) + O(q^(n+(m-2)(h+1)))` | inherits 7 | error exponent rises by `delta/2` | via 7 |
| 13 | Thm 4.4 | von-Mangoldt-type moment asymptotic | inherits 12 | as 12 | via 7 |
| 14 | Cor 4.9/4.10 | `Lambda` and `Lambda - 1` moments | inherits 13 | as 12 | via 7 |
| 15 | Cor 4.12 | `mu` moments | inherits 13 | as 12 | via 7 |
| 16 | Thm 5.1 / C | `Gr_W^(2n-2) H^(2n-2)(X_2)` as `S_n x S_n`-rep | **No** (`m = 2`), but uses Rodgers' analytic input | -- | n/a |

**Findings from the table.**

1. The four candidate tameness uses in the charge map as follows.
   (i) *Galois group of the generic polynomial being `S_n`*: **not used**.
   Hast--Matei never invoke `S_n`-monodromy; the `S_n^m`-action is a geometric
   action on ordered roots, present in every characteristic.  This is the
   sharpest structural difference from Bank--Bary-Soroker--Rosenzweig and from
   Sawin, both of which do need a Galois/monodromy input.
   (ii) *`A_n` vs `S_n` and square-discriminant strata*: **not used**.
   (iii) *Burnside / orbit counting with char-0 representation theory*: **not
   used**; the counting is Grothendieck--Lefschetz plus Lemma 3.4, both
   char-free.  What plays the role of representation theory is Prop 3.5
   ("the action is trivial in the computed range"), which is inherited from the
   singular-locus dimension and nothing else.
   (iv) *Lang--Weil / Weil constants needing tame monodromy*: **not used**;
   Deligne's weight bound is applied through [GL], which is char-free.  The
   constants are Betti numbers, not monodromy constants.
2. So the tameness dependency of the whole paper is **one lemma, used once, at
   one parameter pair**.  Hast--Matei's Remark 4.1 is exactly right, and the
   BBSR citation inside Lemma 2.8 -- the one place a hidden hypothesis could
   have lurked, since BBSR's own main theorems are stated for `p > n` -- is
   clean: their Lemma 3.2 is char-free.  Verified by reading BBSR's proof, not
   its context.
3. **Correction to diary 02, item 2.**  Diary 02 records "the `m = 2` case is
   unconditional at `q = 2`".  True, and worth sharpening: it is unconditional
   because Prop 2.5 -- the `m = 2` singular-locus computation -- is a *different
   argument* from Thm 2.7, not a special case of it.  It uses the union
   criterion `#(z_1 u z_2) <= n-h-2`, which is what makes it char-free.  That
   observation is the seed of the repair at 20:40.

### 2026-08-20T20:10Z -- charge 2: the `m = 4`, `p = 2` skeleton, step by step

Endpoint dictionary (charter notation).  `ell >= 2`; both endpoints:

```text
odd :  n = 2ell+1,  h = n - ell - 1 = ell  ,  h+1 = ell+1 = n - ell
even:  n = 2ell+2,  h = n - ell - 1 = ell+1, h+1 = ell+2 = n - ell
both:  t := n-h-1 = ell (odd) / ell (even) ... t = n-h-1,  s := n-h-2 = t-1
       #I(f;h) = q^(h+1) = 2^(n-ell) = mu ,  D_e = sum_(f in I)[Lambda(f)-1]
       LHS of Thm 1.4  =  (1/q^n) sum_f D^m  =  E_e[D_e^m]   (exactly)
       M_m = 2^ell E_e[D_e^m]
m = 4, q = 2, dim X_(4,n,h) = n + 3(h+1) - 1,  R = 2n + 4(h+1) - 1 .
```

`1 <= h <= n-3` requires `ell >= 2` (odd) / `ell >= 1` (even): the endpoint is
inside Hast--Matei's hypotheses for every `ell` we care about.

| Step | Verdict at `m=4`, `p=2`, endpoint | Note |
|------|-----------------------------------|------|
| Lemma 2.2, Cor 2.4 | **SURVIVES** | char-free |
| Prop 2.5 (`m=2` locus) | **SURVIVES** | char-free; union criterion |
| Lemma 2.8, Prop 2.10 (irreducibility) | **SURVIVES** | BBSR 3.2 char-free, `h >= 1` holds |
| Lemma 2.6 | **REFUTED** | explicit `2^delta`-point families, 20:25 |
| Thm 2.7 (codim `2h+3`) | **NEEDS-WILD-SUBSTITUTE**, and the substitute is *available*: conditional on `2 delta <= h+1`, proof at 20:40 | this is the whole wild content |
| Thm 3.1 / [GL] | **SURVIVES** | char-free |
| Cor 3.3, Prop 3.5 | **SURVIVES given Thm 2.7** | no independent char use |
| Lemma 4.2 | **SURVIVES given Thm 2.7** | Grothendieck--Lefschetz is char-free |
| Thm 4.4, Cor 4.9/4.10 | **SURVIVES given Thm 2.7** | `Lambda` is of von Mangoldt type in every characteristic (Cor 4.9's proof is the `n`-cycle criterion, char-free) |
| The *constant* `C_(4,n,h)` | **UNKNOWN, and this is where the endpoint actually dies** | 21:00 |

Two structural remarks that belong in the skeleton, both char-free and both
new to this project's ledger.

**(B1) The centred moment is carried entirely by the sub-threshold cohomology.**
PROVED.  For `phi = Lambda - 1` the coefficients of Cor 4.10 are
`c_sigma = 1 - 1/n!` at one fixed `n`-cycle and `c_tau = -1/n!` elsewhere, so
`sum_(tau in S_n) c_tau = 0`.  In Theorem 4.4's computation the moment is

```text
E_e[D_e^4] = q^(h+1-n) sum_(sigma in S_n^4) (prod_i c_(i,sigma_i)) Lambda(sigma),
Lambda(sigma) := sum_r (-1)^r Tr(Frob_q . sigma^(-1) | H^r_c(Y_(4,n,h), Q_l)) .
```

Any part of `Lambda(sigma)` that is **independent of `sigma`** -- in particular
every degree in which `S_n^4` acts trivially, whatever that range is -- is
annihilated, because it factors out as `(sum_tau c_tau)^4 = 0`.  So the entire
fourth moment of `Lambda - 1` is the `S_n^4`-**non-trivial-isotypic** part of
the cohomology.  This holds in any characteristic and needs no theorem of the
paper.  It says precisely what Prop 3.5 is for: not to supply the answer, but
to certify that the annihilated part is everything above `R`, so that Deligne's
bound may be applied at `q^((R-1)/2)` instead of `q^(dim)`.

**(B2) Consequently the entire content of Theorem 1.4 at `m = 4` is a
weight-times-multiplicity budget.**  PROVED (bookkeeping).  Writing
`B` for the sum of the dimensions of the `S_n^4`-non-trivial-isotypic parts of
`H^r_c` below the threshold and `w` for the largest Frobenius weight occurring
there,

```text
E_e[D_e^4]  <=  (sum_sigma |prod_i c_(i,sigma_i)|) . q^(h+1-n) . B . q^(w/2)
            <=  16 . B . 2^(w/2 - ell)          (odd endpoint, q = 2).
```

The target (diary 04's `(W4-exact)` with `Pi_n = 1`) is
`E_e[D_e^4] < (mu-1)^4/2^ell = 2^(3(h+1)+1)(1-o(1))`, i.e.

```text
(BUDGET)     B . 2^(w/2)  <  2^(4ell+4) / 16  =  2^(4(h+1)-4) .
```

Tame Hast--Matei give `w <= R-1 = 2n+4(h+1)-2 = 8ell+4`, i.e. `2^(w/2) = 2^(4ell+2)`,
so `(BUDGET)` would need `B < 1/4`.  **The measured truth** (`M_4 ~ 12(ell-1)^2 2^(3ell)`,
diary 04) corresponds to `B . 2^(w/2) ~ 2^(3ell) poly(ell)`, i.e. an effective
weight `w ~ 6ell` against the a-priori `8ell+4`.  So the charter's exponential
slack `2^ell/poly` is, in cohomological coordinates, exactly a **weight drop of
`2ell` that the Hast--Matei architecture cannot see**, and `(BUDGET)` is
**failed by the tame theorem itself, by 2 to 4 bits, before any wild question is
asked**.  This is the single most important number in this file.

### 2026-08-20T20:25Z -- REFUTED: Lemma 2.6 at `p = 2`, with witness

The mechanism.  Over `k = Fbar_2` every monic `f` has a unique layer
decomposition `f = prod_(j>=0) C_j^(2^j)` with `C_j` monic of degree `c_j` and
`sum_j 2^j c_j = n` (`C_j` = product of the irreducible factors whose
multiplicity has bit `j` set; computable as: `C_0 = f/gcd(f,f')`, then recurse
on `sqrt(f/C_0)`).  Perturbing one layer, `C_j -> C_j + u`, changes `f` by

```text
f_new - f  =  (f / C_j^(2^j)) . u^(2^j) ,      deg = n - 2^j (c_j - deg u) ,
```

because `(C_j + u)^(2^j) = C_j^(2^j) + u^(2^j)` in characteristic two.  So the
whole space `deg u <= c_j - 1 - floor(t/2^j)` -- affine of dimension
`c_j - floor(t/2^j)` -- **stays inside one short interval** `deg(f_new - f) <= h`.
This is the Frobenius-square proper-power mechanism the lane already classified
(status `52-gf2-lemire.md`, commit `531ed174a`) seen from the moduli side.

Define, at the parameters Thm 2.7 actually uses (`s = n-h-2`, `t = n-h-1`),

```text
delta(n,h)  :=  max_(w in A^n)  dim { x in A^n : #{x_1..x_n} <= s,
                                      e_j(x) = e_j(w) for 1 <= j <= t } .
```

Lemma 2.6 asserts `delta = 0`.  **REFUTED at `p = 2`.**  Witness family: take a
frozen part `G` (a power of one linear polynomial, so one distinct root) and one
moving layer, `f = G . C^(2^j)`; then `deg G + 2^j deg u <= h` keeps the family
in one interval, and `#distinct roots <= 1 + deg C <= s` keeps it in `T_s`.
Optimising the profile gives, at **both** endpoints,

```text
delta(n,h)  >=  ceil(ell/2) - 2      (measured for ell = 6..20; = 1 already at ell = 3).
```

Machine verification, `acb_whm_strata witness <ell>` (every claim checked by
direct polynomial computation over `F_2`, not asserted):

| ell | n | h | s | profile `(c_j)` | moving layer | family dim | members | left interval | max distinct roots | budget |
|-----|---|---|---|-----------------|--------------|-----------|---------|---------------|--------------------|--------|
| 3 | 7 | 3 | 2 | (3,0,1) | j=2 | 1 | 2 | 0 | 2 | 2 |
| 4 | 9 | 4 | 3 | (1,0,2) | j=2 | 1 | 2 | 0 | 2 | 3 |
| 7 | 15 | 7 | 6 | (3,0,3) | j=2 | 2 | 4 | 0 | 4 | 6 |
| 9 | 19 | 9 | 8 | (5,7) | j=1 | 3 | 8 | 0 | 8 | 8 |
| 10 | 21 | 10 | 9 | (5,8) | j=1 | 3 | 8 | 0 | 9 | 9 |
| 12 | 25 | 12 | 11 | (5,10) | j=1 | 4 | 16 | 0 | 11 | 11 |
| 14 | 29 | 14 | 13 | (5,12) | j=1 | 5 | 32 | 0 | 13 | 13 |
| 16 | 33 | 16 | 15 | (5,14) | j=1 | 6 | 64 | 0 | 15 | 15 |

"left interval = 0" means every one of the `2^dim` members has the same top `t`
coefficients as the base point; "max distinct roots <= budget" means every
member is in `T_s`.  Lemma 2.6 says this set has dimension `0`; it has an
affine subspace of dimension `ceil(ell/2)-2` inside it.  **REFUTED.**

The same optimizer, run over general `p`, reproduces the tame case: it returns
`delta = 0` whenever `p > n` (as it must -- the layer construction needs
`p^j <= n`), and returns positive `delta` exactly for `p <= n`.

### 2026-08-20T20:35Z -- charge 3: the deviation is exactly on the classified strata, measured

`acb_whm_strata count <p> <n> <h>` enumerates **every** monic `f` of degree `n`
over `F_p`, computes its number of distinct roots in the algebraic closure (via
the radical, `rad(f) = w . rad(g)/gcd(w,rad(g))` with `w = f/gcd(f,f')`, and the
`p`-th-root branch when `f' = 0`), buckets by short interval, and reports the
largest bucket.  If Lemma 2.6 held, the largest bucket would be `O(1)`
independent of `p`; if it fails with excess `delta`, the largest bucket should
be `~ p^delta`.

Control series at the smallest interesting parameters, `n = 8`, `h = 4`
(`s = 2`, `t = 3`); `p = 11` is the first tame prime (`p > n`):

| `p` | tame? | predicted `delta` | predicted max bucket | **measured max bucket** | locus points |
|-----|-------|-------------------|----------------------|--------------------------|--------------|
| 2 | no | 2 | `2^2 = 4` | **4** | 10 |
| 3 | no | 0 | `O(1)` | **2** | 27 |
| 5 | no | 1 | `5^1 = 5` | **5** | 85 |
| 7 | no | 1 | `7^1 = 7` | **7** | 175 |
| 11 | **yes** | 0 | `O(1)` | (out of budget: `11^8` polynomials) | -- |

Four for four, including the non-monotone `p = 3` row (which has `delta = 0`
because `2 + 3.2 = 8` forces four distinct roots and `s = 2`), which no
"small field artefact" explanation reproduces.  Fully tame rows, where the
census is affordable, come out at exactly one point per interval:

```text
ACB_WHM|count|p=7 |n=5|h=2|s=1|t=2|locus_points=7 |max_bucket=1
ACB_WHM|count|p=11|n=6|h=3|s=1|t=2|locus_points=11|max_bucket=1
```

i.e. `dim = 0` with a single point, exactly Lemma 2.6.

Char-2 census across the endpoints (`acb_whm_strata sweep`), all `2^n` monic
polynomials enumerated, `n <= 24`:

| ell | n | h | s | predicted `delta` | max bucket | `log2` | dominant stratum profile of the max bucket |
|-----|---|---|---|-------------------|-----------|--------|--------------------------------------------|
| 7 | 15 | 7 | 6 | 2 | 7 | 2.81 | `(1,5,1)` |
| 8 | 17 | 8 | 7 | 2 | 8 | 3.00 | `(1,6,1)` |
| 9 | 19 | 9 | 8 | 3 | 16 | 4.00 | `(1,7,1)` |
| 9 | 20 | 10 | 8 | 3 | 22 | 4.46 | `(0,8,1)` |
| 10 | 21 | 10 | 9 | 3 | 16 | 4.00 | `(1,8,1)` |
| 11 | 23 | 11 | 10 | 4 | 30 | 4.91 | `(1,9,1)` |
| 11 | 24 | 12 | 10 | 4 | 44 | 5.46 | `(0,10,1)` |

The measured `F_2`-point count of the heaviest interval sits between `2^delta`
and `2^(delta+1.5)` -- as expected for a `delta`-dimensional family with a few
components -- and, decisively, **the dominant stratum of the heaviest interval
is in every single row the predicted profile shape** `(c_0, c_1, 1)`, i.e. one
`Frobenius-square` layer carrying almost all of the degree.  The wild excess is
concentrated exactly on the square proper-power strata the lane classified.
`F_2` point counts cannot by themselves certify a *dimension*; the dimension
claim is carried by the witness families above, which are proved affine spaces.

### 2026-08-20T20:40Z -- the repair: Theorem 2.7 in characteristic two

This is the positive result of the workstream.  Hast--Matei's Thm 2.7 bounds
`dim Sing` by the *necessary* condition "two of the `m` root tuples lie in
`T_(n-h-2)`", and that condition, combined with `dim(T n Z_w) = delta`, gives
`dim Sing <= (n-h-2) + delta + (m-2)(h+1)`, i.e. `codim = 2h+3-delta`.  The
necessary condition can be sharpened, char-free, and the sharpening is exactly
the "more refined reasoning" Remark 4.1 asks for.

**Lemma W (this workstream).  Let `k` be algebraically closed of any
characteristic, `m >= 3`, `n >= 4`, `1 <= h <= n-3`, `s = n-h-2`, and let
`delta = delta(n,h)` be as above.  Then**

```text
dim Sing(Y_(m,n,h))  <=  max{  s + (m-2)(h+1) ,   s + 2 delta + (m-3)(h+1)  } .
```

**In particular `codim Sing(X_(m,n,h)) >= 2h+3` whenever `2 delta <= h+1`, and
Theorem A, Corollary 3.3, Proposition 3.5, Lemma 4.2, Theorem 4.4 and
Theorem 1.4 all follow verbatim in that characteristic.**

*Proof.*  The rows of `J_(m,n,h)` are indexed by `(iota, j)`, `2 <= iota <= m`,
`1 <= j <= n-h-1`; row `(iota,j)` is `(row_j A_1)` in the `z_1`-columns and
`-(row_j A_iota)` in the `z_iota`-columns.  A dependency with coefficient
vectors `v_iota = (v_(iota,j))_j` satisfies

```text
v_iota^T A_iota = 0 for each iota ,       (sum_iota v_iota)^T A_1 = 0 .
```

Let `V = {iota : v_iota != 0}`, `u = sum_(iota in V) v_iota`.  For `iota in V`,
`A_iota` has a left kernel, so `#{z_iota} <= n-h-2` by **Cor 2.4** (char-free).
Three cases exhaust:

- `|V| = 1`, say `V = {iota}`.  Then `u = v_iota` annihilates both `A_1` and
  `A_iota`, so `v_iota` is in the left kernel of `[A_1 | A_iota]`; by the rank
  criterion in the proof of **Prop 2.5** (char-free) this forces
  `#(z_1 u z_iota) <= n-h-2`.
- `u = 0` and `|V| = 2`, say `V = {iota, iota'}`.  Then `v_iota` annihilates
  both `A_iota` and `A_(iota')`, so `#(z_iota u z_(iota')) <= n-h-2`.
- otherwise (`u != 0` with `|V| >= 2`, or `u = 0` with `|V| >= 3`): at least
  **three** of the `m` tuples lie in `T_(n-h-2)`.

In the first two cases some **pair** of tuples has root *union* of size `<= s`.
The locus of such pairs has dimension `<= s` in **any** characteristic: the
union is a point of the `s`-th symmetric power (dimension `s`) and each tuple is
then one of finitely many multiplicity assignments on that support.  The
remaining `m-2` coordinates are free in `Z_w`, of dimension `h+1` each: total
`s + (m-2)(h+1)`.  In the third case fix one tuple in `T_s` (dimension `s`); the
other two lie in `T_s n Z_w` for the common interval label `w`, of dimension
`<= delta` each; the remaining `m-3` are free in `Z_w`: total
`s + 2 delta + (m-3)(h+1)`.  Taking the max and subtracting from
`dim Y = n + (m-1)(h+1)` gives `codim >= 2h+3` when `2 delta <= h+1`.  QED

Status: **PROVED** modulo one routine point I did not write out in full, namely
that the union criterion of Prop 2.5 (`[A_1 | A_2]` drops rank iff
`#(z_1 u z_2) <= n-h-2`) applies verbatim to `[A_iota | A_(iota')]` for
`iota, iota' >= 2` -- it does, since the two blocks are structurally identical
and the defining equations force equal `e_j` for `j <= n-h-1` between any two
tuples, which is exactly what Prop 2.5's argument uses.  Call this **OPEN(bk)**,
bookkeeping-open, not mathematically open.

Note the tame case `delta = 0` recovers Hast--Matei's Thm 2.7 with a proof that
never mentions the characteristic, and never uses Lemma 2.6 at all.  Lemma 2.6
turns out to be avoidable, not merely repairable.

### 2026-08-20T20:50Z -- the published upper bound for `delta`, and the arithmetic of `2 delta <= h+1`

Sawin, arXiv:1809.05137, **Lemma 2.3**, verbatim from the fetched PDF:

> *"The locus `R` has dimension at most `floor(n/p) - floor(m/p)`, and `R n D`
> has dimension at most `floor(n/p) - floor(m/p) - 1`."*

with `R` the locus of `X_(n,m,c) = { (a_i) : prod (1 - u a_i) = 1 + c_1 u + ... +
c_m u^m mod u^(m+1) }` on which `#{a_1..a_n} <= m-1`.  Its proof is the same
mechanism found independently above: `z = 0` forces
`d/du prod(1-u a_i) = 0`, hence `prod (1-u a_i) in k[u^p]`, and the space of such
polynomials with the first `m` coefficients prescribed has dimension
`#{ m < i <= n : p | i } = floor(n/p) - floor(m/p)`.

**Dictionary.**  Sawin's `X_(n,m,c)` with `m = t = n-h-1` prescribed
coefficients is our `Z_w`, and his `R` (`<= m-1 = t-1 = s` distinct roots) is
our `T_s n Z_w`.  So Lemma 2.3 reads

```text
delta(n,h)  <=  floor(n/2) - floor(t/2)         (p = 2) ,
```

modulo one homogenization step (`R` is projective, the affine cone adds one);
the `+-1` matters below and is flagged.  Numerically, at our endpoints:

| endpoint | `t` | Sawin upper bound for `delta` | this file's lower bound | `h+1` | `2 delta <= h+1`? |
|----------|-----|-------------------------------|--------------------------|-------|-------------------|
| odd `n = 2ell+1` | `ell` | `ell - floor(ell/2) = ceil(ell/2)` | `ceil(ell/2) - 2` | `ell+1` | **yes**, both parities (equality at `ell` odd) |
| even `n = 2ell+2` | `ell` | `(ell+1) - floor(ell/2)` | `ceil(ell/2) - 2` | `ell+2` | **yes** for `ell` even; **short by 1** for `ell` odd |

Upper and lower bound differ by exactly `2`.  So:

- The wild hypothesis of Lemma W is **satisfied at the odd endpoint for every
  `ell`, from published literature alone**, and at the even endpoint for even
  `ell`.
- At the even endpoint with `ell` odd it is short by one unit, which the layer
  model of 20:25 supplies with two units to spare (the model's exhaustive
  optimum over layer profiles is `ceil(ell/2)-2` at both endpoints, and I
  believe it to be tight: an upper bound in the model needs only the generic
  independence of the non-vanishing truncated generators `(f/E_j) x^(2^j i)`,
  which have distinct degrees within each layer).  That is the one genuinely
  open technical point, and it is a one-lemma job.

### 2026-08-20T21:00Z -- the verdict: removing tameness buys nothing at `q = 2`

Now put `(BUDGET)` (20:10) together with the repair.  Suppose Lemma W's
hypothesis holds and Theorem 1.4 is available at `p = 2`, `m = 4`.  Then, at the
odd endpoint,

```text
E_e[D_e^4]  <=  (sum_sigma |prod c|) . (q-1) . B . q^((R-1)/2) . q^(h+1-n)
            <=  32 . B . 2^(3(h+1)-1)  =  16 B . 2^(3ell+3) ,
target                                  <   2^(3ell+4) ,
```

so `(T-weak)`/`(W4-exact)` at `q = 2` needs `C_(4,n,h) < 2`, i.e. `B < 1/8`,
where `B >= 1` is the multiplicity of the `S_n^4`-non-trivial sub-threshold
cohomology.  **The architecture misses by 3 to 5 bits with `B = 1`, and `B = 1`
is fantasy**: sweep-06 established that every available Betti technology (Katz
`3(k+2)^(n+m)`; the 2024 sharpening `2(N+1)^(2N+1)(d+1)^N`; Wan--Zhang; QST's
`b_n` recursion) is exponential in the ambient dimension, which here is `4n`.

So the honest arithmetic is:

```text
what Hast--Matei prove (tame)          : E[D^4] <= C_(4,n,h) 2^(3(h+1)) , C ineffective, n-dependent
what removing tameness would add        : nothing to the constant
what the endpoint needs                 : C < 2, uniformly in n
what is true (measured, diary 04)       : C ~ 1.5(ell-1)^2 2^(-ell)
```

Two further points that sharpen diary 02's translation and should be recorded
as corrections:

1. **Theorem 1.4 at fixed `q = 2` and growing `n` is vacuous as stated.**  Its
   constant `C_(m,n,h)` is allowed to depend on `n` and `h` and is never made
   explicit; Remark 4.1 says so verbatim ("all asymptotic notation has implicit
   constants that may depend on `m`, `n`, and `h`").  Our regime is the exact
   opposite of the paper's (`q -> infinity`, `n` fixed): we have `q = 2` fixed
   and `n = 2ell+1 -> infinity`.  Diary 02's line "`(T-weak)` at the odd endpoint
   is *exactly* Hast--Matei's Theorem 1.4 at `m = 4` with `C < 2`" is right about
   the *shape* and about the *arithmetic of the exponents*, and it must be read
   with "and with `C` uniform in `n`", which no theorem in the paper provides
   and which the paper's method cannot provide, since `C` is a Betti number of a
   variety in `P^(4n-1)`.
   **Therefore the blocker sentence in the board ("remove the tameness
   hypothesis `p > n` from Hast--Matei Thm 1.4 at `m = 4`") is not the right
   handoff sentence.**  Tameness is the smaller half, and this file largely
   removes it; the uniform constant is the whole problem.
2. **Remark 1.5's conjecture is confirmed at `q = 2`, `m = 4`, by our data.**
   Remark 1.5 expects the true order `q^(m(h+1)/2) = 2^(2(h+1))` rather than the
   proved `q^((m-1)(h+1))`.  Diary 04's exact `M_4 ~ 12(ell-1)^2 2^(3ell)` gives
   `E[D^4] ~ 12(ell-1)^2 2^(2ell) = poly(ell) . 2^(2(h+1)-2)`.  That is Remark
   1.5's conjectural order on the nose, at the *fixed small* `q` the remark does
   not discuss.  Worth recording: our lane has 40 rows of exact evidence for a
   published conjecture about a range "not yet computed".

### 2026-08-20T21:08Z -- the two routes are one route, and where the object lives

Sweep-06 identified the surviving target as `(PURITY)` for
`X_(n,ell,0) = { (a_i) : prod(1-u a_i) = 1 mod u^(ell+1) }`, an `h`-dimensional
complete intersection with an `S_n`-action, and named the missing input as a
twisted Milnor number for the wildly ramified `C_n`-action.  In the dictionary
of this file, **`X_(n,ell,0)` is `Z_w` at `w = 0`, the `m = 1` fibre of
Hast--Matei's `pi : Y_(m,n,h) -> M_n^m`**, and `Y_(4,n,h)` is (over the interval
base) the fourfold fibre power of it.  Remark 1.5's "nontrivial `S_n^m`-action
on cohomology in ranges not yet computed" and sweep-06's "long-cycle sector of
`H^*_c` is pure of weight `<= h`" are the same statement about the same sheaf,
one written for the fourfold power and one for the single fibre.  Diary 02's
consequence 3 ("routes A and C of the sweep synthesis are the same route") is
**confirmed at the level of the varieties, not merely by analogy**: the fibre
product presentation is explicit in Hast--Matei Prop 2.10's proof (`pi` is flat
with fibre `Z_w^(m-1)`).

Combining, the weight statement needed is a fourfold-power version of
`(PURITY)`, and the two workstreams' targets differ only by taking a fibre
power and by which group element is inserted.

### 2026-08-20T21:12Z -- comparison with workstream A's cell structure

Workstream A (`acb_cab_cells.rs`) indexes its cells `K_(a,b,c,d)` by the
**conductor order** of the four Hayes characters, `V_d = {1 + a_1 x + ... + a_d x^d}`.
A character of conductor dividing `x^(d+1)` is trivial on `V_d`, i.e. it is a
character of the *coarser* interval equivalence with `h' = n-d-1 >= h`.  On the
Hast--Matei side, the coarser interval is `X_(m,n,h')`, and the tower

```text
X_(m,n,h) --> X_(m,n,h+1) --> ... --> X_(m,n,n-3)
```

is exactly the chain of proper linear sections of codimension `m-1` under the
degree-`n-h-1` Veronese, along which Prop 3.5 runs its induction (via the
[GL, Thm 2.4] semi-regular-pair isomorphism
`H^r(X_(m,n,h)) ~ H^(r+2(m-1))(X_(m,n,h+1))(m-1)`).

**So A's cell index and the Hast--Matei `h`-tower are the same filtration, dual
to each other**: A's "order `d`" cell is the piece of the moment supported on
characters trivial on `V_d` but not on `V_(d-1)`, and the Hast--Matei tower step
`h' -> h'+1` is exactly the corresponding Gysin/section map.  Two consequences:

- **This unifies the workstreams' targets.**  A's `(CAB)` -- cellwise absolute
  bound, no cross-order cancellation -- is, in the geometric language, a bound
  on each graded piece of the tower filtration separately.  What Prop 3.5
  supplies for free is that above the threshold the filtration is the *trivial*
  one (projective-space cohomology, `S_n^m` acting trivially), which is exactly
  the part `(B1)` shows the centred moment annihilates.  A's cells are the
  sub-threshold graded pieces, one per conductor level.
- **A's "no cross-order cancellation needed" is the same virtue as sweep-06's
  "`Frob` and `c` never separated" is a vice**: A's decomposition is *along* the
  filtration Hast--Matei's induction respects, so a per-cell bound composes with
  the tower; a per-conjugacy-class bound (the refuted cyclic/Foulkes
  architecture) is not along any filtration and cannot.

I did not verify numerically that A's `K_(a,b,c,d)` equals a graded piece of the
tower filtration; that is the obvious next joint experiment
(`sum_(a,b,c,d <= D) K = ` the moment of the coarser interval at `h' = n-D-1`),
and it is a cheap one on the existing CAS reports.  **OPEN.**

### 2026-08-20T21:14Z -- what I did not do

- No proof that `delta <= ceil(ell/2)-2` (the layer-model upper bound).  Only
  the lower bound is proved, by witness.
- No independent re-derivation of Ghorpade--Lachaud Prop 3.3 or of Deligne's
  weight bound; both are used as cited, char-free, on the authors' word plus the
  absence of any characteristic hypothesis in their statements as quoted by
  Hast--Matei.
- The `p = 11` tame census at `n = 8` was not run (`11^8` polynomials exceeds the
  compute budget); the tame rows shown are `p = 7, n = 5` and `p = 11, n = 6`.
- No attempt on `(BUDGET)`, `(WK)`, `(PURITY)`, or the twisted Milnor number.
- `acb_whm_strata.rs` emits pedantic clippy warnings comparable to the other
  `acb_*` examples in this ad hoc project (28 for `acb_cab_cells.rs`, similar
  here); it is a read-only diagnostic outside the repository gates, as the
  charter allows.

---

## FINDINGS

### (a) The dependency table

Complete table at 19:55.  Summary of the answers to the charge's four candidate
tameness uses:

- **`S_n` monodromy of the generic polynomial: NOT USED.**  Hast--Matei's
  `S_n^m` is a geometric action on ordered roots, present in every
  characteristic.  This is why their method, unlike Bank--Bary-Soroker--Rosenzweig's
  or Sawin's, has no Galois-theoretic tameness need at all.
- **`A_n` vs `S_n` / square-discriminant strata: NOT USED.**
- **Burnside / char-0 representation theory: NOT USED.**  Point counting is
  Grothendieck--Lefschetz plus the char-free Lemma 3.4.
- **Lang--Weil / Weil constants: NOT USED.**  The constants are Betti numbers
  via [GL], char-free.
- **The whole tameness dependency is `Lemma 2.6`, used once, inside `Theorem 2.7`,
  at `(s,t) = (n-h-2, n-h-1)`, to conclude that `T_(n-h-2) n Z_w` is finite.**
  Confirmed against the authors' own Remark 4.1, and the one place a hidden
  hypothesis could have hidden (BBSR Lemma 3.2 inside the irreducibility proof)
  was checked first-hand and is char-free.

Lane facts that substitute, and where they enter:

| Lane fact | Where it enters |
|-----------|-----------------|
| Frobenius-square proper-power strata confinement (`531ed174a`) | *is* the layer decomposition `f = prod C_j^(2^j)` whose `j >= 1` layers carry the whole wild excess; the census confirms the heaviest interval's dominant stratum is always of that shape |
| Projective eigenline classification (`636f9da38`), unweighted Euler trace `1` (`ada2c4542`) | not needed for the wild singular-locus question; they belong to the *constant*, i.e. the localized-trace route, which is where the residual difficulty actually is |
| Exact long-cycle Euler-trace theorems | same |
| Sweep-06 `(BINOM)`, `(LOWER)` | properties of `Z_w = X_(n,ell,0)`, the `m = 1` fibre of the same family; they bound `B` from below, i.e. they are evidence *against* the Betti route, consistent with 21:00 |

### (b) The minimal wild statement that completes `m = 4`

Two statements, in charter notation, in dependency order.  Only the first is
"wild"; the second is what actually stands between the lane and the endpoint.

**(WILD-`delta`)  [the wild part; nearly proved]**

```text
For k = Fbar_2, n in {2ell+1, 2ell+2}, h = n-ell-1, s = n-h-2, t = n-h-1, put

  delta(n,h) = max_(w in A^n) dim { x in A^n : #{x_1..x_n} <= s ,
                                    e_j(x) = e_j(w) for 1 <= j <= t } .

Claim:   2 delta(n,h)  <=  h+1 .
```

Given (WILD-`delta`), **Lemma W** of 20:40 gives `codim Sing X_(4,n,h) = 2h+3`
at `p = 2`, hence Theorem A, Cor 3.3, Prop 3.5, Lemma 4.2, Thm 4.4 and
**Theorem 1.4 at `m = 4`, `q = 2`** with no tameness hypothesis.

Status: `delta >= ceil(ell/2)-2` **PROVED** (witness families, 20:25, machine
verified).  `delta <= floor(n/2) - floor(t/2)` **PUBLISHED** (Sawin Duke 2021,
Lemma 2.3, read first-hand), which yields (WILD-`delta`) outright at the odd
endpoint for every `ell` and at the even endpoint for even `ell`, and is short
by one unit at the even endpoint for odd `ell`.  The gap between the published
upper bound and this file's lower bound is exactly `2`.  **So the wild half of
the problem is closed at the odd endpoint and one small lemma from closed at the
even endpoint.**

**(HM4-2)  [what actually completes the endpoint; fully open]**

```text
With Y = Y_(4,n,h) over Fbar_2, c_sigma = 1 - 1/n! at one fixed n-cycle and
-1/n! elsewhere, and
   Lambda(sigma) = sum_r (-1)^r Tr(Frob_2 . sigma^(-1) | H^r_c(Y, Q_l)) ,

   | sum_(sigma in S_n^4) (prod_(i=1)^4 c_(sigma_i)) Lambda(sigma) |  <  2^(4(h+1)) .
```

Equivalently, in the budget form of (B2): the `S_n^4`-non-trivial-isotypic part
of `H^*_c(Y)` has `B . 2^(w/2) < 2^(4(h+1)-4)`.  The trivial bound on the left of
(HM4-2) is `#Y = 2^(n+3(h+1)) = 2^(5ell+4)`, so the required cancellation is a
factor `2^ell`, and the measured truth delivers `2^(2ell)/poly(ell)` -- the
charter's exponential slack, in cohomological coordinates.

(HM4-2) is Remark 1.5's `S_n^m`-action statement at `m = 4`, `q = 2`, and it is
the fourfold-fibre-power form of sweep-06's `(PURITY)`.

### (c) Tractability verdict: what is new mathematics and what is bookkeeping

**Bookkeeping (do it, it is cheap and it is real):**

1. Lemma W (20:40) -- a char-free replacement for Hast--Matei Thm 2.7 that never
   uses Lemma 2.6.  Half a page.  It generalises a published theorem and would
   be of interest to the authors independently of this lane.  One routine
   verification remains (OPEN(bk)).
2. The `delta` upper bound in the layer model, closing (WILD-`delta`) at the
   even endpoint for odd `ell`.  One lemma about the independence of the
   truncated generators `(f/E_j) x^(2^j i)`.
3. The `Z_w`/`X_(n,ell,0)` and `h`-tower/conductor dictionaries (21:08, 21:12).

**Genuinely new mathematics (and it is not the wild part):**

4. (HM4-2).  This is a weight statement for a singular complete intersection in
   `P^(4n-1)` in characteristic two, with a wildly ramified group action, at
   fixed `q = 2` and `n -> infinity`.  Sweep-06 searched for a technology that
   delivers it and found none: every effective Betti bound is exponential in the
   ambient dimension, and the two Sawin mechanisms are structurally unavailable
   (Young-quotient with no cyclic analogue; squarefree modulus).  Nothing in
   this file changes that verdict.

**Verdict.**  The workstream's own target -- "remove `p > n` from Hast--Matei
Thm 1.4 at `m = 4`" -- is **substantially achieved here**, and the discovery is
that **it does not matter**.  Even with tameness removed, Hast--Matei's theorem
at `q = 2` yields `E[D^4] <= 16 B . 2^(3(h+1))` against a target `2^(3(h+1)+1)`:
the architecture is 3 to 5 bits short before a single Betti number is counted,
and the Betti number is astronomically large.  The wild question was the visible
obstruction; the constant is the real one.  I would **retire the "wild
Hast--Matei" framing from the board** and replace it with (HM4-2)/`(PURITY)`,
which is the same target sweep-06 arrived at from the other side.

Priority recommendation: workstreams A (cellwise, conductor-graded) and C
(dichotomy) are now the strictly better bets, because they attack the constant
directly and in coordinates where the lane has exact data.  Workstream B's
residue is items 1-3 above -- worth landing, not worth continuing past.

### (d) Does it unify with workstream A?

**Yes, and precisely.**  A's cell index `(a,b,c,d)` is the conductor filtration
on the character side; the Hast--Matei tower
`X_(m,n,h) -> X_(m,n,h+1) -> ... -> X_(m,n,n-3)` is the same filtration on the
geometric side, and it is the filtration along which Prop 3.5's induction runs.
The part of the tower above the threshold is the trivial `S_n^m`-isotypic part,
which finding (B1) shows the *centred* fourth moment annihilates identically --
so A's cells are exactly the sub-threshold graded pieces, one per conductor
level, and `(CAB)`'s "no cross-order cancellation required" is the assertion
that a per-graded-piece bound suffices.  That is the same object (HM4-2) asks
about, decomposed rather than bounded whole.

Concrete joint experiment, cheap, not run here: check
`sum_(a,b,c,d <= D) mult . K_(a,b,c,d)` against the fourth moment of the coarser
interval `h' = n-D-1` computed directly.  If they agree row by row, the
identification is verified numerically and A's ladder inherits the Hast--Matei
tower's Gysin structure -- which would give A a recursion in `D`, the thing its
charge asks for ("an induction/recursion on cell order").

### Epistemic ledger for this file

**PROVED:** the dependency table (by reading the fetched proof); BBSR Lemma 3.2
is char-free; (B1) the centred moment is carried by the `S_n^4`-non-trivial
sub-threshold cohomology, in any characteristic; (B2) the budget form and its
arithmetic; Lemma W, modulo OPEN(bk); `delta >= ceil(ell/2)-2` at both
endpoints; the `Z_w = X_(n,ell,0)` and conductor/tower dictionaries.

**REFUTED (with witness):** Hast--Matei Lemma 2.6 at `p = 2` at the parameters
Theorem 2.7 uses -- machine-verified affine families of dimension
`ceil(ell/2)-2` inside a set the lemma calls zero-dimensional, at
`ell = 3,4,5,7,9,10,12,14,16`.  Also refuted: the reading of diary 02's
translation under which removing tameness would give `(T-weak)`; the constant is
`n`-dependent and ineffective in the paper, and the architecture misses at
`q = 2` by 3-5 bits regardless.

**OPEN:** (WILD-`delta`) at the even endpoint for odd `ell` (one unit);
`delta <= ceil(ell/2)-2` as an upper bound; OPEN(bk) in Lemma W; (HM4-2) and
everything downstream of it; the numerical A-tower identification.

**Data:** all tables above are exact integer counts from
`crates/axeyum-cas/examples/acb_whm_strata.rs` (`optimize`, `predict`, `count`,
`sweep`, `witness`), reproducible in under two seconds each; the largest census
enumerates `2^24` monic polynomials.

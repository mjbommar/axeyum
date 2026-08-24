# AC-Bridge workstream 01: literature review, hypercontractivity toward (GHC-W)

Workstream: comprehensive, verified literature review of hypercontractivity
relevant to a global-hypercontractivity-type inequality for the mixed-cyclic
Witt grading `prod_(i odd, i<=ell) Z/2^(k_i)`, `k_i = min{m : i 2^m > ell}`.

Date opened: 2026-08-20.
Charter: `00-charter.md` (notation `G_ell`, `D_e`, `S_chi`, `M_2`, `M_4`,
`K_4`, `R_0`, ladder L0..L4).
Parent finding under test: sweep diary
`../adhoc-blocker-sweep-2026-08-20/09-additive-combinatorics.md`, entry
2026-08-20T17:05 (weight-graded Efron--Stein hypercontractivity; required
per-unit-weight constant `C <= 2^1.636 = 3.11` under the uniform-mass model
versus the sharp two-point Bonami value `3`; risk (R2) explicitly says the
`Z/2^k` per-coordinate constant "must be read out of the literature, not
guessed").

**Project law observed here:** every reference below was fetched or searched
on the live web during this session and what it proves is recorded from the
fetched text. Nothing is cited from memory. Where a fetch failed or returned
only an abstract, the entry says so and the claim is marked UNVERIFIED.

## Log

### 2026-08-20 (open) -- required reading complete

Read `00-charter.md`, the full sweep diary 09, and `00-synthesis.md`.

The question this workstream must answer, stated precisely before searching,
so that the literature is judged against a fixed target rather than the other
way round:

```text
(GHC-W)  Let G = prod_(i in I) Z/2^(k_i) with uniform (Haar) measure,
         I = { i odd, i <= ell },  k_i = min{ m : i 2^m > ell },
         sum_i k_i = ell,  |I| = ceil(ell/2).
         Grade the dual Ghat by the WEIGHT  w(chi) = sum_(i in supp chi) k_i
         in {0,...,ell}   [note: NOT the number of nontrivial coordinates,
         and NOT a polynomial degree].
         Wanted: for f : G -> R with a globalness hypothesis expressible in
         the lane's already-computed cylinder data B_j(b),
              || f^(=w) ||_4  <=  C^(w/4) || f^(=w) ||_2
         with an ABSOLUTE constant C (independent of ell and of the k_i),
         C < 2^1.636 = 3.11..., under normalized counting measure.
```

Three features make this non-standard and are the search axes:
(1) coordinates are `Z/2^k` with *varying* `k`, not `Z/2`;
(2) the grading is a weighted Efron--Stein filtration, not a degree;
(3) the needed constant is per unit of WEIGHT, and the weight of a
    coordinate is `k_i = log_2 |Z/2^(k_i)|`.  That normalization is not
    innocent: the worst single-coordinate function (a delta) on a
    `2^k`-point uniform space has `||f||_4/||f||_2 = 2^(k/4)`, which is
    exactly `C^(w/4)` at `w = k` with `C = 2`.  So the coordinate-size
    blow-up is *exactly absorbed* by the weight normalization, and the
    threat to `C <= 3.11` is not coordinate size but LEVEL: multi-coordinate
    extremals in a fixed weight.  Establishing the sharp level-graded
    constant, for `Z/2` first and then for mixed `Z/2^k`, is the technical
    core of this review.

### 2026-08-20 -- KLLM read from the primary text (JAMS version), verbatim

Fetch route (recorded because the sweep failed here): the arXiv PDF and the
`ar5iv` HTML both produce unreliable extractions -- `ar5iv` gave me a
paraphrase of Definition 1.2 that I was able to *refute* against a worked
example before noticing it was the tool, not the theorem, that was wrong.
The reliable route was: fetch the AMS/author PDF, then `pdftotext` locally.

Reference (verified):
Peter Keevash, Noam Lifshitz, Eoin Long, Dor Minzer, *Hypercontractivity for
global functions and sharp thresholds*, **J. Amer. Math. Soc. 37 (2024),
no. 1, 245-279**, DOI 10.1090/jams/1027, electronically published
2023-07-18; preprint <https://arxiv.org/abs/1906.05568>; author copy
<https://people.maths.ox.ac.uk/keevash/papers/GlobalHypJournal.pdf>.
(Note: the sweep and the JAMS masthead disagree on the year -- the volume is
37 (2024) with the article posted July 2023. Cite as JAMS 37 (2024) 245-279.)

**Definition 1.1 (noise operator), verbatim.** "For x in {0,1}^n we define the
rho-correlated distribution N_rho(x) on {0,1}^n: a sample y ~ N_rho(x) is
obtained by, independently for each i, setting y_i = x_i with probability rho,
or otherwise (with probability 1-rho) we resample y_i with P(y_i = 1) = p."

**Definition 1.2 (generalised influences), verbatim.** "For f : {0,1}^n -> R
and S subset [n] we let (suppressing p in the notation)
`I_S(f) = E_{mu_p}[ ( sum_{x in {0,1}^S} (-1)^{|S|-|x|} f_{S->x} )^2 ]`.
We say f has beta-small generalised influences if `I_S[f] <= beta E[f^2]` for
all `S subset [n]`."

**Theorem 1.3, verbatim.** "Let p in (0,1/2]. Suppose f in L^2({0,1}^n, mu_p)
has beta-small generalised influences (for p). Then
`||T_{1/5} f||_4 <= beta^{1/4} ||f||_2`."

**Reading it correctly (this cost me an hour and is worth recording).**
`S = empty` is included in "for all S subset [n]", and `I_empty(f) = E[f^2]`,
so **`beta >= 1` always**. "beta-small" therefore means *bounded*, not
*tending to zero*. I first read `beta` as a small parameter and produced what
looked like a counterexample (the symmetric degree-`d` function
`f = sum_{|T|=d} chi_T` has `I_S(f)/E[f^2] = 4^{|S|} C(n-s,d-s)/C(n,d) -> 0`
for `s >= 1`, while `||f||_4/||f||_2 -> rho_d^{1/4} > 1` in the Gaussian
limit).  That "counterexample" only shows the `S = empty` term is load-bearing.
The genuine content is the *rate*: a dictator at small `p` has
`beta = 1/p`, matching the classical `rho = O(p^{1/4})` obstruction quoted in
the paper's own introduction, and a global function keeps `beta = O(1)` and so
enjoys `(4,2)`-hypercontractivity at the **constant** rate `rho = 1/5`.

**Consequence 1 (decisive for this project): KLLM is a small-`p` theorem, and
our measure is uniform.**  At `p = 1/2` Theorem 1.3 is strictly WEAKER than
classical Bonami: `rho = 1/5 < 1/sqrt(3)`, and `beta^{1/4} >= 1`. Globalness
buys exactly the thing we do not need. Our coordinates carry **Haar (uniform)
measure on `Z/2^(k_i)`**; there is no bias to repair. The sweep's route (b)
therefore mis-identifies the machine -- but, as the next entry shows, it
mis-identifies it in a way that makes the situation *better*, not worse.

**The general-product-space version, which IS about our objects.**
Section 7.2, verbatim: "(Omega, nu) = prod_{t=1}^n (Omega_t, nu_t). We assume
`p_t = min_{omega_t in Omega_t} nu_t(omega_t) in (0,1/2)` for each t...
generalised Laplacians `L_S` defined by composing `L_t` for all t in S, where
`L_t f = f - E_t f`, and the generalised influences
`I_S[f] = E[L_S[f]^2] prod_{i in S} sigma_i^{-2}`, where
`sigma_i^2 = p_i(1-p_i)`." The decomposition used is **explicitly the
Efron--Stein decomposition**: "`f^{=S} = sum_{J subset S} (-1)^{|S\J|} f^{subset J}`
... This decomposition is known as the Efron--Stein decomposition [23]", with
noise operator `T_rho[f] = sum_S rho^{|S|} f^{=S}`.

**Theorem 7.10, verbatim.** "Let f in L^2(Omega,nu), let q > 2 be an even
integer, and let `rho <= 1/(4 q^{1.5})`. Then
`||T_rho f||_q^q <= sum_{S subset [n]} sigma_S^{2-q} ||L_S[f]||_2^q`,"
where `sigma_S = prod_{i in S} sigma_i`.

**Consequence 2: Theorem 7.10 has exactly the right SHAPE for (GHC-W) and
exactly the wrong CONSTANT.**  Specialise to one Efron--Stein layer
`f = f^{=S}` (so `L_T f = f^{=S}` for `T subset S`, `0` otherwise), `q = 4`,
`Omega_i = Z/2^(k_i)` uniform (so `p_i = 2^(-k_i)`,
`sigma_i^2 = 2^(-k_i)(1 - 2^(-k_i))`):

```text
rho^(4|S|) ||f^(=S)||_4^4  <=  ( sum_{T subset S} sigma_T^(-2) ) ||f^(=S)||_2^4
      ||f^(=S)||_4  <=  rho^(-|S|) prod_{i in S} (1 + sigma_i^(-2))^(1/4) ||f^(=S)||_2
                    ~   32^(|S|) * 2^(w(S)/4) * ||f^(=S)||_2 ,   w(S) = sum_{i in S} k_i .
```

The `sigma_T^(2-q)` factor is **precisely the weight normalization the charter
asks for**: `sigma_i^(-2) ~ 2^(k_i)` makes the per-coordinate cost `2^(k_i/4)`,
i.e. `C = 2` per unit of Witt weight -- comfortably under the required `3.11`.
The killer is the universal noise floor `rho <= 1/(4 q^1.5) = 1/32` at `q=4`,
which is a constant **per coordinate** and not per unit weight:
`32^{|S|} = 32^{ceil(ell/2)} = 2^{2.5 ell}` at full support, against a total
allowance of `2^{ell/4}`. KLLM state plainly that they do not optimise it
("Theorem 7.1 is a qualitative generalisation of Theorem 3.4 (with smaller
rho, which we do not attempt to optimise)").

So the exact gap, in one sentence: **(GHC-W) is Theorem 7.10 with the
universal `rho <= 1/(4q^{1.5})` replaced by a per-coordinate
`rho_i <= rho_c(2^{k_i})` at (or near) the sharp hypercontractive threshold of
the uniform `2^{k_i}`-point space.** Every global-hypercontractivity paper in
this family is written for `|S| <= d = O(1)` applications, where
`const^{|S|}` is free; (GHC-W) needs `|S| ~ ell/2`, where it is fatal.

### 2026-08-20 -- charge item 1: the sharp constant for `Z/2^k` IS known, and it is exactly `2` per unit of Witt weight

Risk **(R2)** of the sweep ("the per-unit-weight constant for a `Z/2^k` factor
with `k >= 2` is not known to me to be 3 ... Must be read out of the
literature, not guessed") is fully answered by the literature, and the answer
is *sharp*, not just an estimate.

**Classical chain, verified.**
- Aline Bonami, *Etude des coefficients de Fourier des fonctions de L^p(G)*,
  Ann. Inst. Fourier (Grenoble) **20** (1970), fasc. 2, 335-402. (Note the
  title: `G` is a **compact abelian group**, so the classical source is already
  general-abelian, not cube-specific. Citation verified in the reference lists
  of both KLLM/JAMS and Ivanisvili--Tkocz.)
- Leonard Gross, *Logarithmic Sobolev inequalities*, Amer. J. Math. **97**
  (1975), no. 4, 1061-1083.
- William Beckner, *Inequalities in Fourier analysis*, Ann. of Math. (2)
  **102** (1975), no. 1, 159-182.

**The sharp two-point inequality** (O'Donnell, *Analysis of Boolean
Functions*, CUP 2014; arXiv edition <https://arxiv.org/abs/2105.10386>,
fetched and read locally, Chapter 10.1), verbatim: "Two-Point Inequality. Let
`1 <= p <= q <= infty` and let `0 <= rho <= sqrt((p-1)/(q-1))`. Then
`||T_rho f||_q <= ||f||_p` for any `f : {-1,1} -> R`." For `(p,q) = (2,4)`
this is `rho_c(2) = 1/sqrt(3)`.

**Tensorization**, verbatim (same source, Ch. 10.1): "**Hypercontractivity
Induction Theorem.** Let `0 <= rho <= 1`, `1 <= p,q <= infty`, and assume that
`||T_rho f||_q <= ||f||_p` holds for every `f in L^2(Omega_1,pi_1), ...,
L^2(Omega_n,pi_n)`. Then it also holds for every
`f in L^2(Omega_1 x ... x Omega_n, pi_1 (x) ... (x) pi_n)`."
Note it already allows **different factors**, but a **single** `rho`.

**The sharp constant for a general finite alphabet** (same source, Ch. 10.2),
verbatim:

> **Theorem 10.18.** Let `X` be a mean-zero discrete random variable and let
> `lambda < 1/2` be the least value of its probability mass function, as in
> Proposition 10.17. Then for `q > 2` it holds that `X` is
> `(2,q,rho)`-hypercontractive and `(q',2,rho)`-hypercontractive for
> `rho = sqrt( sinh(u/q) / sinh(u/q') )`, with `u` defined by
> `exp(-u) = lambda/(1-lambda)`.
> **This value of `rho` is optimal, even under the assumption that `X` is
> two-valued.**

Attribution given there: "the below theorem ... is due to Latala and
Oleszkiewicz [LO00]. The case of general discrete random variables is a
reduction to the two-valued case due to Wolff [Wol07]."
(R. Latala, K. Oleszkiewicz, *Between Sobolev and Poincare*, GAFA Seminar
Notes, Springer LNM 1745 (2000), 147-168; P. Wolff, *Hypercontractivity of
simple random variables*, Studia Math. **180** (2007), 219-236.)
And **Corollary 10.20**, verbatim: "Let `(Omega,pi)` be a finite probability
space, `|Omega| >= 2`, in which every outcome has probability at least
`lambda`. Let `f in L^2(Omega,pi)`. Then for any `q > 2` and
`0 <= rho <= (1/sqrt(q-1)) lambda^(1/q - 1/2)`, `||T_rho f||_q <= ||f||_2`."

**Specialize to our coordinate.** `Omega_i = Z/2^(k_i)` with Haar measure has
every atom of probability exactly `lambda = 2^(-k_i)`; the extremal function
(a point indicator minus its mean) attains that `lambda`, so Theorem 10.18 is
*attained*, not merely applicable. With `q = 4`, `q' = 4/3`,
`u = log(2^(k)-1)`:

```text
rho_c(2^k) = sqrt( sinh(u/4) / sinh(3u/4) ),      u = log(2^k - 1).
```

Evaluated (exact formula, `python3`; the `k = 1` row is the independent
two-point check and reproduces `1/sqrt(3) = 0.5773502...` to 6 places):

```text
 k      m   rho_c(m)   cost = 1/rho   C := cost^(4/k)  [= per-unit-WEIGHT constant]
 1      2   0.577350   1.732051       9.0000
 2      4   0.549699   1.819176       3.3094
 3      8   0.498524   2.005920       2.5298
 4     16   0.441460   2.265211       2.2652
 5     32   0.384975   2.597570       2.1461
 6     64   0.332168   3.010522       2.0849
 8    256   0.242312   4.126905       2.0315
12   4096   0.124027   8.062742       2.0052   -> C -> 2 as k -> infinity
```

Asymptotics of the exact formula: `sinh(u/4)/sinh(3u/4) -> e^(-u/2)`, so
`rho_c(2^k) ~ (2^k - 1)^(-1/4)` and the per-coordinate cost is `~ 2^(k/4)`,
i.e. **`C -> 2` exactly**. The Witt weight `k_i = log_2|Z/2^(k_i)|` is
therefore the *canonically correct* normalization: it absorbs the alphabet
blow-up exactly, with no room to spare and no degradation with `k`. Answering
the charge's question directly: **there is no degradation with `k`** -- in the
weight normalization the cyclic factors get *better* with `k`, monotonically
from `9` at `k=1` down to `2`.

An independent cross-check I ran before finding Theorem 10.18: direct
numerical maximization of `||T_rho f||_4/||f||_2` over `f in R^m` (coordinate
ascent, 25 restarts) gave `rho_c = 0.57737, 0.54970, 0.49852, 0.44146` for
`m = 2,4,8,16` against the formula's `0.577350, 0.549699, 0.498524, 0.441460`.
Agreement to ~2e-3 (optimizer floor). Recorded because it is the kind of
cross-check the project's Gotchas demand: the formula was *not* taken on trust.

**The log-Sobolev route gives the same answer and identifies the semigroup.**
Our per-coordinate semigroup (resample the coordinate) is exactly the
**Potts semigroup** = random walk on the complete graph. Verified from
Yuzhou Gu, Yury Polyanskiy, *Non-linear Log-Sobolev inequalities for the Potts
semigroup and applications to reconstruction problems*, Comm. Math. Phys.
(2023); <https://arxiv.org/abs/2005.05444>, fetched and read locally, which
states verbatim: "The Markov kernel is `K(x,y) = 1/(k-1) 1{x != y}`, where
`k = #X` ... Its stationary distribution `pi` is uniform on `X` and its
Dirichlet form is rescaled covariance: `E(f,g) = k/(k-1) Cov_pi(f,g)`", and
then: "Diaconis and Saloff-Coste [DSC96] computed the 2-log-Sobolev constant
`alpha_2 = (k-2) / ((k-1) log(k-1))`  (5)". Reference [DSC96] there is
P. Diaconis, L. Saloff-Coste, *Logarithmic Sobolev inequalities for finite
Markov chains*, Ann. Appl. Probab. **6** (1996), no. 3, 695-750
(<https://projecteuclid.org/journals/annals-of-applied-probability/volume-6/issue-3/Logarithmic-Sobolev-inequalities-for-finite-Markov-chains/10.1214/aoap/1034968224.full>,
abstract fetched; it advertises "the log-Sobolev constant of the complete
graph on n points" as one of its exactly computed examples).
They add: "the infimum ... is achieved at a function `f` where `f(1) = k-1`
and `f(i) = 1` for `i != 1`" -- i.e. the same delta-like extremal.
Converting to the resampling normalization (`E_resample = ((k-1)/k) E_DSC`,
so `alpha_res = (k-2)/(k log(k-1))`, `alpha_res(2) = 1/2` by the limit) and
using Gross, `rho >= 3^(-1/(4 alpha_res))`, gives `1.7321, 1.8285, 2.0393,
2.3397` for `k = 1,2,3,4` against the sharp `1.7321, 1.8192, 2.0059, 2.2652`.
So **the log-Sobolev route is within 3% of sharp here** -- worth recording
because it means nothing is to be gained by improving it.

**IMPORTANT CAVEAT, flagged as an open lemma.** The Induction Theorem quoted
above carries a **single** `rho` across the factors. Our factors have
*different* `k_i`, and using `rho = min_i rho_c(2^(k_i)) = rho_c(2^(max k_i))`
throws away everything (it charges every coordinate the largest alphabet's
price). The multi-parameter form
`|| T_(rho_1,...,rho_n) f ||_4 <= ||f||_2` with `rho_i <= rho_c(2^(k_i))`
is standard -- the induction in O'Donnell's Exercise 10.3 is
coordinate-by-coordinate and never uses that the `rho_i` agree -- but I did
**not** find it stated as such in a fetched source. Treat it as
**(L3-1) an explicit lemma to write out**, not as a citation.

### 2026-08-20 -- charge item 4/1: the LEVEL constant on a two-point factor is 9, not 3. This alone refutes (GHC-W) with an absolute constant.

The sweep compared its required `C <= 3.11` against "the *sharp*
Bonami/Khintchine constant at weight one on a two-point factor is exactly 3
(Whittle's identity ...)". That is the correct value **at weight one only**.
The graded inequality (GHC-W) has to hold at *every* weight with the *same*
`C`, and the level-`d` constant grows.

**Literature.** Ivanisvili--Tkocz, *Comparison of moments of Rademacher
chaoses*, <https://arxiv.org/abs/1807.04358> (PDF fetched, text extracted),
introduction verbatim: "One way of effortlessly obtaining such comparison
inequalities is by real hypercontractivity, which for `1 <= p <= q` gives
`C_{p,q,d} = ((q-1)/(p-1))^{d/2}` ... To the best of our knowledge, these are
in fact the best known values of constants `C_{p,q,d}` (except for `p = 2` and
`q` being an even integer, where combinatorial arguments give slightly better
results -- see [2] and Exercise 9.38 in [9]). The constant `((q-1)/(p-1))^{d/2}`
is moreover **asymptotically sharp** as `d` goes to infinity with
`2 < p < q` fixed (see [6]), in the sense that one cannot replace it by
`C^{d/2}` with `C < (q-1)/(p-1)` as `d -> infinity`."
Here [2] = Bonami 1970, [6] = L. Larsson-Cohn, *L^p-norms of Hermite
polynomials and an extremal problem on Wiener chaos*, Ark. Mat. **40** (2002),
no. 1, 133-144 (abstract fetched from Project Euclid, verbatim: "We establish
sharp asymptotics for the L^p-norm of Hermite polynomials and prove
convergence in distribution of suitably normalized Wick powers. The results
are combined with numerical integration to study an extremal problem on Wiener
chaos."), [9] = O'Donnell's book.

At `(p,q) = (2,4)` this is `C_{2,4,d} = 3^(d/2)`, i.e. in the project's
normalization `C^{d/4} = 3^{d/2}`, **`C = 9`**. The quoted sharpness statement
excludes `p = 2`, so I verified the `p=2` case directly on the classical
extremal family (the Wiener-chaos diagonal / Hermite polynomial, which is
exactly Larsson-Cohn's extremal problem). Using the classical linearization
`H_a H_b = sum_r C(a,r)C(b,r) r! H_{a+b-2r}`,
`rho_d := E[H_d^4]/(E[H_d^2])^2 = sum_{r=0}^d (C(d,r)^2 r!)^2 (2d-2r)! / (d!)^2`
(`python3`, exact integer arithmetic):

```text
 d      rho_d          C_level(d) = rho_d^(1/d)
 1      3              3.0000        <- the sweep's "sharp value 3"
 2      15             3.8730
 4      639            5.0278
 10     1.40668e8      6.5286
 30     5.79459e26     7.8001
 50     4.24093e45     8.1762        ->  9  (Larsson-Cohn asymptotics)
```

`d=1` reproduces Whittle exactly (`rho_1 = 3`), and `d=2` gives `rho_2 = 15`,
which is precisely the number O'Donnell's book flags in the same place
("if [f] is homogeneous of degree 2, then `E[f^4] <= 51 E[f^2]^2`.
(Exercise 9.38(a) improves this 51 to **15**.)") -- an independent
confirmation of the computation from a fetched source.

**Consequence, PROVED (given the classical CLT/Wiener-chaos limit).**
`G_ell` has `#{i : k_i = 1} ~ ell/4 -> infinity` two-point coordinates. Take
`f` = the normalized symmetric degree-`d` multilinear form on `d` of them
(`d = ell/4`); it is a **pure weight-`d`** function in the Witt grading, and
`||f^{=d}||_4 / ||f^{=d}||_2 -> rho_d^{1/4}`. Hence any valid
`||f^{=w}||_4 <= C^{w/4} ||f^{=w}||_2` forces `C >= rho_d^{1/d} -> 9`.

> **(GHC-W) with an absolute constant `C < 9` is FALSE.**  In particular
> `C <= 3.11` is false, by a factor that is not marginal: `9` versus `3.11`.

Note also what does *not* rescue it: this extremal `f` is a maximally
**global** function (fully symmetric, every generalized influence `O(d/n)`),
so no globalness hypothesis of the KLLM/Keller--Lifshitz--Marcus type excludes
it. Globalness repairs the *biased-measure* failure mode (deltas, dictators,
juntas); it does nothing about the *level* failure mode, which is what binds
here.

### 2026-08-20 -- the route-(b) arithmetic redone with the sharp constants (and two corrections to the sweep's model)

With the sharp per-coordinate constants in hand the sweep's route (b) can be
evaluated exactly rather than under a guessed `C`. Two corrections to the
sweep's own model surfaced on the way; both are recorded as findings for the
parent diary.

**Correction 1 (arithmetic).** The sweep writes "mass concentrated near
`w ~ 0.335 ell`", taking `0.335 ell` from its own line "expected number of
nontrivial coordinates ~ 0.335 ell". But `w` is the **weight**
`sum_(i in supp) k_i`, not the number of nontrivial coordinates. Under the
character-count (uniform-mass) model the weight of a uniformly random
character has mean `sum_i k_i (1 - 2^(-k_i)) = ell - sum_i k_i 2^(-k_i)`;
with the Witt profile (`#{k_i = j} = ell/2^(j+1)`) this is
`ell (1 - sum_j j 4^(-j)/2) = 0.7778 ell`, and the *binding* term of the
route's own bound sits at `w = 0.87 ell`. The two numbers differ by a factor
`2.6`, and the sweep evaluated the binding term at the wrong weight (it used
`w = ell` with `f_ell = 2^(-0.318 ell)`, which is a much smaller term than the
real maximum). This is what makes the sweep's threshold come out as the
gentle `3.11`.

**Correction 2 (the constant).** The sweep's `C` is a single number for all
weights. The truth is weight-and-support dependent, and the worst support
pattern of a given weight uses the *cheapest-`k`* coordinates first, because
per unit weight `k = 1` costs `9`, `k = 2` costs `3.31`, and large `k` costs
`2`. The correct object is
`B_w := max over supports S of weight w of prod_(i in S) rho_c(2^(k_i))^(-1)`,
computed by an exact knapsack DP over the `k_i` list.

**The exact evaluation** (`python3`, exact integer `N_w` from the generating
polynomial `prod_i (1 + (2^(k_i)-1) z^(k_i))`, `sum_w N_w = 2^ell` asserted;
`f_w = N_w / 2^ell` is the sweep's uniform-mass model; sufficient threshold
`R_0 <= 2^(ell + 2(n-ell)) / Sigma(ell)^2` from the sweep's (SLACK), odd
endpoint `n = 2 ell + 1`):

```text
 ell | log2 C_eff (full support) | log2(sum_w B_w sqrt(f_w))/ell | R_0 bound | sufficient | verdict
  20 |  1.8149   C_eff = 3.5184  |  0.4656                       | 2^37.2    | 2^5.3      | FAIL by 2^31.9
  50 |  1.8170   C_eff = 3.5235  |  0.4401                       | 2^88.0    | 2^29.7     | FAIL by 2^58.4
 100 |  1.8208   C_eff = 3.5329  |  0.4272                       | 2^170.9   | 2^75.5     | FAIL by 2^95.3
 200 |  1.8219   C_eff = 3.5355  |  0.4188                       | 2^335.0   | 2^171.5    | FAIL by 2^163.6
 400 |  1.8223   C_eff = 3.5363  |  0.4139                       | 2^662.2   | 2^367.5    | FAIL by 2^294.8
```

So the route misses by `2^(0.66 ell)`, and it is in fact **worse than the
trivial kurtosis bound `R_0 <= 2^ell`** (from `M_4 <= M_2^2`) by `2^(0.66 ell)`.
It is not a knife edge; it is a rout.

**Where the budget goes, and why no repair inside this architecture works.**
The sweep's allowance is `log2 C_eff <= 1.636`. The Witt weight fractions are
`j/2^(j+1)` for `k_i = j`:

```text
 k=1: weight fraction 1/4,   C = 9      -> uses 0.7925 of 1.636
 k=2: weight fraction 1/4,   C = 3.309  -> uses 0.4306   (running 1.2231)
 remaining weight fraction 1/2 would need C <= 2^0.826 = 1.773,
 but C >= 2 for EVERY coordinate (Latala-Oleszkiewicz/Wolff floor). IMPOSSIBLE.
```

That is a *structural* impossibility, independent of the mass model: the
two-point and `Z/4` blocks of the Witt grading -- which together carry half
the weight -- consume more than the entire budget by themselves, and the
remaining half cannot be bought below the universal floor `C = 2`.

**A third, more general obstruction: layer count.** Any bound of the shape
`||D||_4 <= sum_layers A_layer ||D^(=layer)||_2` pays the triangle inequality
once per layer. Graded by *support set* `S` there are `2^(ceil(ell/2))` layers
and the exact model value is
`B = 2^(-ell/2) prod_i (1 + cost_i sqrt(2^(k_i)-1))`, giving
`R_0 <= 2^(2.15 ell)` -- catastrophic. Graded by *weight* there are only
`ell+1` layers, which is why weight-grading is the right coarseness at all;
but then the per-layer constant must be the worst support pattern of that
weight, which is the computation above. Even the completely elementary
`||f^(=w)||_4 <= N_w^(1/4) ||f^(=w)||_2` (from
`||f||_4^4 = ||fhat * fhat||_2^2 <= ||fhat||_1^2 ||fhat||_2^2`) reproduces
exactly the trivial `R_0 <= 2^ell * poly(ell)` and no better -- consistent
with `sum_w N_w = 2^ell`.

**Scale mismatch, which I regard as the real lesson.** The sweep's own
(SLACK) analysis says the endpoint needs
`R_0 <= 2^(ell+2)/(ell-2)^4` -- a `poly(ell)` improvement over the trivial
`R_0 <= 2^ell`. Hypercontractivity is an instrument whose gains and losses are
`c^ell`. Applied here it loses `2^(0.66 ell)` where a gain of `ell^4` is
wanted. Even a *perfect* hypercontractive inequality with `C = 2` at every
weight would give `log2 C_eff = 1`, i.e. `R_0 <= 2^{ell} * 2^{-...}` only if
the mass profile cooperated; the instrument's precision is exponential and the
target's precision is polynomial. **A route that must win by `poly(ell)`
should not be built out of a tool that is only accurate to `exp(Theta(ell))`.**

### 2026-08-20 -- charge item 2: the global-hypercontractivity family, mapped

All of the following were confirmed by fetching the arXiv metadata/abstract
(arXiv API `export.arxiv.org/api/query`) or the full text; none from memory.

1. **Keevash--Lifshitz--Long--Minzer**, JAMS 37 (2024) 245-279,
   <https://arxiv.org/abs/1906.05568>. Theorem 1.3 (`rho = 1/5`, cube),
   Theorem 7.1 (`rho < 1/(2q^1.5)`, general independent `Z_i` with
   `E|Z_i|^q <= sigma^(2-q)`), Theorem 7.10 (`rho <= 1/(4q^1.5)`, general
   discrete product spaces via the **Efron--Stein** decomposition). All quoted
   verbatim above. Companion/extended version: **Keevash--Lifshitz--Long--Minzer**,
   *Global hypercontractivity and its applications*,
   <https://arxiv.org/abs/2103.04604> (abstract fetched; same inequality,
   applications to Turan numbers of hypergraph expansions, Huang--Loh--Sudakov
   and Furedi--Jiang--Seiver conjectures).
2. **Keller--Lifshitz--Marcus**, *Sharp Hypercontractivity for Global
   Functions*, <https://arxiv.org/abs/2307.01356> (v2, 25 Nov 2025; PDF
   fetched and read). Verbatim, **Theorem 1.3**: "Let `q >= 2` and let
   `(Omega,mu)` be a finite probability space. Let `f : (Omega^n, mu^n) -> R`,
   and assume that `||f_{S->x}||_2 <= r^{|S|} ||f||_2` for all `S subset [n]`
   and for all `x in Omega^S`. If `r >= 1` and `rho <= log q/(32 r q)`, then
   `||T_rho f||_q <= ||f||_2`." And **Theorem 1.4** (sharp level-`d`): for
   `f : (Omega^n,mu^n) -> {0,1}` with `E[f_{S->x}] <= r^{|S|} E[f]` for all
   `|S| <= d <= (1/4)log(1/E[f])`,
   `||f^{=d}||_2^2 <= E[f]^2 (C r^2 log(1/E[f]) / d)^d`.
   Note the globalness here is **restriction-based** (`L^2`/`L^1` norms of
   restrictions), not derivative-based; Section 4 of that paper converts
   between the two.
   *Sharpness is in `q`, not in the absolute constant*: the paper is explicit
   that the new phenomenon is Poisson-type growth `||X||_q = Theta(q/log q)
   ||X||_2` replacing the Gaussian `Theta(sqrt q)`, and Theorem 1.3 "is sharp
   for functions of general degree" in that sense. At `q = 4` its noise floor
   is `log 4/(128 r) ~ 0.0108/r`, i.e. **worse** than KLLM's `1/32` and far
   worse than the classical `1/sqrt 3`.
   Directly relevant remark, verbatim: "This tightness example for the
   classical level-d inequality (i.e., Theorem 1.1) can be lifted to a
   tightness example for Theorem 1.4 with respect to an arbitrary uniform
   product space `(Z/mZ)^n`, with `m` even, by applying `f` to the input
   modulo 2." -- i.e. on our very domain the tight example is a **junta**
   (`AND_t`), a local function, confirming that the theorems in this family
   are calibrated against locality, not against level.
3. **O'Donnell--Zhao** -- an independent global hypercontractivity under "a
   somewhat different notion of globalness", used for near-perfect expansion
   of pseudorandom sets (cited as [60] in Keller--Lifshitz--Marcus; not
   separately fetched, so recorded as a pointer only).
4. **Filmus--Kindler--Lifshitz--Minzer**, *Hypercontractivity on the symmetric
   group*, <https://arxiv.org/abs/2009.05503> (abstract fetched verbatim):
   hypercontractivity on `S_n`, "one of the most basic non-product domains",
   effective for functions "whose 2-norm remains small when restricting `O(1)`
   coordinates"; yields a level-`d` inequality analogue, KKL/small-set
   expansion on the transposition Cayley graph, and multi-slice results.
   Reduction to `[n]^n` is **lossy**.
5. **Keevash--Lifshitz**, *Sharp hypercontractivity for symmetric groups and
   its applications*, <https://arxiv.org/abs/2307.15030>: makes the reduction
   "essentially lossless"; their Theorem 1.10 (quoted through
   Keller--Lifshitz--Marcus Theorem 1.8) has the same
   `rho <= log q/(32 r q)` shape.
6. **Ellis--Kindler--Lifshitz**, *An analogue of Bonami's Lemma for functions
   on spaces of linear maps, and 2-2 Games*, <https://arxiv.org/abs/2209.04243>
   (abstract fetched). The nearest thing in the family to "large alphabet over
   a finite field": `L(V,W)` for `V,W` vector spaces over `F_q`. Also
   globalness-conditioned.
7. **Gur--Lifshitz--Liu**, *Hypercontractivity on High Dimensional Expanders:
   Approximate Efron--Stein Decompositions for eps-Product Spaces*,
   <https://arxiv.org/abs/2111.09375> (abstract fetched). Relevant
   methodologically: it is the paper that builds an *approximate* Efron--Stein
   decomposition where no exact product structure exists.

**What is product-structure-dependent, and what is not.** KLLM Theorem 7.10
needs only: (i) an exact Efron--Stein decomposition, (ii) per-coordinate
`sigma_i^2 = p_i(1-p_i)`, (iii) the encoding step (Proposition 7.11) replacing
`f^{=S}` by `||f^{=S}||_2 chi_S` with independent `chi_i` of matching moments.
Steps (i) and (iii) are where product structure is used; the `S_n` and HDX
papers replace (i) by approximate/coupled versions and pay for it. **For
`G_ell` none of this is needed: `G_ell` is an honest finite abelian product
group and its Efron--Stein decomposition is exact and is the Witt grading.**
This is a genuine structural advantage of our object -- and it is precisely
why the *global* theorems are the wrong ones: their difficulty is our
free hypothesis.

### 2026-08-20 -- charge item 3: level-`d` / level-1 inequalities and Chang's lemma

Verified via arXiv (metadata + abstracts fetched):
- **Chang's lemma** (the level-1 inequality on finite abelian groups). Modern
  proofs and sharp forms: Impagliazzo--Moore--Russell, *An Entropic Proof of
  Chang's Inequality*, <https://arxiv.org/abs/1205.0263> ("an elementary proof
  using entropy ... with tight constants"); Hambardzumyan--Li, *Chang's lemma
  via Pinsker's inequality*, <https://arxiv.org/abs/2005.10830>; J. R. Lee,
  *Covering the large spectrum and generalized Riesz products*,
  <https://arxiv.org/abs/1508.07109> (relates Bloom's variants to Roth's
  theorem); Chakraborty--Mande--Mittal--Molli--Paraashar--Sanyal, *Tight
  Chang's-lemma-type bounds for Boolean functions*,
  <https://arxiv.org/abs/2012.02335>; Lei Yu, *On Average Distance, Level-1
  Fourier Weight, and Chang's Lemma*, <https://arxiv.org/abs/2504.02593>
  ("near-optimal bounds for large and small sets", strengthens
  Friedgut--Kalai--Naor, Hamming balls extremal in `F_2^n`);
  Carenini--Franchi, *A strengthening of Chang's lemma*,
  <https://arxiv.org/abs/2605.07916> (2026; for `F_p^n`, "characters outside
  the large spectrum subspace have small correlation with the set not only
  globally, but also on average over cosets ... a localized counting lemma
  applicable to arbitrary finite abelian groups").
- **Status on `prod Z/2^(k_i)`.** No paper found that states a level-`d`
  inequality for a *mixed-cyclic 2-group* grading. The general-alphabet
  statements available are (a) Keller--Lifshitz--Marcus Theorem 1.4 for
  `(Omega^n, mu^n)` -- identical factors, globalness required, constant
  `(Cr^2 log(1/E f)/d)^d`; (b) O'Donnell's Theorem 10.21 for a product with
  min-atom `lambda`, `||f||_q <= (sqrt(q-1) lambda^{1/q-1/2})^k ||f||_2` for
  degree `<= k` -- which for mixed `lambda_i` charges every coordinate the
  worst alphabet.
- **Applicability to us: nil, and for a stateable reason.** Every inequality
  in this family bounds low-level Fourier *mass of a bounded/indicator
  function in terms of its density*. Our `D_e` is not bounded and not an
  indicator; `E[D] = 0`, the interesting object is `E[D^4]/(E[D^2])^2`, and
  the mass is at the *top* of the grading, not the bottom. Level-`d`
  inequalities are sharpest exactly where our mass is not.

### 2026-08-20 -- charge item 4: martingale / Efron--Stein routes as a substitute for degree

- Our grading **is already an exact Efron--Stein decomposition** of a product
  probability space (KLLM Section 7.2 uses precisely that language and cites
  Efron--Stein [23]). So the "filtration rather than degree" worry in the
  charter is not an obstruction at all: the Efron--Stein layers of a finite
  abelian product group are its character layers grouped by support, and the
  Witt weight is a coarsening of that grading. Nothing needs to be invented to
  *state* (GHC-W).
- The genuinely martingale-flavoured technology in this area exists for
  **non-product** domains, where an exact decomposition is unavailable:
  Filmus--Kindler--Lifshitz--Minzer (`S_n`), Keevash--Lifshitz (sharp `S_n`),
  Gur--Lifshitz--Liu (approximate Efron--Stein for `eps`-product spaces on
  high-dimensional expanders). We do not need any of it.
- **Ivanisvili's programme** (Bellman-function / martingale proofs of sharp
  hypercontractivity) is the right pointer for *sharp constants*, not for
  gradings: Frank--Ivanisvili, <https://arxiv.org/abs/2101.06209>
  (hypercontractivity of the fractional-Laplacian semigroup on `S^n`);
  Ivanisvili--Kalantzopoulos, <https://arxiv.org/abs/2407.18053> and
  <https://arxiv.org/abs/2506.08494>; Huang--Ivanisvili,
  <https://arxiv.org/abs/2607.19769> (closing the remaining two-point cases of
  Weissler's conjecture on complex hypercontractivity, `2<p<q<infty`);
  Ivanisvili--Tkocz, <https://arxiv.org/abs/1807.04358> (complex
  hypercontractivity beats real for *low* moments `p <= 2`; their Theorem 1:
  `||h||_q <= max{(q-1)^{d/2}, (p-1)^{-d/2}} ||h||_p` for `d`-homogeneous
  `h`). **None of these improves the `(2,4)` case**: for `p = 2` the max in
  their Theorem 1 is `(q-1)^{d/2} = 3^{d/2}`, i.e. exactly Bonami, and the
  improvement they obtain is confined to `p < 2`.

### 2026-08-20 -- charge item 5: the number-theoretic intersection, and the ONE close structural match

The sweep concluded that "no such literature exists" for Sidonicity /
multiplicative energy of structured multiplicative sets via hypercontractivity.
I confirm that for the *energy* formulation, and I found one genuinely close
structural match on the *level-inequality* side, which the sweep did not have.

**Green--Sawhney, *Improved bounds for the Furstenberg--Sarkozy theorem*,
<https://arxiv.org/abs/2411.17448> (2024).** Read through
Keller--Lifshitz--Marcus Section 1.5.7, which states their main analytic tool
verbatim:

> **Theorem 1.14 ([26, Theorem 1.2]).** Set `C_0 := 2^13`. Let
> `alpha in (0,1/2)` and `n >= 1` with `alpha > 2 n^(-1/2)`. Let `Q` be a set
> of pairwise coprime positive integers with `max_{q in Q} q <=
> n^(1/(32 log(1/alpha)))`. Let `1 <= d <= 2^(-7) log(1/alpha)`. Let
> `f : [n] -> C` with `|f(x)| <= 1`. Then either
> `sum_{S subset Q, |S|=d} sum_{a mod prod_{q in S} q, q in S => q does not divide a}
>  |fhat(a / prod_{q in S} q)|^2  <=  alpha^2 n^2 (C_0 log(1/alpha)/d)^d`,
> or else for some `S subset Q` with `1 <= |S| <= 2 log(1/alpha)` and some
> `r in Z`, the average of `|f(x)|` on the progression
> `P = {x in [n] : x = r mod prod_{q in S} q}` is greater than `2^{|S|} alpha`.

Result obtained: `s(n) <= n exp(-c (log n)^{1/2})` for the maximal size of a
subset of `[n]` with no square difference -- a large improvement on
Bloom--Maynard's `n (log n)^{-c log log log n}`.

**Why this matters here.** Strip the number theory and this is a **level-`d`
inequality in the Efron--Stein grading of `prod_{q in Q} Z/q` with varying,
non-prime-power moduli**, where the layer `S` is the set of moduli whose
component is *nontrivial* (that is exactly what
"`q in S => q does not divide a`" encodes: `a/prod_S q` is an **exact
conductor** `prod_S q` frequency). Our `B_j(b)` cylinder data and our
exact-conductor layers are the same construction one level down. The
dichotomy form ("either the level inequality, or a density increment on a
short progression") is also exactly the shape a usable (GHC-W) would have to
take, because our `D` has no `a priori` globalness.
Two differences that stop it being importable as-is: (i) the moduli are
**pairwise coprime** and hence the group is a product of *distinct-prime*
cyclic groups, whereas ours are all `2`-power with a common prime; (ii) `f` is
`1`-bounded and the conclusion is in terms of `alpha = ` density, i.e. it is a
level-`d`-for-indicators statement -- again the wrong end of the grading for us.

Other genuine intersections found (recorded, none applicable):
- **Lifshitz--Marmor**, *Bounds for characters of the symmetric group: a
  hypercontractive approach*, <https://arxiv.org/abs/2308.08694>. Theorem 1.12
  (quoted in Keller--Lifshitz--Marcus as Theorem 1.13): for `lambda |- n` with
  `lambda_1 = n - d`,
  `||chi_lambda||_q <= chi_lambda(1) (C q d^d/(log q * n^d))^{d(1-2/q)}`.
  This is the closest thing in the literature to "an `L^q` bound on a family of
  characters proved by hypercontractivity", which is formally what our `M_4`
  target is -- but it is for `S_n` irreducible characters and the mechanism is
  the branching rule.
- **Keevash--Lifshitz**: Roth's theorem analogue for `S_n`
  (`mu(A) <= n^{-c log n}` for `xz = y^2`-free `A`), Bogolyubov analogue for
  `A_n`, diameter bounds.
- **Defant--Frerick--Ortega-Cerda--Ounaies--Seip**, *The Bohnenblust--Hille
  inequality for homogeneous polynomials is hypercontractive*,
  <https://arxiv.org/abs/0904.3540> -- a hypercontractivity/Sidon-constant
  intersection (Bohr radius `~ sqrt(log n / n)`, Sidon constants for Dirichlet
  series). Different notion of "Sidon" from ours; recorded only so the next
  reader does not re-find it and hope.

## FINDINGS

### (a) Map of the field

The literature splits into four layers, and it is worth being explicit about
which failure mode each layer repairs, because the sweep's route (b) picked
the layer that repairs a failure we do not have.

```text
L0  CLASSICAL (uniform / product, sharp).  Bonami 1970 (compact abelian G!),
    Gross 1975, Beckner 1975.  Two-Point Inequality rho_c = sqrt((p-1)/(q-1)).
    Sharp for ALL finite alphabets: Latala-Oleszkiewicz 2000 (two-valued),
    Wolff 2007 (general discrete), rho_c = sqrt(sinh(u/q)/sinh(u/q')),
    exp(-u) = lambda/(1-lambda), lambda = min atom.  Tensorizes.
    Log-Sobolev route to the same place: Gross + Diaconis-Saloff-Coste 1996
    (the Potts/complete-graph constant alpha_2 = (k-2)/((k-1)log(k-1))),
    refined by Gu-Polyanskiy 2020 (all p-NLSI).
    => The `Z/2^k with Haar measure' question in the charge is CLOSED here,
       sharply, with no k-degradation in the Witt normalization.

L1  LEVEL-GRADED SHARPNESS.  Bonami's exponent 3^(d/2) at (2,4); asymptotically
    sharp via the Hermite/Wiener-chaos diagonal (Larsson-Cohn 2002;
    Ivanisvili-Tkocz 2018 for the survey of best known constants; the exact
    level-2 value 15 is O'Donnell Ex. 9.38(a)).
    => per-unit-level constant is 9, not 3.  This layer is what kills (GHC-W).

L2  GLOBAL HYPERCONTRACTIVITY (biased / sparse measures).  KLLM JAMS 2024
    (Thm 1.3, 7.1, 7.10); KLLM `Global hypercontractivity and its
    applications' 2021; O'Donnell-Zhao; sharp version Keller-Lifshitz-Marcus
    2023/25 (Thm 1.3, sharp level-d Thm 1.4).
    Repairs: locality (dictators, juntas, deltas) under p = o(1).
    Does NOT repair: level growth; and is strictly weaker than L0 at uniform
    measure.

L3  NON-PRODUCT DOMAINS.  Filmus-Kindler-Lifshitz-Minzer (S_n),
    Keevash-Lifshitz (sharp S_n), Ellis-Kindler-Lifshitz (L(V,W) over F_q),
    Gur-Lifshitz-Liu (high-dimensional expanders, approximate Efron-Stein).
    Repairs: absence of an exact product/Efron-Stein structure.
    We have an exact one, so this layer is inapplicable by hypothesis.

APPLICATIONS TOUCHING NUMBER THEORY.  Green-Sawhney 2024 (Furstenberg-Sarkozy,
    s(n) <= n exp(-c sqrt(log n)), via a level-d inequality over prod_q Z/q
    for pairwise coprime q, in an exact-conductor layering);
    Lifshitz-Marmor (S_n character L^q bounds); Keevash-Lifshitz (Roth,
    Bogolyubov, diameter for S_n / A_n).
```

### (b) The exact gap between existing theorems and (GHC-W)

Three statements, in decreasing order of how badly they hurt.

**1. (GHC-W) as literally posed -- an absolute constant `C` valid at every
weight -- is FALSE, with `C >= 9 - o(1)`.**  PROVED here (modulo the classical
Wiener-chaos limit): `G_ell` has `~ell/4` coordinates with `k_i = 1`; the
symmetric degree-`d` multilinear form on `d` of them is a pure weight-`d`
element of the Witt grading with `||f^{=d}||_4/||f^{=d}||_2 -> rho_d^{1/4}`,
`rho_d^{1/d} -> 9`.  The required `C <= 3.11` is out by a factor `2.9`, not by
a margin.  No globalness hypothesis excludes this witness (it is the most
global function there is).

**2. The correct formulation -- per-coordinate constants -- is available,
sharp, and still insufficient by `2^(0.186 ell)` per unit weight.**
The right statement is not one `C` but
`||f^{=S}||_4 <= (prod_{i in S} rho_c(2^{k_i})^{-1}) ||f^{=S}||_2`, and the
`rho_c` are known exactly (Latala-Oleszkiewicz/Wolff).  Computed against the
sweep's own budget: the `k=1` block (weight fraction `1/4`, `C = 9`) plus the
`k=2` block (weight fraction `1/4`, `C = 3.309`) already consume
`0.7925 + 0.4306 = 1.2231` of the allowance `log2 C <= 1.636`, leaving the
remaining half of the weight a budget of `C <= 1.773`, below the universal
floor `C >= 2`.  Structurally impossible, independent of any mass model.
End-to-end, `log2 C_eff = 1.822` versus `1.636`, and with the uniform-mass
model the route yields `R_0 <= 2^(1.66 ell)` against a sufficient
`2^(ell + 2 - 4 log2 ell)` -- a shortfall of `2^(0.66 ell)`, i.e. **worse than
the trivial bound `R_0 <= 2^ell`**.

**3. The scale mismatch, which no sharpening can fix.**  The endpoint needs a
`poly(ell)` gain over the trivial kurtosis bound.  Every inequality in this
literature is accurate to `exp(Theta(ell))` on our parameters.  The gap
between (GHC-W) and what exists is therefore not one theorem: it is that the
target lives at a precision the instrument does not resolve.  A theorem of the
right *kind* would have to keep cross-layer cancellation (which the triangle
inequality over layers destroys), and there is nothing in this literature that
does that -- KLLM Theorem 7.10 and Keller--Lifshitz--Marcus Theorem 1.3 both
end in a **sum over layers of positive terms**.

Corollary for the parent diary: sweep 09's route (b) should be moved from
"the one live route in my field" to REFUTED-with-computation, and its risk
register re-read -- **(R2) is answered (the `Z/2^k` constant is `2` per unit
weight, better than feared), (R3) is fatal (not "affordable"), and (R1) is now
secondary** because even a perfect mass profile cannot buy back
`2^(0.186 ell)` per unit weight.

### (c) The most transferable techniques, and where each breaks

1. **Latala--Oleszkiewicz/Wolff sharp `lambda`-alphabet two-point inequality +
   the Hypercontractivity Induction Theorem.**  Fully transferable; gives the
   *best possible* graded inequality on `G_ell`.  *Breaks at*: the two-point
   coordinates (`C = 9`) and the universal floor `C >= 2`; and the induction
   is stated for a single `rho`, so the multi-parameter version has to be
   written out (small, see (d)/L3-1).
2. **The Green--Sawhney dichotomy shape** ("either a level-`d` inequality, or
   a density increment on a short progression"), over an exact-conductor
   layering of `prod_q Z/q`.  This is the closest existing theorem to what we
   would want, *and* it is a number-theoretic application, *and* its layering
   is our conductor filtration.  *Breaks at*: pairwise-coprime moduli (ours
   share the prime 2, so the "restrict a coordinate" operation is the
   Witt/conductor structure, not CRT); `1`-boundedness of `f`; and a
   conclusion phrased in the density of an indicator, i.e. the bottom of the
   grading, where our mass is not.
3. **KLLM Theorem 7.10's `sigma_S^(2-q)` weighting.**  The *shape* is exactly
   the Witt-weight normalization -- `sigma_i^(-2) ~ 2^(k_i)` gives `C = 2` per
   unit weight for free.  Transfer the weighting, not the theorem.
   *Breaks at*: the universal noise floor `rho <= 1/(4q^1.5)`, a constant per
   coordinate, which at `|S| ~ ell/2` costs `2^(2.5 ell)`.
4. **Restriction-based globalness (Keller--Lifshitz--Marcus Thm 1.3) fed by
   the lane's `B_j(b)` cylinder data.**  The hypothesis
   `||f_{S->x}||_2 <= r^{|S|}||f||_2` is *literally* a statement about the
   lane's cylinder masses, and the lane already computes them.  This is the
   one place where the lane has an input the literature wants.
   *Breaks at*: `rho <= log q/(32 r q)`, again per-coordinate; and the
   theorem is stated for `Omega^n` with identical factors.
5. **The Hermite/Wiener-chaos diagonal (Larsson-Cohn) as an obstruction
   generator.**  Transferable in the *negative* direction: it manufactures
   sharp counterexamples for any proposed graded inequality on the `k_i = 1`
   block.  Use it as a falsifier before investing in any new graded candidate.
   *Breaks at*: nothing -- it is a lower-bound machine, and it is why (b)(1)
   above is PROVED rather than merely computed.

### (d) Candidate inequality statements for the ladder (charter notation)

**(L3-1) [provable, small]  Multi-parameter sharp Efron--Stein
hypercontractivity for the Witt grading.**  For `G = G_ell = prod_(i in I)
Z/2^(k_i)` with Haar measure, `f in L^2(G)`, and any `S subset I`,

```text
|| f^(=S) ||_4  <=  ( prod_(i in S) rho_c(2^(k_i))^(-1) ) || f^(=S) ||_2 ,
rho_c(m) = sqrt( sinh(u/4) / sinh(3u/4) ),   u = log(m-1),
```

sharp in each coordinate.  Proof: Latala--Oleszkiewicz/Wolff per factor plus a
coordinate-by-coordinate induction (O'Donnell's Hypercontractivity Induction
Theorem run with distinct `rho_i`).  Status: **not yet written out**; it is the
one clean, certain, publishable-as-a-lemma item this review produces, and it
is the *best possible* statement of its kind.  It does **not** close (T-weak).

**(L2-1) [REFUTED here, record as refuted]**  `|| f^(=w) ||_4 <= C^(w/4)
|| f^(=w) ||_2` on `G_ell` with an absolute `C < 9`.  Witness: symmetric
degree-`d` forms on the `k_i = 1` coordinates, `d -> infinity`.

**(L2-2) [REFUTED under the uniform-mass model, `2^(0.66 ell)` short]**
`R_0 <= ( sum_w B_w sqrt(f_w) )^4` with `B_w` the sharp worst-support
constant.  Recorded so that no one re-derives it.

**(L2-3) [OPEN, and the one worth measuring]  Support-resolved mass profile.**
Define, for `S subset I`,
`f_S := ( sum_(chi : supp chi = S) |S_chi|^2 ) / P_2`.  Then the sharp
tensorized bound gives
`R_0 <= ( sum_S A_S sqrt(f_S) )^4`, `A_S = prod_(i in S) rho_c(2^(k_i))^(-1)`.
This is exact, needs no model, and is decided by one measurement (see below).
*Prediction to falsify*: the `k_i = 1` coordinates are the ones with
`i > ell/2`, i.e. the **top conductor levels**, and `|S_chi|^2` grows with
conductor; so the mass should concentrate on exactly the supports where `A_S`
is largest, making (L2-3) worse than the uniform-mass model, not better.  If
that prediction holds, the hypercontractivity family is closed for this lane.

**(L1-1) [PROVED, elementary; the reformulation I would land first]**
`(MIN)` is a *delocalization* statement, not a moment statement.  With
`p_e := D_e^2 / M_2` (a probability vector on `G_ell`) and
`PR := 1 / sum_e p_e^2 = M_2^2 / M_4` the Renyi-2 participation ratio,

```text
(MIN)  M_4 < 2^(4(n-ell))     <==>     PR  >  M_2^2 / 2^(4(n-ell)) .
```

With the ledger's proved Weil envelope `M_2 <= 2^(n-ell) Sigma(ell)` and the
odd endpoint `n = 2 ell + 1`, it is **sufficient** that

```text
PR  >  Sigma(ell)^2 / 2^(2(ell+1))   ~   (ell-1)^4 / 4 ,
```

and with the measured/Keating--Rudnick `M_2 ~ (ell-1) 2^n` it is
**equivalent** to `PR > (ell-1)^2 / 4`.  In words: *the endpoint follows as
soon as the squared class discrepancies are spread over more than about
`(ell-1)^2/4` of the `2^ell` classes* -- roughly `(n/2)^2/4` classes out of
`2^(n/2)`.  Checked against the CAS row `(9,19)`, exact integers
(`M_2 = 3339712`, `M_4 = 61277466352`, `M_2^2 = 11153676242944`):
`PR = 182.019...` against the true requirement `M_2^2/2^40 = 10.144...`;
passes with a factor `17.9`, and indeed `M_4/2^(4(n-ell)) = 0.05573` (which
is the sweep's own E4 number, independently reproduced).  The *envelope*
version is weaker: `Sigma(9)^2/2^20 = 649.95` (against the asymptotic
`(ell-1)^4/4 = 1024`), which `182` does not clear -- consistent with the
sweep's crossover at `ell = 15` for the envelope-based (SLACK) form.  So the
delocalization requirement is `PR > (ell-1)^2/4` on the measured second moment
and `PR > ~(ell-1)^4/4` on the proved Weil envelope; both are `poly(ell)`.  This is the honest shape of the target, and it explains why
hypercontractivity is the wrong instrument: a `(4,2)` norm inequality is a
statement about the *worst* concentration, whereas `(MIN)` only forbids
concentration onto fewer than `poly(ell)` classes.

**(L2-4) [OPEN, proposed replacement direction]  A cylinder-data
delocalization dichotomy in the Green--Sawhney shape.**  Either
`PR(D^2) > Sigma(ell)^2 2^(-2(ell+1))`, or there is a conductor level
`j <= ell` and a cylinder `b` with
`B_j(b) >= 2^j M_2 / 2^ell * (ell)^(c)` (an anomalous cylinder).  The second
alternative is exactly what the lane's `B_j(b)` data can be tested against,
and the lane has already computed it.  This keeps the useful half of the
global-hypercontractivity idea (the dichotomy against a locality witness) and
discards the half that costs `exp(Theta(ell))` (the graded norm inequality).

**Experiment that decides (L2-3), cheap, and it supersedes the sweep's E1.**
Emit, for `ell = 6..14` at both parities, the exact integer table of
`f_S` **resolved by support set** (not merely by weight `w`), and evaluate
`sum_S A_S sqrt(f_S)` with the `A_S` above; report it against
`2^(ell/4) * Sigma(ell)^(-1/2) * 2^((n-ell)/2)`.  Two integers per support
class; the `k_i` and `rho_c` tables are in this file.  Compare the outcome
with the uniform-mass value `2^(0.42 ell)` computed here.

### (e) References, ranked by importance to this project

1. **O'Donnell, *Analysis of Boolean Functions*, CUP 2014 / arXiv edition
   <https://arxiv.org/abs/2105.10386>, Chapter 10** -- Theorem 10.18
   (Latala--Oleszkiewicz/Wolff sharp `lambda`-alphabet constant), Corollary
   10.20, Theorem 10.21, the Hypercontractivity Induction Theorem, the
   Two-Point Inequality, Exercise 9.38(a).  *The single most useful document
   for us*: it closes charge item 1 sharply and supplies (L3-1).
2. **R. Latala, K. Oleszkiewicz**, *Between Sobolev and Poincare*, GAFA
   Seminar Notes, Springer LNM 1745 (2000), 147-168; and **P. Wolff**,
   *Hypercontractivity of simple random variables*, Studia Math. 180 (2007),
   219-236 -- the primary sources for the sharp constant.  (Reached through
   O'Donnell's attribution; primary texts not fetched -- flagged.)
3. **Keevash--Lifshitz--Long--Minzer**, JAMS 37 (2024) 245-279,
   <https://arxiv.org/abs/1906.05568> -- Theorem 7.10 and its
   `sigma_S^(2-q)` weighting: the right *shape*, the wrong *constant*.
4. **Green--Sawhney**, *Improved bounds for the Furstenberg--Sarkozy theorem*,
   <https://arxiv.org/abs/2411.17448> -- the nearest theorem in form and in
   application domain; the dichotomy template for (L2-4).
5. **Keller--Lifshitz--Marcus**, *Sharp Hypercontractivity for Global
   Functions*, <https://arxiv.org/abs/2307.01356> -- sharp-in-`q` global
   hypercontractivity and the sharp level-`d` inequality; also the explicit
   statement that on `(Z/mZ)^n` the tight example is a junta.
6. **L. Larsson-Cohn**, *L^p-norms of Hermite polynomials and an extremal
   problem on Wiener chaos*, Ark. Mat. 40 (2002), 133-144 -- the obstruction
   generator behind (b)(1).  Companion survey of best-known chaos constants:
   **Ivanisvili--Tkocz**, <https://arxiv.org/abs/1807.04358>.
7. **Diaconis--Saloff-Coste**, *Logarithmic Sobolev inequalities for finite
   Markov chains*, Ann. Appl. Probab. 6 (1996), 695-750 (complete-graph
   constant `alpha_2 = (k-2)/((k-1)log(k-1))`), as transmitted verbatim by
   **Gu--Polyanskiy**, <https://arxiv.org/abs/2005.05444> -- the log-Sobolev
   route; within 3% of sharp, so nothing to gain by improving it.
8. **Bonami** (Ann. Inst. Fourier 20 (1970) 335-402), **Gross** (Amer. J.
   Math. 97 (1975) 1061-1083), **Beckner** (Ann. of Math. 102 (1975) 159-182)
   -- the classical origin; note Bonami is already stated for a general
   compact abelian `G`.
9. **Filmus--Kindler--Lifshitz--Minzer** <https://arxiv.org/abs/2009.05503>,
   **Keevash--Lifshitz** <https://arxiv.org/abs/2307.15030>,
   **Gur--Lifshitz--Liu** <https://arxiv.org/abs/2111.09375>,
   **Ellis--Kindler--Lifshitz** <https://arxiv.org/abs/2209.04243> -- the
   non-product layer; inapplicable to us by hypothesis, listed so it is not
   re-searched.
10. **Lifshitz--Marmor** <https://arxiv.org/abs/2308.08694> -- `L^q` bounds on
    a family of characters proved by hypercontractivity; the only existing
    theorem whose *statement type* matches our `M_4` target.
11. Chang's-lemma family (level-1 on abelian groups): Impagliazzo--Moore--Russell
    <https://arxiv.org/abs/1205.0263>, Lee <https://arxiv.org/abs/1508.07109>,
    Yu <https://arxiv.org/abs/2504.02593>, Carenini--Franchi
    <https://arxiv.org/abs/2605.07916>.  Not applicable (indicator/density
    hypotheses, bottom-of-grading conclusions); listed to close the item.

### Epistemic ledger for this file

PROVED: the sharp per-coordinate constant `rho_c(2^k)` and its consequence
`C -> 2` per unit Witt weight (Latala--Oleszkiewicz/Wolff, quoted; plus my own
numerical confirmation to 2e-3); the refutation of (GHC-W) with an absolute
constant `C < 9` (Wiener-chaos diagonal, classical limit + exact Hermite
linearization arithmetic); the budget impossibility in (b)(2) (arithmetic on
the `k_i` profile and the sharp constants); (L1-1), the participation-ratio
reformulation of (MIN) (algebra plus the ledger's own `M_2` envelope).
PROVED-MODULO-MODEL (the sweep's uniform-mass model `f_w = N_w/2^ell`): the
`2^(0.66 ell)` shortfall of route (b) and the `2^(2.15 ell)` shortfall of the
support-set-graded variant.
CORRECTED IN THE PARENT DIARY: sweep 09 evaluates its binding term at
`w ~ 0.335 ell` (that number is the expected *number of nontrivial
coordinates*; the expected *weight* is `0.778 ell` and the binding weight is
`0.87 ell`), and compares against the level-1 constant `3` where the level
constant is `9`.
OPEN: (L2-3), (L2-4), and whether any dichotomy-shaped statement can retain
cross-layer cancellation.
UNVERIFIED / POINTERS ONLY (fetch failed or only abstract seen):
Latala--Oleszkiewicz and Wolff primary texts; Diaconis--Saloff-Coste primary
text (constant taken from Gu--Polyanskiy's verbatim quotation);
O'Donnell--Zhao; Green--Sawhney primary text (Theorem 1.2 taken from
Keller--Lifshitz--Marcus's verbatim quotation as their Theorem 1.14).
NO THEOREM CREDIT is claimed for the Lemire endpoint or for any lane lemma.

# 02 - Attack (B): better splitting functions at p = 2

Workstream 02 (NoH-p2). Date: 2026-08-20. Author lane: workstream 02.
Charge: 00-charter.md, attack (B). Coordinator corrections read from
10-notes-coordinator.md (Note 1, predictions P1/P3) before writing.

Labels used: **PROVED** (argument given here, or exact computation over an
exactly-represented field), **REFUTED (witness)** (a counterexample/measurement
is exhibited), **OPEN**. Every literature statement is quoted from a fetched
source with an arXiv id / version; nothing is recalled.

---

## VERDICT (up front)

**Attack (B) is DEAD, and the charter's premise for it is REFUTED.**

Three independent findings, each of which alone kills (B):

1. **There is no headroom.** The splitting function used by Kramer-Miller and
   by KMU is the Artin-Hasse one, and its coefficient-decay rate is already
   *exactly* the best any splitting function can have. Ceiling lemma (C1)
   below, plus the exact-radius statements in Kedlaya Thm 19.4.1, Pulita
   Prop 2.12, and Robba's necessity condition. Measured: the rate is attained,
   not merely bounded.
2. **The Lubin-Tate freedom is empty at p = 2 for this purpose.** Measured over
   four distinct Lubin-Tate series at level m = 1 and three at m = 0: the
   valuation profile of the splitting quotient is *bit-identical*. Pulita's
   own Thm 2.13 explains why - varying the series can only *destroy*
   overconvergence, never improve the rate. Negative control reproduces that
   theorem independently (below).
3. **`a(k) = floor((k-1)/3)` is not a splitting-function rate at all.** It is
   the weight exponent on a `U_p`-stable formal basis, and its denominator is
   the ramification index of the auxiliary *tame Belyi map* over the point 1
   (`p-1` for odd p; degenerate at p = 2, whence the fallback 3). Quoted from
   KMU I Prop 4.3 / Rem 6.5 and KM 1909.06905 Prop 4.4 in section 4 below.

So the p = 2 obstruction is **geometric/combinatorial (the auxiliary map and
the induced basis), not Dwork-analytic**. Effort should move to attacks (A),
(C), (D) and to finding a different auxiliary map or a different `U_p`-stable
basis. This is the no-go the charter asked for, and it is a clean one.

Coordinator prediction status: **P1 CONFIRMED** (exactly, with the equality set
measured). **P3 REFUTED (witness)** - there is no extra loss at Witt length
m >= 2; measured at m = 1, 2, 3, and confirmed by KMU II Lemma 3.5 / Thm 3.6,
which carry no parity hypothesis.

Also corrected: the charter's `pi^2 = -2` at p = 2 generates `Q_2(sqrt(-2))`,
which does **not** contain `zeta_4`. The order-4 splitting lives in
`Q_2(zeta_4) = Q_2(i)` with uniformizer `i - 1`, `(i-1)^2 = -2i`. Valuations
are unaffected (`v = 1/2` either way), so the charter's rate arithmetic
survives; the field statement does not.

---

## 1. Bibliography actually fetched

| what | id / url | note |
|---|---|---|
| Pulita, *Rank One Solvable p-adic Differential Equations ... via Lubin-Tate Groups* | **arXiv:math/0612725v2**, Math. Ann. 337 (2007) 489-555, DOI 10.1007/s00208-006-0040-8 | PDF **and** LaTeX source fetched |
| Kramer-Miller, *p-adic estimates of exponential sums on curves* | arXiv:1909.06905v2 | |
| Kramer-Miller, *p-adic estimates of abelian Artin L-functions on curves* | arXiv:2006.04936v2 | |
| Kramer-Miller-Upton I, *Newton Polygons of Sums on Curves I* | arXiv:2110.08656v1 | Remark 6.5 lives here |
| Kramer-Miller-Upton II, *...Variation in p-adic Families* | arXiv:2110.08657v1 | Thm 3.6 lives here |
| Kedlaya, *p-adic Differential Equations* (1st ed.) + errata | kskedlaya.org/papers/p-adic_differential_equations.pdf, /pde-errata.pdf | |

**The charter's arXiv guess `math/0602627` is wrong** - that id is
Nikiforov-Schelp, "Cycles and Stability" (math.CO). The correct id is
**math/0612725**.

**Not obtainable:** Matsuda, *Local indices of p-adic differential operators
corresponding to Artin-Schreier-Witt coverings*, Duke Math. J. **77**(3):607-625,
**1995** (DOI 10.1215/S0012-7094-95-07719-9) - Project Euclid has no online
version, paywalled. Every Matsuda statement below is therefore quoted
*secondhand* from Pulita or Kedlaya and is flagged as such. (Note the charter's
"1997" and "extensions" are both wrong: 1995, "coverings".) Christol-Mebkhout
I-IV originals likewise not fetched; Kedlaya Thm 12.6.4 / 19.4.1 is used as the
statement source, with Kedlaya's own citations recorded.

---

## 2. Pulita's replacement for the Dwork/Artin-Hasse exponential

**Lubin-Tate series** (arXiv:math/0612725v2, eq. 1.5.1, PDF p. 15):

> P(X) = w X (mod X^2 Z_p[[X]]),  P(X) = X^p (mod w Z_p[[X]]).

**The exponential** (Prop. 2.12, eq. 2.1.14, PDF p. 19), which is what replaces
`AH(pi x)`:

> E_m(T) := E([w_m], T) = exp(w_m T + w_{m-1} T^p/p + ... + w_0 T^{p^m}/p^m)
>
> "converges **exactly** in the disk |T| < 1, for all m >= 0, if and only if
> P(X) is a Lubin-Tate series, and w := (w_j)_{j>=0} is a generator of the
> Tate module T(G_P)."

(Here `w_j` is Pulita's `varpi_j`, an ASCII rendering.) The **pi-exponential**
(Def. 2.14, eq. 2.2.2, PDF p. 20):

> e_d(lambda, T) := E([pi_m] lambda, T^n)
>  = exp( pi_m phi_0 T^n + pi_{m-1} phi_1 T^{np}/p + ... + pi_0 phi_m T^d/p^m )
>
> "We will call e_d(lambda, T) in 1 + pi_m T B[[T]] the **pi-exponential**
> attached to lambda."

and the **splitting/theta function** (Def. 2.35, eq. 2.3.4, PDF p. 26):

> theta_d^{(phi)}(lambda, T) := e_d(phi(lambda), T^p) / e_d(lambda, T).

Relation to the classical objects (Intro 0.0.7, PDF p. 4; Rem 1.44, PDF p. 16):

> "If G_P is the formal multiplicative group Ghat_m, that is if
> P(X) = (X+1)^p - 1, then we recover **Matsuda's** exponentials (0.0.3). On the
> other hand, if P(X) = pX + X^p, we recover, for m = 0, **Dwork's** exponential.
> Observe that, in the case considered by Dwork, the formal group G_P is
> isomorphic, but not equal, to Ghat_m."

**Note for p = 2 specifically:** `(X+1)^2 - 1 = 2X + X^2`, so at p = 2 Dwork's
`pX + X^p` and Matsuda's `(X+1)^p - 1` are *literally the same series*. The
"choice of Lubin-Tate group" that exists at odd p collapses at p = 2 for the
two classical choices.

### 2.1 Torsion valuations - the structural no-go

arXiv:math/0612725v2, section 1.5.1, PDF p. 16 (`omega := |p|^{1/(p-1)}`,
section 1.1, PDF p. 7):

> "The Newton polygon of P shows that P has exactly p - 1 non trivial zeros of
> value omega = |p|^{1/(p-1)}, and inductively P(X) - pi_{j-1} has p zeros of
> valuation omega^{1/p^j}. **Hence |pi_j| = omega^{1/p^j}, for all j >= 0**, and
> the Galois extension Q_p(Lambda_{P,m}) = Q_p(pi_{m-1}) is totally ramified."

i.e. `v_p(pi_j) = 1/(p^j (p-1))`, **for every Lubin-Tate series P**. The
statement is uniform in P: the choice of P cannot move a single torsion
valuation. Cross-checked against KM 2006.04936v2 section 5.2.2:

> "Note that **v_p(gamma_i) = 1/(p^{i-1}(p-1))**."

and KM 1909.06905v2 section 5.3: "**v_p(gamma) = 1/(p-1)**".

### 2.2 Is p = 2 included? Yes.

Exhaustive grep of Pulita's LaTeX source for `p=2`, `p>2`, `p\neq 2`, `p\geq 3`,
"odd" returns **six** hits. Standing hypothesis (section 1.1, PDF p. 7) is only
*"Let p > 0 be a fixed prime number."* Of the six hits, four are about *prior
literature* and two are about a *result* where p = 2 genuinely differs:

- Intro 0.0.4, PDF p. 3, about **Matsuda**, not Pulita:
  > "Matsuda proves also that, **if p != 2**, then the exponential
  > E_m(T^{-p})/E_m(T^{-1}) is over-convergent. He obtains these results by a
  > quite complicates, but elementary, **explicit estimation of the valuation of
  > the coefficients** of this exponential."
- Cor. 4.31, eq. (4.3.13), PDF p. 46 - a *conclusion*, not an assumption:
  > Pic^sol(R_K) = { Z_p/Z **if p > 2** ; Z_p/Z (+) k((t))/(Fbar - 1)k((t))
  > **if p = 2** }
- Proof of Cor. 4.31, PDF p. 46 - the unique point where p = 2 is exceptional:
  > "which easily gives |lambda_{...,j}| <= |p|^j |pi_{m-j}|^{-1} < 1. This last
  > is <= 1, and **is = 1 if and only if p = 2, and m(n) = j = 0**."
- Remark before Thm 4.57, PDF p. 50 - again about [Ma], [Crew], [Tsu].

**Thm 2.13 / 2.21 / 2.28 / 3.4 / 4.57 carry no parity hypothesis.** Independent
confirmation from Kedlaya, Example 17.1.5, p. 293:

> "it was shown **for p > 2 by Matsuda** [169] by an explicit calculation, and
> **for all p by Pulita** [185] as part of a much broader result."

So: **Pulita's construction includes p = 2, and its entire point (relative to
Matsuda) is that it removes the p != 2 restriction.** Attack (B) was premised
on Pulita offering a *better* p = 2 rate; what Pulita actually offers is
*existence* at p = 2, which Matsuda's elementary route could not reach. That
gap was closed in 2007.

### 2.3 Pulita's coefficient bounds - what is and is not there

**There is no theorem in the paper of the form `v(a_k) >= f(k)`.** The
coefficient control is entirely the membership statement, Prop. 2.15,
eq. (2.2.3), PDF p. 20:

> "The map lambda -> e_d(lambda, T) defines a group morphism
> W_m(B) --> 1 + pi_m T B[[T]]."

i.e. a *flat* bound `v(coeff) >= v(pi_m)` for every degree, used as such at
eq. (2.3.7), PDF p. 26. The sharpest quantitative statement is Lemma 4.24,
PDF p. 45, a two-sided Witt/phantom translation:

> "Let c <= omega = |p|^{1/(p-1)}, n in J_p, rho <= 1 be fixed. ... Then
> **|phi_i / p^i| <= c rho^{n p^i} for all i >= 0 if and only if
> |lambda_i| <= c rho^{n p^i} for all i >= 0**."

and the p = 2 estimate inside Cor. 4.31's proof, PDF p. 46:

> "|lambda_{-n p^{m(n)}, j}| <= |p|^j |pi_{m-j}|^{-1} < 1."

Pulita's method deliberately *avoids* the per-coefficient computation; he says
so in the Intro passage quoted above, attributing that style to Matsuda.
**Consequently: the "exact coefficient-valuation lower bounds specialized to
p = 2" that the charge asks me to extract from Pulita do not exist in Pulita.**
I computed them instead (section 3).

The only printed truncated expansion is eq. (2.3.9), PDF p. 27, and it is the
one that matters for the ceiling:

> theta_d((1,0,...,0), T)^{-1} = 1 + pi_m T^n   **mod C**

where `C := {1 + sum c_i T^i : c_i in Z_p[pi_{m+1}], |c_i| < |pi_m|}` (PDF p. 26).
**The leading coefficient of the splitting function is exactly `pi_m`.**

---

## 3. MEASURED valuation tables at p = 2

All arithmetic exact: number fields represented as `Q[t]/(g)` with `g` monic
Eisenstein (so totally ramified over `Q_p`, uniformizer `t`, and
`v(sum c_i t^i) = min_i (v_p(c_i) + i/e)` is exact); series coefficients exact
`Fraction`s; `exp` via the ODE recursion `n c_n = sum_k k f_k c_{n-k}`; division
by series inversion. Cross-checked two independent ways where noted. Valuation
normalized `v(p) = 1` throughout. Scripts in the session scratchpad
(`ah.py`, `l1.py`, `lt.py`, `ltgen.py`, `more.py`, `dens.py`, `run2.py`);
nothing written into the repo outside this file.

### 3.1 Table A - the classical Artin-Hasse splitting `AH(pi x)`, p = 2

First, the charter's own request: verify the unit-coefficient claim.
**REFUTED (witness)** - and the coordinator's Note 1 self-correction is right.
Computing `AH(pi x) = exp(pi x - x^2 + x^4 + 2 x^8 + 16 x^16 + ...)` with
`pi^2 = -2`:

| k | coefficient (basis 1, pi) | v(c_k) | v(c_k)/k | in units of v(pi)=1/2 |
|---:|---|---:|---:|---:|
| 1 | `pi` | 1/2 | 1/2 | **1** |
| 2 | `-2` | 1 | 1/2 | **1** |
| 3 | `-(4/3) pi` | 5/2 | 5/6 | 5/3 |
| 4 | `8/3` | 3 | 3/4 | 3/2 |
| 5 | `(28/15) pi` | 5/2 | 1/2 | **1** |
| 6 | `-128/45` | 7 | 7/6 | 7/3 |
| 7 | `-(536/315) pi` | 7/2 | 1/2 | **1** |
| 8 | `1408/315` | 7 | 7/8 | 7/4 |
| 9 | `(9872/2835) pi` | 9/2 | 1/2 | **1** |
| 10 | `-84032/14175` | 6 | 3/5 | 6/5 |
| 12 | `444736/66825` | 6 | 1/2 | **1** |
| 13 | ... | 13/2 | 1/2 | **1** |
| 16 | ... | 8 | 1/2 | **1** |
| 22 | ... | 11 | 1/2 | **1** |
| 24 | ... | 12 | 1/2 | **1** |

Degree-2 coefficient is `-2`, valuation 1 = `2 v(pi)`, **not a unit**. The two
unit terms `pi^2/2 = -1` and `pi^4/4 = 1` live in the *exponent* and cancel
against the `1/2!`, `1/4!` terms of `exp`. The charter's mechanism for
`a(k) ~ k/3` does not exist.

**`min_{1<=k<=40} v(c_k)/k = 1/2 = v(pi)`, attained at 22 of the 40 indices.**

### 3.2 Why - and the equality set (P1)

`AH(x) = sum a_k x^k` has `a_k in Z_(p)`, so `AH(pi x)` has `c_k = a_k pi^k` and
`v(c_k) = v(a_k) + k v(pi) >= k v(pi)`, with **equality exactly when `a_k` is a
p-adic unit**. Measured at p = 2 to degree **160**:

- non-2-integral coefficients: **none** (integrality holds at p = 2);
- `#{k <= 160 : v_2(a_k) = 0} = 82`, **density 0.512**;
- largest gap between consecutive unit indices: **6**;
- unit indices begin `1, 2, 5, 7, 9, 12, 13, 16, 22, 24, 28, 33, 35, 36, 40,
  41, 42, 43, 44, 46, 48, 49, 50, 53, 54, 57, 62, ...`

So not only `inf_k v(c_k)/k = v(pi)` but also `liminf_k v(c_k)/k = v(pi)`: the
rate is **flat at `v(pi)`**, with the bound attained about half the time.

> **P1: CONFIRMED.** Rate exactly `v(pi) = 1/2` (for the order-4 normalization),
> equality on a set of density ~1/2, verified to degree 160.

**Adversarial check of the coordinator's lemma (L1).** The four flagged gaps:

1. *`-mu(n)/n in Z_p` for `(n,p)=1`* - yes at p = 2 (n odd => `1/n in Z_2`).
2. *Binomial integrality* - `(1-y)^e = sum_k binom(e,k)(-1)^k y^k`; `binom(e,k)`
   is a polynomial in `e` with integer values on `Z`, hence on `Z_p` by density
   and continuity. Fine.
3. *Product rearrangement* - each factor is `1 + O(x^n)`, so the product
   converges x-adically; the coefficient of `x^d` is a finite sum. Fine.
4. *`AH(pi x)` really equals the product over `Z_2[pi]`* - substitution
   `x -> pi x` is a continuous ring endomorphism of the formal series ring, so
   this reduces to the identity over `Z_(2)`.

Point 4's premise, the identity itself, was **verified computationally**:
`exp(sum_i x^{2^i}/2^i)` and `prod_{n odd} (1 - x^n)^{-mu(n)/n}` agree as exact
rational series to degree 40 (`True`). **(L1) holds. PROVED** - though note it
is the classical Dwork/Dieudonne integrality of `AH`, and the shorter proof is
just `AH in Z_(p)[[x]] => c_k = a_k pi^k`. It is also *exactly* the argument
KM already use: 2006.04936v2 section 5.2.2, "**Since E(x) in Z_p[[x]]**, it is
clear that `E_r in O_L[[pi_s t^{-1}]]`."

Control at other primes (`AH(pi x)`, `pi^{p-1} = -p`, to degree 30):

| p | v(pi) | measured `min_k v(c_k)/k` | in units of v(pi) | #k attaining |
|---:|---:|---:|---:|---:|
| 2 (m=1) | 1 | 1 | 1 | 15/40 |
| 3 | 1/2 | 1/2 | 1 | 16/30 |
| 5 | 1/4 | 1/4 | 1 | 25/30 |

**p = 2 is not anomalous.** The rate is `v(pi)` at every prime.

### 3.3 Table B - Witt length m >= 2 (prediction P3)

Multi-level Artin-Hasse-Witt splitting
`Theta^(m)(x) = prod_{i=0}^{m-1} AH(pi^{p^i} x^{p^i})`, `pi^{(p-1)p^{m-1}} = -p`,
p = 2, to degree 40:

| Witt length m | e | v(pi_m) | `min_k v(c_k)/k` | ratio to v(pi_m) | #k attaining |
|---:|---:|---:|---:|---:|---:|
| 1 | 1 | 1 | 1 | **1** | 15 |
| 2 | 2 | 1/2 | 1/2 | **1** | 22 |
| 3 | 4 | 1/4 | 1/4 | **1** | 23 |

`v(c_k)/v(pi_m)` for k = 1..16 at m = 2: `1, 4, 3, 10, 15, 6, 9, 10, 9, 10, 11,
22, 15, 16, 15, 16`. At m = 3: `1, 6, 3, 4, 5, 6, 7, 8, 25, 22, 19, 24, 13, 26,
23, 16`. No cross-term degradation: every factor `AH(pi^{p^i} x^{p^i})` has
coefficient of `x^{p^i k}` equal to `a_k pi^{p^i k}`, i.e. valuation
`(degree) * v(pi_m)` uniformly, so the product inherits the same rate exactly.

> **P3: REFUTED (witness).** No genuine p = 2 loss appears at Witt length
> m >= 2. The rate stays exactly `v(pi_m)`, i.e. exactly `1` in `pi_m`-units,
> for m = 1, 2, 3.

Confirmed independently by the literature. **KMU II, arXiv:2110.08657v1,
section 3.1**, growth ring

> A^m_{pi_chi} = { sum a_k t^{-k} : **v_{pi_chi}(a_k) >= k/m** }

and **Lemma 3.5**:

> "**v_{pi_chi}(tau_j(pi_chi)) = p^j** for 0 <= j < m_chi, infinity for
> j >= m_chi."

and **Theorem 3.6**:

> "Suppose that F_inf/F has delta-stable monodromy. If chi is equicharacteristic
> or finite, then **Etilde_{pi_chi} in A^delta_{pi_chi}**."

**Sections 2-3 of 2110.08657 carry no parity hypothesis.** The splitting
function's rate is `1/delta` at p = 2 exactly as at odd p. Matching statement in
the rank-one paper, KM 1909.06905v2 **Prop. 5.5**: `E_r in O_E^{d(p-1)}`, i.e.
`v_p(a_k) >= k/(d(p-1))` for Swan conductor `d` - rate `1/(d(p-1))`, again with
no parity restriction.

### 3.4 Table C - Pulita's `E_m(T)` and the splitting quotient, p = 2

Computed in `Q_2(zeta_{2^{m+1}})` (Eisenstein `(1+t)^{2^m} + 1`), Lubin-Tate
series `P(X) = 2X + X^2` (= Ghat_m = Dwork's, coincident at p = 2).

**`E_m(T)` itself is NOT overconvergent - its rate is 0.**

| p=2, m | `v(c_k)/k`, k = 1..12 | `min_{k<=32} v/k` |
|---:|---|---:|
| 0 | 1, 1/2, 2/3, 1/4, 2/5, 1/3, 3/7, 1/8, 2/9, 1/5, 3/11, 1/6 | 1/32 |
| 1 | 1/2, 1/4, 1/3, 1/8, 1/5, 1/6, 3/14, 1/16, 1/9, 1/10, 3/22, 1/12 | 1/64 |

`v(c_k)` is **bounded** (the `1/k` pattern), so `liminf v(c_k)/k = 0`: radius
exactly 1. This is an independent confirmation of **Pulita Prop. 2.12**
("converges *exactly* in the disk |T| < 1"; proof: `Ray(L,rho) = rho^{p^m+1}`,
irregularity `p^m`).

It also shows `E_m` is **strictly worse** than `AH(pi_m T)`: the exponent
coefficients are `pi_{m-j}/p^j` for *distinct* torsion points, which are only
*equal in valuation* to `pi_m^{p^j}/p^j`, not equal - so Artin-Hasse
integrality fails by a unit and the radius drops from `p^{v(pi_m)} > 1` to
exactly 1. This is uniform in p, not a p = 2 effect.

**The overconvergent object is the quotient `theta_m(T) = E_m(T^p)/E_m(T)`**
(Pulita Def. 2.35 / Thm 2.13). Measured to degree 64:

| p = 2 | `v(theta_{2^j})` for j = 2..6 | `min v/k` on [N/2, N] | limit |
|---|---|---:|---:|
| m = 0 (order 2) | 2, 3, 5, 9, 17 | 17/64 = 0.2656 | `(2^{j-2}+1)/2^j -> ` **1/4** |
| m = 1 (order 4) | 1, 2, 2, 3, 5 | 5/64 = 0.0781 | `(2^{j-4}+1)/2^j -> ` **1/16** |

The m = 0 limit `1/4 = (p-1)/p^2` matches **Kedlaya, Definition 17.1.3**, p. 292:

> "Suppose that pi in K satisfies pi^{p-1} = -p. Then the power series
> **E(t) = exp(pi t - pi t^p)** ... **has radius of convergence p^{(p-1)/p^2}**
> (exercise), even though the series exp(pi t) has radius of convergence 1."

Cross-check at other primes (my own computation of `exp(pi(x - x^p))`,
`min_k v(c_k)/k`, converging from above):

| p | `(p-1)/p^2` | measured min v/k | at N |
|---:|---:|---:|---:|
| 2 | 1/4 = 0.2500 | 9/32 = 0.2812 | 32 |
| 3 | 2/9 = 0.2222 | 13/54 = 0.2407 | 30 |
| 5 | 4/25 = 0.1600 | 17/100 = 0.1700 | 30 |

**The key comparison the charge asks for.** At the order-4 level (p = 2, m = 1),
in units of `v(pi_m)`:

| splitting function | rate / `v(pi_m)` | rate (v(2)=1) |
|---|---:|---:|
| Pulita/Matsuda `E_m(T^p)/E_m(T)` | 1/8 | 1/16 |
| Dwork short `exp(pi(x - x^p))` (m=0 analogue) | 1/4 | 1/4 |
| **Artin-Hasse `prod AH(pi^{p^i} x^{p^i})` (what KM/KMU actually use)** | **1** | **1/2** |
| ceiling (C1 below) | **1** | **1/2** |

**Nothing beats Artin-Hasse, and Artin-Hasse is at the ceiling.** Note in
particular that the *theta-quotient* form of the splitting function is far
worse than the Artin-Hasse form - this is a real and measurable difference, and
it runs the *opposite* way from what attack (B) hoped.

### 3.5 Table D - varying the Lubin-Tate series changes nothing

The charge asks: "compute the same for Pulita's Lubin-Tate exponential at p = 2
for the multiplicative formal group and for at least one other Lubin-Tate
series". Done, over `P(X) = wX + X^2` for several `w` (each an admissible
Lubin-Tate series: `w` a uniformizer of `Z_2`, `P = X^2 mod w`). Measured to
degree 64.

**Level m = 1 (order-4), `v(pi_1) = 1/2`. Pulita Thm 2.13 requires
`|w - p| <= |p|^{m+2} = 1/8` for overconvergence:**

| `w` | `|w-2|_2` | admissible? | `v(theta_{2^j})`, j=2..6 | `min v/k` on [32,64] |
|---:|---:|---|---|---:|
| 2 (= Ghat_m = Dwork) | 0 | yes | 1, 2, 2, 3, 5 | 5/64 |
| 10 | 1/8 | yes | 1, 2, 2, 3, 5 | 5/64 |
| -6 | 1/8 | yes | 1, 2, 2, 3, 5 | 5/64 |
| 18 | 1/16 | yes | 1, 2, 2, 3, 5 | 5/64 |

**Bit-identical profiles.** Level m = 0 likewise: `w = 2, 10, 6` all give
`v(theta_{2^j}) = 2, 3, 5, 9, 17` and `min v/k = 17/64`.

**Negative control** (this is the falsification test, and it passes): take `w`
*violating* the criterion at m = 1, `|w-2|_2 = 1/4 > 1/8`:

| `w` | `|w-2|_2` | `v(theta_{2^j})`, j=1..5 | `min v/k` on [24,48] |
|---:|---:|---|---:|
| 6 | 1/4 | 3/2, -, 1, 1, 1 | 1/32 |
| -2 | 1/4 | 3/2, 2, 1, 1, 1 | 1/32 |
| 14 | 1/4 | 3/2, 2, 1, 1, 1 | 1/32 |

`v(theta_{2^j})` is **bounded (= 1)**, i.e. rate 0, i.e. **not overconvergent** -
exactly as Pulita Thm 2.13 predicts, reproduced here from first principles by
an independent implementation. So the machinery is validated *and* the
conclusion is confirmed: **within the admissible Lubin-Tate family the rate is
constant, and leaving the family destroys overconvergence rather than improving
the rate.**

> **Does ANY choice beat 1/3?** In units of `v(pi_m)`: the Artin-Hasse splitting
> gives rate **1** (better than 1/3), and no splitting function can exceed 1.
> Pulita's theta-quotient gives **1/8** (worse than 1/3). So the answer is
> "yes, and it is the classical one, and it was already what KM/KMU use" -
> which is precisely why attack (B) has nothing to contribute.

---

## 4. Is there a ceiling? YES - and it has no p = 2 anomaly

### 4.1 (C1) An elementary ceiling. PROVED.

**Lemma (C1).** Let `theta(T) = 1 + sum_{k>=1} c_k T^k` be a splitting function
for a character of order `p^M`, over a complete field extending `Q_p`,
convergent on `|T| <= 1`, and normalized so that `theta(a)` is a *primitive*
`p^M`-th root of unity for some `a` with `|a| = 1`. Suppose
`v(c_k) >= r k` for all `k >= 1`. Then

>   **`r <= v(zeta_{p^M} - 1) = 1 / (p^{M-1} (p-1)) = v(pi_{M-1})`.**

*Proof.* `theta(a) - 1 = sum_{k>=1} c_k a^k`, and `v(c_k a^k) = v(c_k) >= rk >= r`
for every `k >= 1`, so by the ultrametric inequality
`v(theta(a) - 1) >= r`. But `theta(a) = zeta` is a primitive `p^M`-th root of
unity, whose `zeta - 1` has valuation exactly `1/(p^{M-1}(p-1))`. Hence
`r <= 1/(p^{M-1}(p-1))`. QED

Two remarks. (i) The hypothesis is exactly Pulita's setting - **Theorem 2.38**,
PDF p. 26:

> "Let a^p = a in O_L, and let lambda in W_m(O_L^{phi=1}). Then
> theta_d^{(phi)}(lambda, a) is a **p^{m+1}-th root of 1**. ... the image of 1
> ... is the inverse of the unique primitive p^{m+1}-th root of 1, say xi_m,
> satisfying **|a^n pi_m - (xi_m - 1)| < |a^n pi_m|**."

so `|xi_m - 1| = |pi_m|`, which is the number (C1) needs, quoted. (ii) The
bound is *attained*: Pulita eq. (2.3.9) gives leading coefficient exactly
`pi_m`, and my section 3.2 measurement shows Artin-Hasse achieves `r = v(pi_m)`
on a density-1/2 set of degrees, so `inf` and `liminf` coincide there.

**(C1) caps only bounds of the shape `v(c_k) >= r k`.** A *shifted* certificate
like `floor((k-1)/3)` is not of that shape (it permits `v(c_1) >= 0`), so (C1)
does not cap its asymptotic slope. For that one needs the radius theory:

### 4.2 The radius ceiling, from the fetched literature. Exact, not an inequality.

`liminf_k v(c_k)/k = log_p(radius of convergence)`, so the asymptotic slope is
the radius, and the radius of a solvable rank-one object is *pinned* by its
break / Swan conductor.

**Kedlaya, Theorem 19.4.1** (section 19.4, p. 321):

> "Assume that kappa_K is perfect. Let V be a finite-dimensional vector space
> over K, and let tau : G_{kappa_K((t))} -> GL(V) be a continuous homomorphism
> ... with finite local monodromy. Then, for rho in (0,1) sufficiently close
> to 1,
>   **R(D+(V) (x) F_rho) = rho^b,  b = max{ i >= 1 : G^i ... subset ker(tau) }.**"

An **equality**. Attribution (Notes to Ch. 19, p. 324): "originally stated in its
present form by Matsuda [169, Corollary 8.8] ... thanks to the p-adic global
index theorem of **Christol and Mebkhout [51, Theorem 8.4-1], [52, Corollaire
5.0-12]** ... **Tsuzuki [208, Thm 7.2.2]** ... **Crew [63, Thm 5.4]**".
Underlying decomposition, **Kedlaya Theorem 12.6.4 (Christol-Mebkhout)**,
p. 212: the intrinsic subsidiary radii of `M_b (x) F_rho` "are all equal to
**(rho/beta)^b**".

**Pulita Prop. 2.12**, PDF p. 19, the same ceiling in his normalization:

> "Since |w_0| = omega, by Lemma 1.14, we have **Ray(L, rho) = rho^{p^m + 1},
> for all rho < 1. In particular, the irregularity of L is p^m.**"

**Robba's necessity**, Pulita Intro 0.0.3, PDF pp. 2-3:

> "Moreover Robba shows the **necessity** of the condition
> **|pi_0 alpha_i| = |p|^{1/p^i}**, for all i >= 0."

**Kedlaya Remark 9.9.5**, p. 163, for Matsuda's rank-one module:

> "It is possible to prove directly that, for rho in [1, +inf) sufficiently
> close to 1, **I R(M_h (x) F_rho) = rho^{-p^h}** (exercise)."

**Answer to the charge's question 3.** *Yes, there is a theoretical ceiling on
the decay rate of a splitting function for an order-`2^m` character, and it is
exact rather than an inequality.* **But it is a clean function of the Swan
conductor / break with no p = 2 anomaly whatsoever.** Every statement above is
uniform in p, and Pulita's Thm 2.13 / 2.28 - the p = 2-inclusive replacement
for Matsuda's p != 2 result - has no parity hypothesis. The ceiling therefore
does **not** kill the NoH-p2 program; it kills attack (B) only, by removing the
headroom (B) was hoping to exploit.

Two caveats recorded honestly: Kedlaya's two exact-radius claims (Def. 17.1.3,
Rem. 9.9.5) are stated **as exercises** with no proof in the book and no errata
entry; and Matsuda's own coefficient estimates could not be fetched (paywalled).
Neither affects the conclusion, which rests on Thm 19.4.1 / Thm 12.6.4 / Pulita
Prop. 2.12, all of which are proved statements in the fetched sources.

### 4.3 Where `floor((k-1)/3)` actually comes from - NOT the splitting function

This is the load-bearing correction, and it settles (B).

**KMU I, arXiv:2110.08656v1, after Def. 6.3, p. 33** (general odd p):

> "For each k > p - 1, define the positive integer
>   **a(k) = floor( (k - 1)/(p - 1) ).**
> Then the elements pi^{a(k)/m_P} t_P^{-k} constitute a formal basis for
> A^m_{pi,P}."

**Correction to the charter/brief:** for `p >= 3` the rate is
`floor((k-1)/(p-1))`, **not** `floor((k-1)/2)`; `floor((k-1)/2)` is only the
p = 3 instance. The paper's opening line is "Let p be an odd prime".

**Remark 6.5, verbatim, p. 33:**

> "Suppose that p = 2. For k >= 3, define **a(k) = floor((k - 1)/3)**. A similar
> construction provides a submodule A^m_{pi,P} subset A+_{pi,P} with the
> following property: Let k = 2l - r with r = 0 or 1. Then
>   U_p(pi^{a(k)/m_P} t_P^{-k}) in pi^{(a(k) - a(l+r))/m_P} A^m_{pi,P}.
> **This estimate is too low for applications to the global setting.** For
> example, if k = 5 = 2 * 3 - 1, then a(k) - a(l+r) = 0, and this contributes
> an extra segment of slope 0 in the global Hodge bound below."

(Their example checks: `a(5) - a(4) = floor(4/3) - floor(3/3) = 1 - 1 = 0`.)

`a(k)` is a **weight exponent on a `U_p`-stable formal basis**, not a splitting
coefficient valuation. What must hold is the *combinatorial* identity
(KM 1909.06905v2, proof of Prop. 4.4): "**First note that
a(j + np) - a(j + n) = n.**" That identity forces denominator exactly `p - 1`.
And the `p - 1` is the **ramification index of the auxiliary tame Belyi map**,
KMU I **Prop. 4.3**, p. 21:

> "The composite eta = eta_q o eta_0 : X -> P^1_{F_q} is a tame Belyi map such
> that (1) eta(P) = 0 for each P in S; (2) **If eta(P) = 1 then the ramification
> index of eta at P is p - 1.**"

with local Frobenius `sigma(u_1) = (u_1 + 1)^p - 1` and
`sigma(t_P) = ((t_P^{p-1} + 1)^p)^{1/(p-1)} + 1`. At p = 2 the index `p - 1 = 1`
is trivial and the construction degenerates; the smallest usable tame index is
**3** (smallest integer > 1 coprime to 2). Hence `floor((k-1)/3)`.

That the geometry is otherwise fine is stated by the authors, KMU I
**Remark 4.2**, p. 21:

> "In [23], Sugiyama and Yasuda extend Fulton's result to the case p = 2. **We
> have omitted this case for other reasons (see Remark 6.5).** By a recent
> theorem of Kedlaya-Litt-Witaszek, eta exists even without extending the base
> field [13]."

and the diagnosis had already shifted between papers - KM 1909.06905v2,
section 1.4:

> "When p = 2 it is likely that the methods in this paper still work. **The main
> difficulty is that some estimates in section 4 must be modified.**"

**No source in the fetched literature claims `floor((k-1)/3)` is optimal.**
Remark 6.5 says only "A similar construction provides..." and "This estimate is
too low for applications" - an obstruction to *their* construction, not a
theorem. **OPEN**, and it is the right thing for workstreams (A)/(C)/(D) to
attack.

---

## 5. Answer to charge item 4 (what a(k) a better splitting would certify)

Moot, and worth saying precisely why. `01-kmu-extraction.md` **had not landed**
at the time of writing (checked at the end of this run; the directory held only
`00-charter.md` and `10-notes-coordinator.md`), so this is stated against the
primary sources directly.

The splitting function enters KMU's local estimate only through
`Etilde_P in 1 + pi R_q` (KMU I, proof of Prop. 6.4) and, quantitatively,
through `Etilde_{pi_chi} in A^delta_{pi_chi}` (KMU II Thm 3.6). **Both already
hold at p = 2 with the same `delta` as at odd p** - no parity hypothesis in
either statement, and my section 3.3 measurement confirms the rate is exactly
`1/delta` at Witt lengths 1, 2, 3. Improving the splitting function therefore
changes **nothing** in `a(k)`: `a(k)`'s denominator is the tame index of `eta`,
and `Etilde` contributes only the `1 + pi(...)` unit factor at the end of the
proof.

Concretely: even a *hypothetical* splitting function with infinite decay rate
would leave Remark 6.5's `a(5) - a(4) = 0` untouched, because that quantity is
`floor(4/3) - floor(3/3)` - pure arithmetic of the basis weights.

**The lever that would move `a(k)` is a `U_p`-stable basis whose weight function
satisfies `a(pl + r) - a(l + r) = l`, which requires an auxiliary map with tame
ramification index `p - 1 = 1` over the point 1 - impossible for a tame index -
or a restructuring that avoids needing that identity at all.** Attack (A)'s
bigraded transplant and attack (C)'s direct measurement of the true `U_2`
profile both target exactly that, and are unaffected by anything in this
document. Attack (D)'s "what estimate would suffice" should be stated against
the identity `a(pl+r) - a(l+r) = l`, not against a coefficient rate.

Coordinator's Note 2 (the even-part commutation trick) is **not** touched by
this no-go: it restructures the operator, not the splitting function, and it is
in the same family as the live levers above.

---

## 6. Status summary

| claim | label | evidence |
|---|---|---|
| Charter's "unit coefficients at degree 2, 4 of `AH(pi x)`" | **REFUTED (witness)** | `c_2 = -2`, `v = 1 = 2 v(pi)`; table A |
| (L1) `v(c_i) >= i v(pi)` for `AH(pi x)`, all p incl. 2 | **PROVED** | integrality of AH; product identity verified to degree 40; 2-integrality to degree 160 |
| P1: rate exactly `v(pi)`, equality infinitely often | **CONFIRMED** | density 0.512 of unit `a_k` to degree 160, max gap 6 |
| P3: genuine p = 2 loss first appears at Witt length m >= 2 | **REFUTED (witness)** | rate exactly `v(pi_m)` at m = 1, 2, 3; KMU II Lem 3.5 / Thm 3.6 have no parity hypothesis |
| Pulita's construction includes p = 2 | **PROVED (quoted)** | no parity hypothesis in Thm 2.13/2.21/2.28/3.4/4.57; Kedlaya Ex. 17.1.5 |
| Pulita states a per-coefficient decay bound | **REFUTED** | only `1 + pi_m T B[[T]]` (Prop 2.15) and Lem 4.24; he says he avoids the computation |
| `E_m(T)` is overconvergent | **REFUTED (witness)** | `v(c_k)` bounded, rate 0, degree 64; = Pulita Prop 2.12 |
| Some Lubin-Tate series at p = 2 beats the rate | **REFUTED (witness)** | 4 series at m=1, 3 at m=0: identical profiles; `\|pi_j\| = omega^{1/p^j}` for *every* LT series |
| Leaving the admissible LT family helps | **REFUTED (witness)** | negative control `w = 6, -2, 14`: rate collapses to 0 |
| (C1) ceiling `r <= v(pi_{M-1})` for `v(c_k) >= rk` | **PROVED** | this document, section 4.1; Pulita Thm 2.38 supplies the hypothesis |
| A theoretical ceiling exists on the decay rate | **YES, exact** | Kedlaya Thm 19.4.1 (`R = rho^b`), Thm 12.6.4; Pulita Prop 2.12; Robba necessity |
| That ceiling has a p = 2 anomaly | **REFUTED** | every statement uniform in p; Pulita closed Matsuda's `p != 2` gap in 2007 |
| `floor((k-1)/3)` is a splitting-function rate | **REFUTED** | it is a `U_p`-basis weight; denominator = tame Belyi index (KMU I Prop 4.3, Rem 6.5) |
| `floor((k-1)/3)` is optimal at p = 2 | **OPEN** | no source claims it; Rem 6.5 says only "too low for applications" |
| **Attack (B) can improve the p = 2 local estimate** | **REFUTED** | sections 3.4, 3.5, 4.1, 4.3, 5 |

## 7. Reproduction

Scratchpad scripts (session-local, not committed): `ah.py` (number-field power
series over `Q[t]/(pi^e - c)`), `l1.py` (AH exp-form vs product-form, unit
census), `dens.py` (integrality/unit density to degree 160), `lt.py` (cyclotomic
Eisenstein tower, Pulita `E_m` and `theta_m`), `ltgen.py` (arbitrary Lubin-Tate
series `wX + X^2`, incl. the negative control), `more.py` / `run2.py` (short
Dwork splitting, multilevel Witt splitting, p = 3 / p = 5 controls). All runs
completed in well under the 5-minute / 2 GB budget. Independent cross-checks
used: exp-form vs product-form for AH; `(p-1)/p^2` at p = 2, 3, 5 against
Kedlaya Def. 17.1.3; Pulita Prop. 2.12 and Thm 2.13 reproduced from first
principles.

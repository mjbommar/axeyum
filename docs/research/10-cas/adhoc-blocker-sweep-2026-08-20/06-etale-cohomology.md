# Ad hoc blocker sweep, lane 06: etale cohomology and effective sheaf theory

Field specialist: etale cohomology, quantitative/effective sheaf theory,
Betti-number bounds, characteristic-two wild ramification.

Scope note: this file is my own diary.  I edit no other repository file and
run no mutating git command.  Every claim below is labelled PROVED (with a
citation or a replayable command), REFUTED (with the exact witness), or
OPEN.  Finite computation is evidence, never a theorem.

---

## 2026-08-20T19:09Z -- orientation

Read, in order:

- `docs/research/10-cas/lemire-review-2026-08-20-reaim.md` (264 lines)
- `docs/plan/status/52-gf2-lemire.md` (747 lines, full)

Key items extracted from the ledger that bound my charge:

1. **Cyclic/Foulkes compression (PROVED in-lane, commit `6c6e36597`).**
   Ramanujan-sum orthogonality gives the von Mangoldt long-cycle character as
   `p_n = sum_{k | n} mu(k) Ind_{C_n}^{S_n} theta_{n/k}`, coefficient mass
   `2^omega(n)`.  A uniform effective bound `B(n,r) <= n^4` for the *cyclic*
   rank-one local systems appearing there would close every degree past the
   certified degree-400 handoff (twelve base rows + strict twelve-degree
   induction, replayable).
2. **Sawin equation-level audit (commit `9e3cb37a4`).**  The naive
   half-parameter recursion through Sawin's characteristic-two vanishing-cycle
   argument is REJECTED: (a) his characteristic-two logarithmic-derivative
   bound only controls the image of the bad locus at infinity, and (b) the
   generic smoothing behind the vanishing-cycle theorem is not
   `S_n`-equivariant, so the resulting ordinary cohomological support bound
   cannot be projected onto the long-cycle virtual character.
3. **What was REFUTED at extension-field rows, precisely.**  Two *different*
   statements died, and neither is the surviving cyclic conjecture:
   - `ff09b9baa`: at `(ell,n,r) = (2,5,5)` the exhaustive `32^5` `GF(32)` row
     needs normalized coefficient `26`, refuting the *universal* `ell^4 = 16`
     Betti budget for the **connected Adams (fourth-cumulant) trace**.
   - `0cbcafe68`: the exact trace polynomial `T_r = q^12 (q-1)(q^2-6q+6)` has
     normalized `q`-degree five, one above the proposed degree-four cutoff --
     so the *cohomological degree cutoff* is false as a universal all-level
     statement too.
   - `ef5a90f0b` / `9a3e77556`: the level-three `GF(16)` merge over all `16^7`
     monics has minimum normalized coefficient `250`, refuting the `ell^4 = 81`
     Adams allowance that had survived through `GF(8)`; and Gorodetsky's
     period-24 symmetry gives the closed form
     `T_r = q^16 (q^2-1)(q^4-6q^2+6)`, normalized `q`-degree eight, refuting
     both the degree-six cutoff and the "one extra `q`" repair (at `q=128`).
   **These refutations are about the ADAMS / fourth-cumulant local system at
   fixed small `ell` over growing `GF(q)`.**  The surviving conjecture is a
   different one: a quartic bound `B(n,r) <= n^4` for the **cyclic rank-one**
   summands over the **fixed** base field `GF(2)` with `n` growing, needed
   only for `n > 400`.  A small-`ell`, large-`q` counterexample does not touch
   it.  I must not conflate them, and any expert-facing statement must make
   the distinction explicit.
4. **Long-cycle Euler-trace theorems (PROVED in-lane, `1c517c87f`,
   `ada2c4542`, `35b4c6ad2`, `636f9da38`).**  Writing `n = 2^a b` with `b`
   odd: the non-top long-cycle complex has alternating Euler trace zero at
   every non-power-of-two degree; the homogeneous-cone decomposition removes
   the power-of-two exception unweighted (punctured `G_m`-torsor Euler trace
   zero, vertex contributes 1).  **With Frobenius inserted the fibre factor is
   `2^r - 1`, which is `1` over `GF(2)`** -- so the surviving object is a
   *projective Frobenius-weighted long-cycle trace*, and the reduced
   projective fixed locus has exactly `phi(b)` points (never empty): no free
   cyclic-torsor quotient.
5. **Wan--Zhang complete-intersection Betti theorem (`9a49f2023`)** applies to
   Sawin's ordered-root variety and improves the old generic bound, but still
   misses the first two post-400 endpoint margins by **6,829 and 6,851 bits**.
   So generic total-Betti technology is not one log short here -- it is
   thousands of bits short.  Only cyclic-eigenspace / signed long-cycle
   cancellation can close it.

---

## 2026-08-20T19:20Z -- literature sweep 1: where the exponential constant enters

All statements below were fetched live today; none is from memory.

### Sawin, Duke 2021 (arXiv:1809.05137)
<https://arxiv.org/abs/1809.05137>, ar5iv text
<https://ar5iv.labs.arxiv.org/html/1809.05137>.

Verbatim items I extracted (theorem numbering as in the ar5iv text):

- **Variety.** `X_{n,m,c}` is the closed subscheme of `A^n` with coordinates
  `(a_1,...,a_n)` defined by
  `prod_{i=1}^n (1 - u a_i) = 1 + c_1 u + ... + c_m u^m  (mod u^{m+1})`.
- **Theorem 1.2 (= Cor 4.7).**
  `|sum_{deg g < h} Lambda(f+g) - q^n| <= 6 (n+2)^{2n-h} q^{(h + floor(n/p) - floor((n-h)/p) + 1)/2}`.
  (For `Lambda` the main term in his normalisation is `q^h` after the
  `Lambda`-weight bookkeeping; the exponent is what matters here.)
- **Lemma 2.3 (the characteristic-`p` logarithmic-derivative lemma).**
  `dim(R cap D) <= floor(n/p) - floor(m/p) - 1`, because at a point of the bad
  locus `d/du prod (1 - u a_i) = 0`, so the product lies in `k[u^p]` and has at
  most `m-1` distinct roots.
- **Lemma 2.4 (vanishing cycles).** For a complete intersection `Xbar` of
  dimension `d`, hyperplane section `D`, singular locus `Z`:
  `H^i_c(X) = 0` for `dim Z + d + 1 < i < 2d`; and `H^{2d}_c = Q_l(-d)` if
  `dim Z < d - 1`.  Proof via `R Phi j_! Q_l` supported on `Z` and semiperverse
  [Deligne--Katz, SGA 7 XIII 2.1].
- **Proposition 4.3 / Corollary 4.4 (THE BETTI MECHANISM).**
  For `pi` a subrepresentation of `Ind_{S_{n_1} x ... x S_{n_k}}^{S_n} Q_l`,
  `B(pi) <= 3 (k+2)^{n+m}`; for `pi` inside the regular representation,
  `B(pi) <= 3 (n+2)^{n+m}`.
  This follows from **Katz 2001, Theorem 12** applied to a variety cut by `m`
  equations of degree `<= k` in `n` variables, after Frobenius reciprocity plus
  the projection formula.

**Answer to charge (1a): the exponential constant is NOT a singular-support or
characteristic-cycle bound in the Duke paper.**  It is Katz's generic
`sum of Betti numbers` bound for an affine complete intersection, and the
reason a Young (parabolic) subgroup is the only group that appears is
structural: `X/(S_{n_1} x ... x S_{n_k})` is *again* a prescribed-coefficient
variety, cut by `m` equations of degree `<= k` in `n` variables, so Katz's
theorem applies verbatim to it.  A **cyclic** subgroup has no such quotient
presentation; Sawin reaches `Ind_{C_n}^{S_n} theta_r` only by embedding it in
the regular representation, i.e. taking `k = n`, which is exactly where
`3(n+2)^{n+m}` comes from.  There is no cyclic-specific mechanism in the paper
to improve.

Katz's own bound and its modern sharpening (checked today):
Katz, *Sums of Betti numbers in arbitrary characteristic*, FFA 7 (2001),
<https://web.math.princeton.edu/~nmk/BettiSum14.pdf>; and the 2024 improvement
"On sums of Betti numbers of affine varieties", <https://arxiv.org/abs/2411.02970>,
whose abstract states verbatim: "if V is a subvariety of the affine N-space
defined by polynomials of degree at most d, then the sum of its l-adic Betti
numbers does not exceed `2(N+1)^{2N+1}(d+1)^N`.  This answers a question of Katz
(FFA 2001)."  Both are exponential in the ambient dimension.

### Sawin, Acta 2024 (arXiv:2102.09730)
<https://arxiv.org/abs/2102.09730>, ar5iv <https://ar5iv.labs.arxiv.org/html/2102.09730>.

Here the mechanism **is** singular support / characteristic cycle.  Theorem 1.7
has the shape
`|sum_{f in M_n, f = a mod g} F_rho(f) - (1/phi(g)) sum_{gcd(f,g)=1} F_rho(f)|
 <= 2 (C_1(rho) + C_2(rho) sqrt q) q^{(n-m)/2}`,
and Section 1.3 says the strategy "applies the characteristic cycle, and
associated strong Betti number bounds"; Lemma 2.19 extends Saito's
characteristic-cycle formula `CC(Rf_+ F) - f_= CC(F)` supported on `S`.

Two structural facts kill direct import for us, and both are in the paper's own
framing:

1. **The modulus must be squarefree.**  The restriction to squarefree `g` is
   stated as inherent to the compactification strategy.  Our modulus is
   `x^{ell+1}` -- maximally non-squarefree, wildly ramified at `x`.  This is not
   a technical hypothesis one strips off; the whole compactification is built on
   it.
2. **The constants are `C_i(rho)`, i.e. representation-dependent, and unbounded
   in the same way.**  Nothing in the paper makes them polynomial in `n` for
   `rho` of long-cycle type.

### Sawin--Forey--Fresan--Kowalski, "Quantitative sheaf theory", JAMS 36 (2023)
<https://arxiv.org/abs/2101.00635>, ar5iv <https://ar5iv.labs.arxiv.org/html/2101.00635>.

Extracted:

- Definition 3.2: `c(A) = max_{0<=m<=n} sum_i h^i(P^m, l_a^* A)` over generic
  linear `l_a : P^m -> P^n`; Definition 6.3 extends it to quasi-projective
  varieties through a chosen embedding.
- Theorem 1.1 / 6.8 (continuity of the six operations): `c(D(A)) << c(A)`,
  `c(A tensor B) << c(A) c(B)`, `c(f^* C) << c(f) c(C)`, `c(f_+ A) << c(f) c(A)`,
  "the implied constants depend only on `(n,m)` and are effective".
- Proposition 3.17: `sum_i h^i(P^n, A tensor l_g^* B) <= b_n(cc(A), cc(B))`
  with `b_0(x,y) = x.y` and `b_n(x,y) = x.y + 4 b_{n-1}(f_n(x), f_n(y))`,
  `f_n` the linear map of Lemma 3.15.

**Answer to charge (1b): QST's effective bounds are polynomial in the complexity
but exponential (at best `4^n`, and in practice `(deg)^{Theta(n)}` through the
`f_n` iterates) in the ambient dimension.**  The paper contains no statement
bounding Betti numbers polynomially in the dimension, and none of the
applications need one.  QST's selling point -- uniformity in the *characteristic*
-- is exactly the property we want at `q = 2`; its price -- exponential
dependence on the *dimension* -- is exactly the one we cannot pay, because our
ambient dimension is `n` (root variety in `A^n`) and the variety dimension is
`h = floor(n/2)+1`.  Moreover the complexity of the rank-one sheaf `L_{theta_r}`
on the cyclic quotient is itself at least of the order of the Swan conductor
`~ ell` coming from `x^{ell+1}`, so the bound is `>= ell^{Theta(n)}` before any
of the constants are chased.

So all three of Katz / Wan--Zhang / QST are dimension-exponential, and the
ledger's measured misses (`6,829` and `6,851` bits for Wan--Zhang at `n = 401,
402`) are what that costs.  Nothing in effective sheaf theory as it stands is
one log factor away.

---

## 2026-08-20T19:35Z -- the arithmetic of the reduced statement, done exactly

Before hunting for a technique I re-derived what the Foulkes ledger actually
needs, because the note's clean sufficient form `B(n,r) <= n^4` hides how much
room there is.

At the endpoint `ell = ceil(n/2) - 1`, `h = n - ell = floor(n/2) + 1`, the note's
weight is `W = h + floor(n/2) - floor(ell/2) + 1 = 2h - floor(ell/2)` and the
sufficiency inequality is `(2^omega(n) B)^2 2^W < (2^h - P_n)^2`, i.e.

```text
B  <  2^{h - W/2} / 2^omega(n)  =  2^{floor(ell/2)/2} / 2^omega(n)  ~  2^{ell/4} = 2^{n/8}.
```

**So the room is exponential, not polynomial.**  Any bound `B(n,r) <= C^n` with
`C < 2^{1/8} = 1.0905...` would do; `n^4` is merely a convenient point inside
that window (and the twelve-degree induction is what converts it to all `n`).
This is worth recording because it changes what one asks an expert for.

Second, the same arithmetic isolates the two *separate* characteristic-two
deficits, which the ledger has been treating as one:

- **Weight deficit.**  For `p > n` Lemma 2.3 gives `dim(R cap D) < 0`, so
  `W = h + 1` and Sawin's error is `q^{(h+1)/2}` -- genuine square-root
  cancellation, matching the Keating--Rudnick variance heuristic (pure weight
  `h`).  At `p = 2`, `floor(n/2) - floor(ell/2) ~ ell/2`, so `W ~ 1.5 h`.  The
  wild bad locus alone eats half of the available exponent.
- **Betti deficit.**  `3(n+2)^{2n-h} = 2^{Theta(n log n)}` versus the
  `2^{n/8}` that is affordable.

Fixing only the weight is not enough (`2^{ell/2}` of room, still not
`2^{Theta(n log n)}`); fixing only the Betti constant is enough, which is why the
ledger targeted it.  That made the cyclic Betti bound the whole ballgame -- and
so it is worth attacking the question of whether it is even *true*.

---

## 2026-08-20T19:50Z -- an exact identity nobody in the ledger had written down

`B(n,r)` in the Foulkes ledger plays the role of Sawin's `B(pi)`, i.e. it is an
honest dimension: `B(n,r) = sum_i dim Hom_{C_n}(theta_r, H^i_c(X_{n,ell,0}))`,
the total Betti number of the `theta_r`-multiplicity space, and the estimate
used is `|Tr(Frob | theta_r-part)| <= B(n,r) q^{W/2}` via Deligne.

Since `Q_l[C_n]` is semisimple (`l != 2`), for each cohomological degree
`sum_{r mod n} dim Hom(theta_r, H^i_c) = dim H^i_c`.  Hence

```text
(IDENTITY)     sum_{r mod n} B(n,r)  =  sum_i dim H^i_c(X_{n,ell,0}).
```

**PROVED (elementary).**  Consequence: `B(n,r) <= n^4` for all `r` would force
the *total* Betti number of the ordered-root variety `X_{n,ell,0}` to be at most
`n^5`.  That is a polynomial replacement for Katz's bound on this family -- an
enormous strengthening (state of the art for a general affine variety in `A^N`
of degree `<= d` is `2(N+1)^{2N+1}(d+1)^N`).  That made me suspect the
conjecture is not merely unproved but false, and gave a cheap way to test it:
lower-bound a Betti sum by a point count.

Dead end recorded: I first tried to *determine* `B_total` by computing
`#X_{n,ell,0}(F_{2^s})` for many `s` and running Berlekamp--Massey / Hankel
minors (the technique the lane already uses for `A_r(9,4)`).  That is hopeless
beyond `n = 5`: pinning a length-`B` recurrence needs `2B` field sizes and the
cost is `q^{ell+1}`.  Abandoned in favour of the one-field lower bound below.

---

## 2026-08-20T20:00Z -- bounded computation 1: deviation probe

Wrote a standalone C probe (scratchpad, not in the repo):
`betti_probe.c`, DP over the truncated principal-unit group
`U = (1 + u F_q[[u]]) / (1 + u^{ell+1})`, order `q^ell`; state update
`c'_j = c_j + a c_{j-1}` with `c_0 = 1`.  It returns the full distribution of
`#X_{n,ell,c}(F_q)` over *all* prescribed-coefficient vectors `c`.

```sh
gcc -O2 -o betti_probe betti_probe.c -lm
./betti_probe <n> <ell> <s>          # q = 2^s
```

Independent control (exhaustive Python enumeration of `F_2^n`): `n=5,ell=2 -> 6`;
`n=7,ell=3 -> 36`; `n=9,ell=4 -> 10`.  All three match the DP exactly.  The
`(n,ell)=(5,2)` row reproduces the lane's known
`A_r(5,2) = (-4)^r - (-2)^r` for `r = 1..6` (`dev0 = -2, +12, -56, +240, -992,
+4032`), which cross-validates the probe against the committed CAS.

Family series at `q = 4`, `n = 9..23` at the endpoint, reporting
`sqrt(E_c[dev^2]) / q^{h-1/2}` (a rigorous lower bound for
`sqrt(E_c[B_c^2])` by Deligne, since all non-top weights are `<= 2h-1`):

```text
n      9     11     13     15     17     19     21     23
bound  3.11   6.32  11.08  20.57  36.20  66.77 124.06 232.08
```

Ratio per `Delta n = 2` is `2.03, 1.75, 1.86, 1.76, 1.84, 1.86, 1.87` -- clean
geometric growth `~ 1.36^n`.  At `q = 2`, `n = 9..49` the same statistic gives
`1.98, 4.25, 8.22, 15.77, 30.30, 58.45, 113.2, 220.1, 429.2, 838.8, 1642.4`
(steps of `4`), i.e. `~ 1.18^n`.  Both bases exceed `2^{1/8} = 1.0905`.

That was already suggestive, but the `q = 2` numbers had an obvious structural
cause, and chasing it produced the actual result.

---

## 2026-08-20T20:15Z -- the mechanism: over F_2 the identity fibre is a binomial sum

Over `F_2` the multiplier set is only `{1, 1+u}`, so
`prod_i (1 + u a_i) = (1+u)^k` with `k = #{i : a_i = 1}`.  The order of `1+u` in
`(F_2[u]/u^{ell+1})^*` is `2^t` with `2^t = 2^{ceil(log2(ell+1))}` (because
`(1+u)^{2^t} = 1 + u^{2^t}`).  Therefore, **exactly**:

```text
(BINOM)   #X_{n,ell,0}(F_2) = sum_{k = 0 (mod 2^t)} binom(n,k),
          2^t = 2^{ceil(log2(ell+1))}.
```

**PROVED (elementary).**  Verified against twelve independent DP rows
(`n = 7,9,13,17,21,25,29,33,37,41,45,49` at the endpoint): predicted
`36, 10, 1288, 18, 20350, 2042976, 67863916, 34, 435898, 350343566,
73006209046, 6499270398160` -- all twelve match the probe **exactly**.

At the endpoint `ell + 1 = floor(n/2) + 1 = h`, so `2^t` is the least power of
two `>= h`, hence `2^t in [n/2, n)` and the sum always contains `k = 0` and
`k = 2^t`, giving `#X_0(F_2) >= binom(n, 2^t)`, which is `2^{n H(2^t/n) - o(n)}`.

Compare `dim X_{n,ell,c} = h` for *every* `c` (the map `X_c -> A^h` sending a
tuple to its polynomial is finite and surjective).  So the `F_2`-points of the
identity fibre outnumber `q^{dim}` by an exponential factor.  This is precisely
the characteristic-two, base-field-`F_2` pathology: the image of
`a |-> 1 - ua` generates a *cyclic group of order about n*, not an
equidistributed set.  Over `F_q` with `q` large the same set generates enough of
`U` and `#X_0(F_q) ~ q^h`; the pathology is a `q = 2` phenomenon only, which is
exactly why Sawin's theorems need `q` large.

---

## 2026-08-20T20:30Z -- REFUTATION of the cyclic Foulkes architecture

Set, for each `g | n` (writing `M = n/g`),

```text
T_g := # { (alpha_1,...,alpha_g) in (F_{2^M})^g :
           prod_i charpoly_{F_2}(alpha_i) has its top ell coefficients zero }.
```

`T_g` is the twisted Lefschetz count `Tr(Frob . c^j | H^*_c(X_{n,ell,0}))` for
any `j` with `gcd(j,n) = g` (`c^j` has `g` cycles of length `M`; the twisted
points are `g`-tuples in `F_{2^M}`), so in particular **every `T_g` is a
non-negative integer**, `T_n = #X_{n,ell,0}(F_2)`, and `T_1` is the Lemire /
von Mangoldt endpoint count.  With `zeta = zeta_n` and Ramanujan sums,

```text
tau_r := Tr(Frob | theta_r-isotypic part)
       = (1/n) sum_{j mod n} zeta^{-rj} T_{gcd(j,n)}
       = (1/n) sum_{g|n} T_g c_{n/g}(r),
```

and the lane's proved compression `p_n = sum_{k|n} mu(k) Ind_{C_n}^{S_n} theta_{n/k}`
becomes the exact identity `sum_{k|n} mu(k) tau_{n/k} = T_1`.

Because all `T_g >= 0` and the `j = 0` term is `T_n`,

```text
(LOWER)    tau_0  >=  T_n / n  =  #X_{n,ell,0}(F_2) / n.
```

**PROVED.**  Note `theta_0 = theta_n` is the *trivial* character, i.e. the
`k = 1` term of the Foulkes sum -- one of the summands the ledger must bound.
Its multiplicity space is `H^*_c(X_{n,ell,0} / C_n)`.

### Exact control at small n

`foulkes_check.py` (scratchpad) enumerates the whole endpoint interval
(`2^h` monic polynomials), factors each over `F_2`, and computes every `T_g`,
every `tau_r`, and the Moebius recombination.

```sh
python3 foulkes_check.py 9 15 21 25
```

```text
n=9   h=5   T_1=37    T_3=1                     T_9=10          tau_0=26
n=15  h=8   T_1=301   T_3=751   T_5=406         T_15=6436       tau_0=844
n=21  h=11  T_1=2101  T_3=148   T_7=1           T_21=20350      tau_0=2212
n=25  h=13  T_1=8551  T_5=1                     T_25=2042976    tau_0=88560

in every row  sum_{k|n} mu(k) tau_{n/k}  ==  T_1   exactly  (MATCH=True),
and  tau_0 >= T_n / n  as predicted.
```

The two columns that matter:

```text
n      |T_1 - 2^h| / 2^h      tau_0 / 2^h
9        0.156                 0.81
15       0.176                 3.30
21       0.026                 1.08
25       0.044                10.81
```

`T_1` -- the quantity Lemire needs -- stays within a few percent of the main
term `2^h`, exactly as the conjecture says.  The *cyclic summand* `tau_0`
crosses `2^h` at `n = 15` and is already `10.8 x 2^h` at `n = 25`.  The
decomposition inflates the object.

### The witness at n = 401

`ell = 200`, `h = 201`, `ell+1 = 201`, so `2^t = 256` and
`#X_0(F_2) = 1 + binom(401,256)`, `log2 = 373.95`.  Hence

```text
tau_0 >= 2^{365.30},        while the whole main term is 2^h = 2^{201}
                            and the endpoint needs |T_1 - 2^h| < 2^{201}.
```

Feeding this through the ledger's own weight `W = 302`:

```text
B(401, theta_0) >= tau_0 / 2^{W/2} = 2^{365.30 - 151} = 2^{214.30},
ledger allowance                                        2^{49} - 1,
                                                 miss:  165.3 bits.
```

All twelve induction base rows fail, by a growing margin:

```text
 n     2^t   log2 #X_0(F_2)   log2 tau_0 >=    W    log2 B_min   allowance
401    256      373.95           365.30       302     214.30       2^49
402    256      375.41           366.76       304     214.76       2^49
403    256      376.87           368.21       304     216.21       2^49
...
412    256      389.69           381.00       312     225.00       2^49
```

Across `401 <= n <= 1024`: **523 of 624 degrees** have
`#X_0(F_2)/(n 2^h) > 2^{h - W/2}` (the allowance), and 541 of 624 exceed `n^4`.
The 101 exceptions are exactly the `n` sitting just above a power of two, where
`2^t / n` is close to 1 and the binomial `binom(n, 2^t)` degenerates (e.g.
`n = 513`: `#X_0(F_2) = 514`).  Those are degrees where *this particular lower
bound* is weak, not degrees where the conjecture survives.

### What this refutes, stated carefully

- **REFUTED:** the uniform cyclic Betti statement `B(n,r) <= n^4` in its
  intended reading (Sawin's `B(pi)`, an honest sum of Betti numbers of the
  `theta_r`-multiplicity space).  Explicit witness: `n = 401`, `r = 0`
  (trivial character, the `k = 1` Foulkes summand),
  `B >= 2^{214.30} >> n^4 = 2^{34.6}`.
- **REFUTED, and this is the stronger statement:** the *architecture*, not just
  the constant.  The refutation needs no cohomology at all.  `T_1 ~ 2^{201}` is
  decomposed by the Foulkes identity into `2^omega(n)` cyclic traces each of
  size `>= 2^{365}`.  For `n = 401` (prime) there are exactly two,
  `T_1 = tau_0 - tau_1`, and they must cancel to relative precision `2^{-164}`.
  **No bound on the individual summands -- Betti-based, weight-based, or
  otherwise -- can recover the endpoint, because the individual summands are
  genuinely that large.**  The compression's small *coefficient* mass
  (`2^omega(n)`) was never the issue; the *summands* are the issue.
- **NOT refuted:** the ledger's implication `(CF)` itself, which remains a
  correct (now vacuous) conditional; and nothing about the certified degrees
  `<= 400`, the Euler-trace theorems, or the projective eigenline
  classification.
- **NOT refuted:** an "effective" reading in which `B(n,r)` is a *trace-bound
  constant* rather than a dimension.  But that reading is not available either,
  for the same reason: `tau_0` is not a cancelling object, it is a
  non-negative-dominated sum bounded below by `T_n / n`.  The trace itself is
  too big.

### Why this is consistent with everything else the lane found

The ledger's `q > 2` extension-field refutations (`GF(32)` needing normalized
coefficient `26`, `GF(16)` needing `250`, `T_r = q^12(q-1)(q^2-6q+6)`,
`T_r = q^16(q^2-1)(q^4-6q^2+6)`) are about the *Adams / fourth-cumulant* local
system at small fixed `ell` with `q` growing -- a different object, and their
failure mode is a `q`-degree one.  The present refutation is about the *cyclic*
summands at the base field `q = 2` with `n` growing, and its failure mode is a
`binom(n, n/2)`-versus-`2^{n/2}` one.  They are independent, and together they
say the same thing: **no uniform Betti-style constant survives characteristic
two at the endpoint.**

---

## 2026-08-20T20:50Z -- what the true statement looks like

The same small-`n` table says what *is* true.  With `h = floor(n/2)+1`:

```text
n      |T_1 - 2^h|      n 2^{h/2}
9         5              50.9
15       45             240
21       53             950
25      359            2263
```

so the data are consistent with the natural purity statement

```text
(PURITY)   | T_1(n) - 2^h |  <=  C n 2^{h/2},
```

i.e. the long-cycle sector of `H^*_c(X_{n,ell,0})` has Frobenius weights `<= h`
(not `W ~ 1.5h`) and effective multiplicity `O(n)`.  This is the exact
function-field analogue of the Keating--Rudnick short-interval variance
`Var(psi) = q^h (n - h - 2)`, and it implies Lemire with enormous room.  It is
also, honestly, at least as hard as Lemire.  Its virtue is that it is the *right
shape*: a statement about weights and about the long-cycle sector as a single
object, with `Frob` and `c` never separated.

The technique that formally matches that shape, and the one I would put in front
of an expert:

- **Saito's characteristic cycle / singular support** (the machinery Sawin
  actually uses in the Acta paper, via Lemma 2.19 extending
  `CC(Rf_+ F) - f_= CC(F)`), combined with
- **the Lefschetz--Verdier trace formula localised by a twisted Milnor formula**
  for the finite-order automorphism `c`, so that `Tr(Frob . c | H^*_c)` is
  computed from local terms on the fixed locus of `c` rather than from a
  dimension count.  The relevant modern technology:
  Umezaki--Yang--Zhao, "Characteristic class and the epsilon-factor of an etale
  sheaf", Trans. AMS 2020; Yang--Zhao, "Cohomological Milnor formula and Saito's
  conjecture on characteristic classes", Inventiones (2025),
  <https://arxiv.org/abs/2209.11086>; and the relative Lefschetz--Verdier
  formalism, <https://arxiv.org/pdf/2309.02587>.
  The lane has already computed the geometry these need: the reduced projective
  fixed locus of `c` has exactly `phi(oddpart(n))` points (commit `636f9da38`),
  the unweighted Euler trace is `1` at every degree `n >= 5` (`ada2c4542`), and
  the wild/tame split is classified (`1c517c87f`).  What is missing is the
  *local* term at those points in characteristic two with wild ramification --
  i.e. a twisted Milnor number, not a global Betti number.

I did not find, and do not believe there exists, a published equivariant
characteristic-cycle bound that applies to a wildly ramified `C_n`-action at
`p = 2` on a singular complete intersection of this size.  That is the missing
lemma.

---
## 2026-08-20T21:05Z -- dead ends, recorded

1. **Determining `B_total` by Berlekamp--Massey on `#X(F_{2^s})`.**  Needs `2B`
   field sizes at cost `q^{ell+1}` each; feasible only for `n = 5`.  Abandoned.
2. **Second-moment / variance lower bound on Betti numbers via
   `E_c[dev^2] / q^{2h-1}`.**  Works (it is rigorous by Deligne) and shows
   `~1.36^n` growth at `q = 4`, but it is lossy and it bounds `max_c`, not the
   `c = 0` fibre Lemire needs.  Superseded by the exact `(BINOM)` identity.
3. **"Many top-dimensional components" as an alternative explanation of the
   large `F_2`-count.**  Rejected: at `n = 13` the ratio
   `#X_0(F_q)/q^h` is `10.06, 27.7, 5.63, 0.42` for `q = 2,4,8,16` -- it drops
   below 1, so it is not a component count (which would be a stable integer
   `>= 1`).  It is oscillation from many eigenvalues.
4. **Reading `B(n,r)` as an effective trace constant to save the conjecture.**
   Rejected: `tau_0 >= T_n/n` is a lower bound on the *trace itself*, so the
   effective constant is equally large.
5. **Importing quantitative sheaf theory.**  Rejected on the arithmetic above:
   polynomial in complexity, exponential in dimension; our dimension grows.
6. **Importing Sawin's Acta 2024 characteristic-cycle bound.**  Rejected: the
   modulus must be squarefree there, and ours is `x^{ell+1}`.

---

# FINDINGS

## (a) Sharpest reformulation

Let `n >= 5`, `ell = ceil(n/2) - 1`, `h = n - ell = floor(n/2) + 1`, and let

```text
X = X_{n,ell,0} = { (a_1,...,a_n) in A^n_{F_2} : prod_i (1 - u a_i) = 1 mod u^{ell+1} },
```

an `h`-dimensional complete intersection carrying an `S_n`-action.  Let `c` be an
`n`-cycle.  Lemire's conjecture at degree `n` is exactly

```text
Tr(Frob . c | H^*_c(X_{Fbar_2}, Q_l))  >  1,           and one wants
| Tr(Frob . c | H^*_c) - 2^h |  =  o(2^h).
```

The sufficient bound the ledger needs is **not** `B(n,r) <= n^4`; it is
`B < 2^{h - W/2} / 2^{omega(n)} ~ 2^{ell/4} = 2^{n/8}`, i.e. *any* bound `C^n`
with `C < 2^{1/8}`.  And the char-2 loss splits into two independent deficits:
`W ~ 1.5h` instead of `h+1` (Lemma 2.3's wild bad locus), and
`3(n+2)^{2n-h} = 2^{Theta(n log n)}` instead of `2^{n/8}` (Katz).

The sharpest *surviving* reformulation is a purity statement, with `Frob` and
`c` never separated:

```text
(PURITY)  the long-cycle sector of H^*_c(X) is pure of weight <= h with
          effective multiplicity O(n):   |Tr(Frob . c | H^*_c) - 2^h| <= C n 2^{h/2}.
```

Verified exactly at `n = 9,15,21,25` (`5, 45, 53, 359` against `50.9, 240, 950,
2263`).  This is the geometric form of the Keating--Rudnick variance
`Var(psi) = q^h(n-h-2)`.

## (b) Most promising technique

Not a Betti bound.  The only shape that can work is an **equivariant,
localised trace formula**: Saito's characteristic cycle plus a
Lefschetz--Verdier localisation with a *twisted Milnor formula* for the
finite-order automorphism `c`, computing `Tr(Frob . c | H^*_c)` from local terms
on `Fix(c)` -- a locus the lane has already classified exactly (`phi(oddpart n)`
projective eigenlines, `636f9da38`; unweighted Euler trace `1`, `ada2c4542`).
Citations verified today:
Saito, "Characteristic cycles and the conductor of direct image"
(<https://arxiv.org/abs/1704.04832>, as cited in Sawin's Acta paper Lemma 2.19);
Sawin, Acta Math. 2024, <https://arxiv.org/abs/2102.09730> (the only place the
CC machinery is actually run on a short-interval/progression problem);
Umezaki--Yang--Zhao, Trans. AMS 2020, and Yang--Zhao, Inventiones 2025,
<https://arxiv.org/abs/2209.11086> (cohomological Milnor formula on singular
varieties); relative Lefschetz--Verdier, <https://arxiv.org/abs/2309.02587>;
Sawin--Forey--Fresan--Kowalski, JAMS 2023, <https://arxiv.org/abs/2101.00635>
(effective machinery, but dimension-exponential).

## (c) Decisive obstructions

1. **The cyclic/Foulkes architecture is dead at `q = 2`, proved.**  `T_1 ~ 2^h`
   is decomposed into `2^omega(n)` cyclic traces each of size `>= 2^{365}` at
   `n = 401`.  Individual bounds cannot recover a quantity `2^{164}` times
   smaller.  Witness `(BINOM)` + `(LOWER)`, twelve DP rows and four exact
   Foulkes rows as controls.
2. **Every available Betti technology is exponential in the dimension**, and the
   dimension here grows: Katz `3(k+2)^{n+m}`; the 2024 sharpening
   `2(N+1)^{2N+1}(d+1)^N`; Wan--Zhang `binom(n-1,ell-1)(ell+1)^n`
   (the lane's own `6,829`-bit miss); QST `b_n` with a factor 4 per dimension
   step.  None is one log factor away; they are thousands of bits away, and
   after this refutation we know that is *correct*, not merely lossy.
3. **Sawin's two mechanisms are structurally unavailable here**: the Duke paper's
   Betti step is a Young-subgroup quotient argument with no cyclic analogue; the
   Acta paper's characteristic-cycle step requires a squarefree modulus and ours
   is `x^{ell+1}`.  Together with the lane's earlier equivariant-smoothing audit
   (`9e3cb37a4`), the Sawin route is closed in all three of its parts.

## (d) Concrete next experiments runnable here

1. **Promote `(BINOM)` to a bounded native CAS operation** and make the twelve
   induction rows `401..412` a replayable *refutation* certificate for
   ADR-0550's cyclic Betti obligation.  Cost: seconds; the identity is a
   binomial sum.
2. **Measure the purity constant.**  Extend `foulkes_check.py` (interval
   enumeration + factorisation, cost `2^h`) to `n <= 41` and tabulate
   `|T_1 - 2^h| / (n 2^{h/2})`.  If it stays below a small absolute constant,
   `(PURITY)` becomes the lane's replacement conjectured fact with real
   evidence, and the constant is the thing to conjecture sharply.
3. **Compute the twisted local terms.**  For small `n` compute all `T_g` (already
   done) and compare against the *predicted* localisation
   `Tr(Frob . c^j) = sum over Fix(c^j) of local terms`; this calibrates what a
   twisted Milnor number must equal at `p = 2` before any theorem work.
4. **Repeat `(BINOM)` over `F_4`** for the 101 exceptional degrees in
   `[401,1024]` (those just above a power of two) to see whether the refutation
   can be made to cover *all* degrees rather than 84 percent.  The `F_4`
   multiplier set is `{1, 1+ua : a in F_4}`, so the analogue of `(BINOM)` is a
   subgroup-index count in `U(F_4)`; cheap.

## (e) New to the ledger

- `(BINOM)`: `#X_{n,ell,0}(F_2) = sum_{k = 0 mod 2^t} binom(n,k)`,
  `2^t = 2^{ceil(log2(ell+1))}`.  PROVED, verified on twelve DP rows.
- `(IDENTITY)`: `sum_{r mod n} B(n,r) = sum_i dim H^i_c(X_{n,ell,0})`.  PROVED.
- `(LOWER)`: `tau_0 >= #X_{n,ell,0}(F_2) / n`, from non-negativity of every
  twisted Lefschetz count.  PROVED.
- **REFUTED:** the quartic cyclic Betti obligation (ADR-0550 / `6c6e36597`),
  witness `n = 401`, `B >= 2^{214.30}` against allowance `2^{49}-1`; all twelve
  induction bases fail; 523 of 624 degrees in `[401,1024]` fail.
- **REFUTED (stronger):** the cyclic/Foulkes *architecture* at `q = 2`, without
  reference to cohomology.
- The room in `(CF)` is `2^{ell/4}`, i.e. exponential; `n^4` was an
  unnecessarily strong sufficient form.  Worth recording so no future lane
  re-targets a polynomial statement when an exponential one would do.
- The char-2 penalty decomposes into a *weight* deficit (`W ~ 1.5h`) and a
  *Betti* deficit; fixing the weight alone leaves `2^{ell/2}` of room and is not
  sufficient against Katz, but is sufficient against a `2^{n/8}`-scale bound.
- Sawin Acta 2024 is closed for this endpoint by its squarefree-modulus
  hypothesis (new source-level audit point, alongside the existing Duke audit).

## (f) DRAFT one-page problem statement for an expert

> **Weights of the long-cycle sector of a prescribed-coefficient variety in
> characteristic two**
>
> Fix `n >= 5`, put `ell = ceil(n/2) - 1` and `h = n - ell = floor(n/2) + 1`, and
> let
> ```
> X = X_n = { (a_1,...,a_n) in A^n_{F_2} : prod_{i=1}^{n} (1 - u a_i) = 1  (mod u^{ell+1}) },
> ```
> Sawin's variety `X_{n,ell,c}` at `c = 0`.  It is an `h`-dimensional complete
> intersection with an `S_n`-action, and `X -> A^h` (tuple to its polynomial) is
> finite surjective.  Let `c` be an `n`-cycle.  By Grothendieck--Lefschetz for
> the twisted Frobenius,
> ```
> Tr(Frob . c | H^*_c(X_{Fbar_2}, Q_l))  =  # { alpha in F_{2^n} : deg( charpoly(alpha) - x^n ) <= floor(n/2) },
> ```
> so the positivity of this trace for all `n` is exactly **Lemire's 2011
> conjecture**: every degree `n` admits a monic irreducible `f` over `F_2` with
> `deg(f - x^n) <= floor(n/2)`.  (Verified computationally to `n = 400`.)
>
> **The question.**  Is the "long-cycle sector" of `H^*_c(X)` pure of weight
> `<= h`, with polynomially bounded effective multiplicity?  Concretely:
> ```
> (PURITY)     | Tr(Frob . c | H^*_c(X)) - 2^h |  <=  C n 2^{h/2}       for an absolute C.
> ```
> Exact values: `|T_1 - 2^h| = 5, 45, 53, 359` at `n = 9, 15, 21, 25`, against
> `n 2^{h/2} = 50.9, 240, 950, 2263`.
>
> **What is known and what fails.**  Sawin (Duke 170 (2021), arXiv:1809.05137)
> proves `|Tr(Frob . c | H^*_c) - q^h| <= 6(n+2)^{2n-h} q^{W/2}` with
> `W = h + floor(n/p) - floor((n-h)/p) + 1`.  At `p > n` this is `W = h+1`:
> square-root cancellation, and the estimate is decisive once `q` exceeds
> `(n+2)^{O(1)}`.  At `q = 2` two things go wrong at once.  (i) The bad locus of
> Lemma 2.3 has dimension `~ ell/2`, so `W ~ 1.5h`, leaving only a factor
> `2^{h - W/2} ~ 2^{n/8}` of room.  (ii) The Betti factor is
> `2^{Theta(n log n)}`, from Katz's generic bound (FFA 2001, Thm 12); the 2024
> sharpening `2(N+1)^{2N+1}(d+1)^N` (arXiv:2411.02970), the Wan--Zhang
> complete-intersection bound `binom(n-1,ell-1)(ell+1)^n`, and the complexity
> bounds of quantitative sheaf theory (JAMS 36 (2023)) are all exponential in the
> dimension, which here grows like `n/2`.
>
> **A route we closed, in case it is tempting.**  Foulkes plus Ramanujan
> orthogonality gives the exact virtual-character identity
> `p_n = sum_{k | n} mu(k) Ind_{C_n}^{S_n} theta_{n/k}`, whose coefficient mass
> is only `2^{omega(n)}`; this suggests bounding each cyclic multiplicity space
> `H^*_c(X/C_n, L_{theta_r})` separately.  That cannot work over `F_2`.  Writing
> `T_g` for the `c^j`-twisted point count (`g = gcd(j,n)`, `T_g >= 0`,
> `T_n = #X(F_2)`, `T_1` the count above), the trivial-character summand
> satisfies `tau_0 = (1/n) sum_j T_{gcd(j,n)} >= #X(F_2)/n`.  Over `F_2` the only
> linear factors are `1` and `1+u`, whose product is `(1+u)^k` of order
> `2^t = 2^{ceil(log2(ell+1))}`, so
> ```
> #X(F_2) = sum_{k = 0 (mod 2^t)} binom(n,k)   >=  binom(n, 2^t),   2^t in [n/2, n).
> ```
> At `n = 401` this gives `tau_0 >= 2^{365.3}` while `2^h = 2^{201}`: each cyclic
> summand exceeds the object it decomposes by `2^{164}`, and the summands must
> cancel to that relative precision.  (Verified exactly for
> `n = 9, 15, 21, 25`, where the Moebius recombination reproduces `T_1` on the
> nose; the inflation begins at `n = 15`.)  So any argument that bounds the
> cyclic pieces separately is dead at `q = 2`, however good the Betti bound.
>
> **What we are asking.**  Is there an equivariant route to `(PURITY)` -- for
> instance a Lefschetz--Verdier localisation of `Tr(Frob . c | H^*_c)` on
> `Fix(c)` with a twisted Milnor formula, in the presence of the wild
> `p = 2` ramification of `x^{ell+1}`?  The relevant fixed-point geometry is
> already explicit: the reduced projective `c`-fixed locus consists of exactly
> `phi(oddpart(n))` eigenlines, the unweighted alternating trace of `c` on
> `H^*_c(X)` is `1` for every `n >= 5`, and after removing the top class the
> non-top long-cycle Euler trace is `0`.  What is missing is the *local* term at
> those points -- a Frobenius-weighted, wildly ramified, twisted Milnor number --
> rather than any global dimension count.
>
> Any of: a proof of `(PURITY)`; a proof that `W` can be improved to `h + O(log n)`
> at `p = 2`; or a reason that `(PURITY)` is as hard as the original -- would all
> be valuable to us.


---

## Appendix: sources of the bounded probes (scratchpad only; nothing added to crates)

Both ran in well under five minutes and under 300 MB.  Reproduce with:

```sh
gcc -O2 -o betti_probe betti_probe.c -lm
./betti_probe 49 24 1        # n ell s   (q = 2^s)
python3 foulkes_check.py 9 15 21 25
```

### betti_probe.c

```c
/* Bounded probe: distribution of #X_{n,ell,c}(F_q) over all prescribed
 * coefficient vectors c, where X_{n,ell,c} = { (a_1..a_n) in A^n :
 *   prod_i (1 - u a_i) = 1 + c_1 u + ... + c_ell u^ell  mod u^{ell+1} }.
 * char 2, q = 2^s.  DP over the truncated principal-unit group U (order q^ell).
 * Outputs: q^h (h=n-ell), #X_0, mean, max |dev|, second moment, and
 * R = E_c[(#X_c - q^h)^2] / q^{2h-1}   (a rigorous lower bound for E[B_c^2],
 * B_c = sum of non-top compactly-supported Betti numbers, by Deligne). */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>

static int s, q, ell, n;
static unsigned char *mulT; /* q x q multiplication table for s>1 */

static inline int gmul(int x,int y){return mulT[x*q+y];}

int main(int argc,char**argv){
  n=atoi(argv[1]); ell=atoi(argv[2]); s=atoi(argv[3]);
  q=1<<s;
  long long states=1;
  for(int i=0;i<ell;i++){states*= (long long)q; if(states> (1LL<<27)){printf("TOO BIG\n");return 1;}}
  unsigned long long *old=calloc(states,8), *nw=calloc(states,8);
  if(!old||!nw){printf("OOM\n");return 1;}
  old[0]=1;
  if(s==1){
    unsigned long long mask=(states-1);
    for(int step=0;step<n;step++){
      memset(nw,0,states*8);
      for(long long t=0;t<states;t++){
        unsigned long long v=old[t]; if(!v)continue;
        nw[t]+=v;                                   /* a = 0 */
        unsigned long long u=((t^(t<<1))^1ULL)&mask;/* a = 1 */
        nw[u]+=v;
      }
      unsigned long long *tmp=old; old=nw; nw=tmp;
    }
  } else {
    /* GF(2^s) tables via a fixed primitive polynomial */
    static const int poly[]={0,0,0x3,0x3,0x3,0x5,0x3,0x3,0x1d,0x11,0x9};
    int p=poly[s];
    mulT=malloc((size_t)q*q);
    for(int x=0;x<q;x++)for(int y=0;y<q;y++){
      int a=x,b=y,r=0;
      while(b){ if(b&1)r^=a; b>>=1; a<<=1; if(a&q)a^=(q|p);}
      mulT[x*q+y]=(unsigned char)r;
    }
    int *dig=malloc(sizeof(int)*ell);
    for(int step=0;step<n;step++){
      memset(nw,0,states*8);
      for(long long t=0;t<states;t++){
        unsigned long long v=old[t]; if(!v)continue;
        long long tt=t; for(int j=0;j<ell;j++){dig[j]=tt&(q-1); tt>>=s;}
        for(int a=0;a<q;a++){
          long long u=0; int prev=1;
          for(int j=0;j<ell;j++){ int c=dig[j]^gmul(a,prev); u |= ((long long)c)<<(s*j); prev=dig[j]; }
          nw[u]+=v;
        }
      }
      unsigned long long *tmp=old; old=nw; nw=tmp;
    }
  }
  int h=n-ell;
  long double qh=powl((long double)q,h);
  __int128 tot=0; unsigned __int128 sq=0; long double maxdev=0; long long argmax=-1;
  for(long long t=0;t<states;t++){
    tot+=old[t];
    long double d=(long double)old[t]-qh;
    sq += (unsigned __int128)((long double)fabsl(d)*fabsl(d)+0.5L);
    if(fabsl(d)>maxdev){maxdev=fabsl(d);argmax=t;}
  }
  long double Estates=powl((long double)q,ell);
  long double second=(long double)(unsigned long long)(sq>> 0 ? 0:0); /* placeholder */
  /* recompute second moment in long double to avoid 128-bit printf issues */
  long double sm=0;
  for(long long t=0;t<states;t++){ long double d=(long double)old[t]-qh; sm+=d*d; }
  long double R = (sm/Estates)/powl((long double)q,2*h-1);
  (void)second;(void)tot;
  printf("n=%d ell=%d q=%d h=%d states=%lld  q^h=%.6Le  X_0=%llu  dev0=%.6Le  maxdev=%.6Le  E[dev^2]=%.6Le  R=%.6Le  sqrtR=%.6Le\n",
     n,ell,q,h,states,qh,(unsigned long long)old[0],(long double)old[0]-qh,maxdev,sm/Estates,R,sqrtl(R));
  return 0;
}
```

### foulkes_check.py

```python
"""Exact check of the cyclic/Foulkes decomposition at the Lemire endpoint over GF(2).
   T_g = # {(a_1..a_g) in (F_{2^{n/g}})^g : prod charpoly_{F2}(a_i) has top ell coeffs 0}
       = Tr(Frob . c^j | H^*_c(X_{n,ell,0})) for any j with gcd(j,n)=g.
   tau_r = (1/n) sum_j zeta_n^{-rj} T_{gcd(j,n)}   (Frobenius trace on the theta_r-isotypic part)
   Foulkes/Ramanujan:  sum_{k|n} mu(k) tau_{n/k} = T_1 = the von Mangoldt endpoint count."""
import sys
from math import comb, gcd, ceil, log2, factorial
from fractions import Fraction

def polymulmod(a,b):
    r=0
    while b:
        if b&1: r^=a
        b>>=1; a<<=1
    return r
def polydivmod(a,b):
    db=b.bit_length()-1; q=0
    while a.bit_length()-1>=db and a:
        s=a.bit_length()-1-db; q|=1<<s; a^=b<<s
    return q,a
def irreducibles(maxd):
    out={d:[] for d in range(1,maxd+1)}
    for d in range(1,maxd+1):
        for c in range(1<<d, 1<<(d+1)):
            if c&1==0: continue            # x | c  -> reducible unless d==1
            ok=True
            for e in range(1,d//2+1):
                for p in out[e]:
                    if polydivmod(c,p)[1]==0: ok=False;break
                if not ok: break
            if ok: out[d].append(c)
    out[1]=[0b10,0b11]                     # x and x+1
    return out

def factorize(f, irr, maxd):
    fac={}
    for d in range(1,maxd+1):
        for p in irr[d]:
            while True:
                q,r=polydivmod(f,p)
                if r: break
                fac[p]=fac.get(p,0)+1; f=q
            if f==1: return fac
    if f!=1: fac[f]=fac.get(f,0)+1        # remaining irreducible factor
    return fac

def run(n):
    ell=ceil(n/2)-1; h=n-ell
    irr=irreducibles(h)                    # any factor of degree>h has cofactor degree<h
    divs=[g for g in range(1,n+1) if n%g==0]
    T={g:0 for g in divs}
    base=1<<n
    for low in range(1<<h):                # f = x^n + (poly of degree < h)
        f=base^low
        fac=factorize(f,irr,h)
        degs={p:(p.bit_length()-1) for p in fac}
        for g in divs:
            M=n//g
            ms={}; ok=True
            for p,e in fac.items():
                d=degs[p]
                if M%d or (e*d)%M: ok=False;break
                ms[p]=e*d//M
            if not ok: continue
            tot=factorial(g); w=1
            for p,m in ms.items():
                tot//=factorial(m); w*=degs[p]**m
            T[g]+=tot*w
    # tau_r via Ramanujan grouping: tau_r = (1/n) sum_{g|n} T_g * c_{n/g}(r)
    def ramanujan(q,r):                    # c_q(r) = sum_{d | gcd(q,r)} d*mu(q/d)
        def mu(m):
            res=1; x=m; p=2
            while p*p<=x:
                if x%p==0:
                    x//=p
                    if x%p==0: return 0
                    res=-res
                p+=1
            if x>1: res=-res
            return res
        return sum(d*mu(q//d) for d in range(1,q+1) if q%d==0 and r%d==0)
    tau={}
    for r in range(n):
        s=sum(Fraction(T[g])*ramanujan(n//g,r) for g in divs)
        tau[r]=s/n
    def mobius(m):
        res=1;x=m;p=2
        while p*p<=x:
            if x%p==0:
                x//=p
                if x%p==0: return 0
                res=-res
            p+=1
        if x>1: res=-res
        return res
    ks=[k for k in divs if mobius(k)!=0]
    foulkes=sum(mobius(k)*tau[(n//k)%n] for k in divs)
    print(f"n={n} ell={ell} h={h} 2^h={2**h}")
    for g in divs: print(f"   T_{g:<4} = {T[g]}")
    print(f"   tau_0            = {tau[0]}   (>= T_n/n = {Fraction(T[n],n)})")
    print(f"   sum_k mu(k) tau_{{n/k}} = {foulkes}   T_1 = {T[1]}   MATCH={foulkes==T[1]}")
    print(f"   |tau_0| / 2^h    = {float(tau[0]/2**h):.6g}      |T_1 - 2^h|/2^h = {float(abs(Fraction(T[1])-2**h)/2**h):.6g}")
    print(f"   max_r |tau_r|/2^h = {max(float(abs(v))/2**h for v in tau.values()):.6g}")
for n in [int(x) for x in sys.argv[1:]]:
    run(n)
```

---

## Addendum 2026-08-20T21:20Z -- the n = 401 witness in closed form

Because 401 is prime, `gcd(j,401) = 1` for all `j != 0`, so the Ramanujan
grouping collapses completely and the whole Foulkes decomposition is two lines:

```text
X   := #X_{401,200,0}(F_2) = 1 + binom(401,256) = 2^{373.95...}   (2^t = 256, k in {0,256})
T_1 := # { alpha in F_{2^401} : deg(charpoly(alpha) - x^401) <= 200 }  =  2^{201}(1 + o(1))

tau_0 = (X + 400 T_1)/401        (trivial character, the k=1 Foulkes summand)
tau_r = (X -     T_1)/401        (every r != 0, all Galois-conjugate)
tau_0 - tau_1 = T_1              (the Foulkes identity, exact)
```

So `tau_0, tau_1 >= 2^{365.3}` while their difference is `2^{201}`: the two
summands agree to relative precision `2^{-164}`.  Bounding them separately --
by a Betti number, a complexity, a characteristic cycle, or anything else --
cannot produce `T_1 < 2^{201}` or `T_1 > 1`.  That is the refutation in its
shortest form, and it uses no cohomology at all.

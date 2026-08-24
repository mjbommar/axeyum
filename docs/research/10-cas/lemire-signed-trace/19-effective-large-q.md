# Effectivising the large-`q` Kaser--Lemire theorem

Status: research note, 2026-08-23. Lane `lemire-signed-trace`. This note
extends note 16 (`16-large-q-threshold.md`), which verified that for `p` odd
and `q = p^l > 961 e^2 p^2 = 7100.883 p^2` the combination of
Bagshaw arXiv:2401.10399 Cor. 2.5 with the reversal duality `r = ceil(n/2)`
gives Kaser--Lemire over `F_q` for all `n >= n_0(q)`, **with `n_0`
ineffective**. The question here is whether `n_0` can be made explicit, how it
trades against the level-of-distribution parameter `omega`, and whether the
resulting gap against the Hsu/Cohen range can be closed.

Primary sources read as LaTeX: arXiv:2401.10399 (all of `Files/`) and
arXiv:1808.04001 (`Geometric_Mobius.tex`, secs. "Character sums", "The Mobius
Function", "Linear forms in Mobius", "Level of distribution"). Machine checks:
`scripts/lemire-signed-trace/lemire_effective_largeq.py`.

## 0. Verdict, up front

1. **There is no Siegel-type mechanism anywhere in the chain.** The strong
   prior in the brief is confirmed: every `L`-function in sight is a
   polynomial, every bound is Weil/Deligne plus elementary counting, and every
   "sufficiently large" is a limit with an explicit rate. The ineffectivity is
   pure bookkeeping.
2. **But the bookkeeping, done honestly on the argument as written, produces
   `n_0(3^11) ~ 10^{344.5}`.** One step is responsible: both papers invoke the
   *pointwise* divisor bound `tau(x) = O_eps(q^{eps deg x})` at an `eps` that
   the same proof drives down to `8.63 * 10^{-4}`, and the extremal constant
   there is `q^{10^{341.2}}` (check C3.3). Nothing else in the chain is worse
   than `q^{O(1)}` times a polynomial in `n`.
3. **The fix is known and exact, not conjectural.** Over `F_q[T]` the *averaged*
   divisor identity is `sum_{x monic, deg x = m} tau(x) = (m+1) q^m` -- an
   identity, with no `eps` at all (check C3.1). Every pointwise `q^{eps n}`
   in Bagshaw sec. 4--5 and Sawin--Shusterman sec. 4 sits inside a sum over the
   variable it bounds, so it can be replaced by that identity at a cost of a
   polynomial factor. That rewrite is the whole remaining task, and it is
   routine, but it is *not done* -- so this note cannot state an explicit
   `n_0`, only the machinery around it.
4. **The `omega` trade-off in the brief is inverted.** Constants do not blow up
   as `omega -> 1/2`; `omega = 1/2` is optimal in *both* directions (the
   `q`-threshold `g(omega)` is minimised there, and the savings exponent
   `delta(omega)` is maximised there; check C2.4). What degrades near the
   endpoint is only the *odd*-`n` requirement `omega >= 1/2 + 1/(2n)`, and at
   `q = 3^11` that is already satisfied by every odd `n >= 78` (C2.5). **The
   window is not the blocker; the implied constant is.**
5. **Coefficient slack is not a lever either.** With `k` coefficients of slack
   the Hsu/Cohen range jumps from odd `n <= 839` to odd `n <= 149118215`
   (`k = 1`) and `n <= 2.6 * 10^{13}` (`k = 2`), check C1.4. So the gap exists
   *only* at the exact half-degree endpoint -- exactly the lane's standing
   diagnosis (note 00, Barrier III: Kaser--Lemire is `~log_q n` past Weil).
6. **`3^11` is the smallest admissible `q` but not the best target.** Under a
   polynomial-constant hypothesis on `C`, the Bagshaw range and the Hsu/Cohen
   range first *meet with no gap* at `q = 3^14 = 4782969`, and meet robustly
   (for every constant of shape `C <= q^{10} n^6`) at `q = 3^17`. See sec. 6.
7. **What is closed unconditionally, today:** Kaser--Lemire over `F_{3^11}` for
   every even `n <= 354292` and every odd `n <= 839` (Hsu/Cohen), plus the
   certified odd witnesses of sec. 5. The residual is an interval of odd `n`,
   and its upper end is not known.

## 1. Where the ineffectivity lives

### 1.1 The chain

```text
Kaser--Lemire over F_q, degree n
  <- reversal duality (Keating--Rudnick), r = ceil(n/2), F = T^r, a = 1
  <- Bagshaw arXiv:2401.10399 Cor. 2.5   [level of distribution, arbitrary F]
       <- Bagshaw Thm 2.3 (mobius_3/4)            [case k <= r(1+eps)]
       |    <- Thm 2.1 (bilinear_savings) <- Lem. bilinear/garaev
       |    <- Lem. inverse_energy_k=2 <- Bagshaw2023 Lem. 5.3
       |    <- Lem. weil / weil_incomplete <- Bagshaw2023 Lem. A.13
       |    <- Cor. mobius_arith <- Cor. Han+BLL <- Lem. BLL, Lem. Han
       |    <- Lem. divisors (Cilleruelo--Shparlinski)     ** see sec. 3 **
       <- SS Thm 4.5 = `LinearFormsMobThm`         [case k > r(1+eps)]
       |    <- Prop. `LinearFormsDistinctDerivatives`
       |         <- Lem. `PreparingMobiusToArithProgLem` (Pellet + Jacobi)
       |         <- Prop. `DerCongProp`
       |         <- Cor. `FFCSCor` <- Thm `main-character-sum` (Deligne)
       |         <- Prop. `BounNumSqArithProgProp`        ** not proved **
       |         <- the divisor bound                     ** see sec. 3 **
       <- SS Prop. 5.2 `MainTermPrimesLD` (main term)
```

**A structural simplification worth recording.** Bagshaw applies SS Thm 4.5
with `n = 1` -- a *single* linear form. At `n = 1` the whole pair machinery of
`LinearFormsDistinctDerivatives` (the polynomials `G_r^{(i,j)}`, `U_r`, the
`ell`-counting claim, the auxiliary prime `P` of degree `o(d)`) is vacuous:
there are no pairs `i < j`, so `U_r = 1` and `ell_r = 0`. What survives is
exactly the theorem SS wrote out and then commented out of the source
(`Geometric_Mobius.tex`, lines ~1000--1090): split `M_d` by `p`-th powers,
convert `mu` to a real character by Pellet + Jacobi, discard the `r` whose
character is principal (that is `BounNumSqArithProgProp`), and bound the rest
by `FFCSCor`. **On the Sawin--Shusterman branch, the Kaser--Lemire application
is three lemmas deep, not ten** -- the Bagshaw branch (Thm 2.3) is the long one.

### 1.2 Step-by-step effectivity

Classification: **(i)** explicit already, or immediately computable from the
paper's own inequalities; **(ii)** computable in principle, but the paper does
not write the constant and getting it needs real (routine) work; **(iii)**
genuinely ineffective.

| step | statement as given | class | why |
| --- | --- | --- | --- |
| SS `main-character-sum` | `<= (q^{1/2}+1) binom(m-1,t) q^{t/2}` | **(i)** | a literal inequality; Deligne + a rank count |
| SS `FFCSCor` | `<< q^{(1-beta)t}`, "implied constant depending only on `q`" | **(i)** | the proof's own chain gives the constant `q^{1/2}+1` verbatim |
| SS `PreparingMobiusToArithProgLem` | exact identity `mu(a+gM) = S chi(w+g)` | **(i)** | no constant |
| SS `DerCongProp` | `<= q^{-min(m, floor((d-1)/p))}` | **(i)** | exact |
| SS `BounNumSqArithProgProp` | `<< q^{(1/2+alpha)d}`, cited to BGP92 / CG07 | **(ii)** | **not proved in either paper**; see sec. 1.3 |
| SS `LinearFormsMobThm` (=Thm 4.5) | `<< abs(M_d)^{1-beta/p}`, "implied constant depending only on `eps, delta, beta, n` and `q`" | **(ii)** | assembled from the above plus the divisor bound |
| SS Prop. 5.2 (main term) | `= -q^m/phi(M) + q^{o(m+d)-d}` | **(ii)** | a divisor-type `o(.)`; explicit from the generating function |
| Bagshaw `lem:divisors` | `tau(x) = O_eps(q^{eps deg x})` | **(ii)** but catastrophic | finite for each `eps`, but `10^{341}` in the exponent at the `eps` the proof forces -- **sec. 3** |
| Bagshaw `lem:BLL`, `lem:Han` | literal inequalities | **(i)** | |
| Bagshaw `cor:Han+BLL`, `cor:mobius_arith` | `<<_eps q^{n(1/2+eps)}` | **(ii)** | assembled from two explicit lemmas plus a splitting argument |
| Bagshaw `lem:weil`, `lem:weil_incomplete` | `<<_eps q^{r/2+deg(a,b,F)/2+r eps}` | **(ii)** | inherits `lem:divisors`; the Weil input itself is explicit |
| Bagshaw Thms 2.1, 2.3 | `<<_eps` | **(ii)** | Holder + Cauchy--Schwarz + energies; every step is an inequality with a divisor-bound loss |
| Bagshaw Cor. 2.5 | `<<_omega q^{n-r(1+delta)}`, `delta = delta(omega) > 0` | **(ii)** | see sec. 2 for `delta`, sec. 3 for the constant |

**Nothing is class (iii).** No class number, no exceptional zero, no
compactness/normal-families argument, no unspecified "sufficiently large".
Every `<<` in the chain is an inequality between explicit quantities, or a
limit `d -> infinity` with a rate the same proof supplies.

### 1.3 The one input nobody proved

Verbatim, `Geometric_Mobius.tex`:

> The following technical proposition follows from the arguments of
> [BGP92, Page 371] or [CG07, Section 9] (see also [BZ02]), which obtain
> stronger statements over `Z` in place of `F_q[T]`.
>
> **Proposition** (`BounNumSqArithProgProp`). Fix `alpha, eps > 0`, and a
> prime power `q`. Then for integers `d, m, k >= 0` with `d >= eps(m+k)`, and
> `M in M_m`, `A in M_k`, `a in F_q[T]`, we have
> `#{g in F_q[T] : d(g) < d, a + gM = lambda A B^2, lambda in F_q, B in F_q[T]}
>  << q^{(1/2+alpha)d}` as `d -> infinity`, with the implied constant depending
> only on `eps, alpha` and `q`.

BGP92 is Bombieri--Granville--Pintz, *Squares in arithmetic progressions*
(Duke 66 (1992) 369--385); CG07 is Cilleruelo--Granville. Over `Z` those are
genuinely deep (Bombieri--Pila determinant method). **Over `F_q[T]` the
statement is elementary**, and that is the finding: `g` is determined by
`(lambda, B)`; `B` is pinned modulo `M` by `lambda A B^2 = a mod M`, a
congruence with at most `tau(M) q^{m/2}` solutions (the `q^{m/2}` only when `M`
is not squarefree and the residue is degenerate); and `deg B <= (d+m-1-k)/2`,
so the number of lifts of a fixed residue is `q^{max(0, deg B + 1 - m)}`.
Multiplying gives `q^{(d+1)/2} tau(M)` in the main range, which is
`q^{(1/2+alpha)d}` on taking the divisor bound at `gamma = alpha eps`. Check
C4.1 brute-forces the count over `F_3[T]` for every `(M, A, d)` in a small
sweep and confirms it never exceeds
`1 + (q-1) tau(M) q^{m/2 + max(0, DB+1-m)}`; C4.2 is the positive control that
the exponent `1/2` is doing work (some row exceeds `q^{0.4 d}`).

So this is class **(ii)**, not (iii) -- but note that the constant it
contributes carries a divisor bound, which is the very step sec. 3 indicts.

### 1.4 The oddness hypothesis is unchanged

Nothing here touches note 16's verdict that `p` odd is *mechanism*: SS's
`JacobiLem` needs the unique quadratic character of `F_q^x`. Effectivising
does not create a `p = 2` case, so **none of this touches the lane's actual
conjecture over `F_2`.**

## 2. The savings exponent `delta`, reconstructed

Bagshaw states Cor. 2.5 with an unnamed `delta = delta(omega) > 0`. It is
recoverable exactly from his proof (`Files/ProofVonMangoldt.tex`), which is
worth doing because `n_0` is `2 log_q(C)/delta` and therefore *inversely*
proportional to it.

### 2.1 The parameters

With `d = n - r` and `omega' = (2 omega - 1)/omega < 1/16`, he fixes
`theta > 0` and `beta in (0, 1/2)` "sufficiently small", sets

```text
eps = (16/15)(1/16 - omega' - 2 theta),
```

and gets two branches:

- `k <= r(1+eps)`: via Thm 2.3, `S_0 <<_theta q^{15r/16 + 15 r eps/16 + r theta}
  = q^{r - r omega' - r theta} <= q^{d - r theta}`;
- `k > r(1+eps)`: via SS Thm 4.5, `S_0 <<_{theta,beta} q^{d - r beta eps / p}`,
  valid as long as `q > (p e (eps+2)/eps)^{2/(1-2 beta)}`.

Verbatim, the sentence that hides the whole question:

> But since we fix `p` and `q`, we may choose `theta` and `beta` sufficiently
> small so that we only require `q > p^2 e^2 (1 + 30/(1-16 omega'))^2`.

Hence

```text
delta(omega; q, p) = max over (theta, beta) of min(theta, eps*beta/p)
    subject to  eps = (16/15)(1/16 - omega' - 2 theta) > 0
    and         beta < 1/2 - log(p e (2+eps)/eps) / log q.
```

The identity `(16-omega)/(16-31 omega) = 1 + 30/(1-16 omega') = (2+eps)/eps`
(at `theta = 0`) is check C2.1; it is what makes the two forms of the
`q`-hypothesis the same, and it re-derives note 16's `961 e^2` at `omega = 1/2`.

### 2.2 The optimum, and a hard cap

The two branches pull opposite ways: `theta` up raises the first saving and
lowers `eps`, hence `beta`, hence the second. The optimum is the crossing.
Measured (check C2.3, `data/effq-delta-tradeoff.txt`):

```text
q = 3^11 = 177147:  delta = 8.6302e-04  at theta = 8.631e-04, beta = 0.03994,
                    eps = 0.064825      =>  n_0 = 2317.5 * log_q C.
```

(Where `n_0 = 2 log_q(C)/delta` comes from: the main term of Cor. 2.5 at
`F = T^r` is `q^n/phi(T^r) = q^{d+1}/(q-1)` and the error is `C q^{d - r delta}`,
so positivity of the von Mangoldt sum needs `r delta > log_q C + O(1)`, i.e.
`n >= 2r > 2 log_q(C)/delta`. The step from a positive `Lambda`-sum to an
actual irreducible costs nothing: note 16 sec. 3 step 5 bounds the proper
prime-power contribution by `O(n q^{n/(2p)})`, which at `p = 3` is `q^{n/6}`
against a main term of size `q^{n/2}`.)

A cap that does not depend on `q` at all: `eps <= 1/15` and `beta < 1/2`, so

```text
delta < 1/(30 p)      (check C2.2; = 0.011111 at p = 3)
n_0 > 60 p * log_q C  (= 180 log_q C at p = 3, for EVERY q).
```

Per extension degree at `p = 3` (excerpt; full table in the data file):

| `l` | `q = 3^l` | `delta` | `beta` | `n_0 / log_q C` |
| --- | --- | --- | --- | --- |
| 11 | 177147 | 8.630e-04 | 0.0399 | 2317.5 |
| 12 | 531441 | 1.611e-03 | 0.0764 | 1241.3 |
| 14 | 4782969 | 2.728e-03 | 0.1345 | 733.0 |
| 17 | 129140163 | 3.839e-03 | 0.1970 | 521.0 |
| 20 | 3486784401 | 4.575e-03 | 0.2412 | 437.1 |
| 30 | 2.0589e14 | 5.881e-03 | 0.3260 | 340.1 |

And across characteristics, each at its own smallest admissible `q`
(table (c) in the data file): `p = 3` gives `n_0/log_q C = 2317`, `p = 5` gives
`5118`, `p = 7` gives `6847`, `p = 11` gives `13358`, `p = 13` gives `8778`,
`p = 23` gives `40471`. **`p = 3` is the best characteristic**, by the `1/p` in
`eps*beta/p` and by `p` inside the `q`-threshold; this is not close.

### 2.3 The `omega` trade-off, and why the brief's premise is inverted

The brief anticipates that "constants blow up as `omega -> 1/2`, so there is a
genuine trade-off between how close to `1/2` you push and how large `n_0`
becomes". **That is backwards, and the check is a positive control (C2.4).**
Both quantities are monotone the other way on `[1/2, 16/31)`:

- `g(omega) = e^2((16-omega)/(16-31 omega))^2`, the `q`-threshold, is strictly
  *increasing*; its minimum is `g(1/2) = 961 e^2 = 7100.883`;
- `delta(omega)` is *decreasing* -- larger `omega` means larger `omega'`,
  smaller `eps`, smaller `beta`.

So `omega = 1/2` is optimal in both directions simultaneously, and there is no
trade-off of the shape the brief expects. What is real is different and much
milder: **even `n` can use `omega = 1/2` exactly (`r = n/2`), odd `n` needs
`omega >= (n+1)/(2n)`, so `delta` for odd `n` depends on `n`** and rises to the
even-`n` value. At `q = 3^11` (table (b)):

| odd `n` | `omega = (n+1)/2n` | `delta` | `n_0 / log_q C` |
| --- | --- | --- | --- |
| 79 | 0.5063291 | 1.243e-05 | 160915 |
| 101 | 0.5049505 | 1.699e-04 | 11774 |
| 201 | 0.5024876 | 4.921e-04 | 4064 |
| 401 | 0.5012469 | 6.718e-04 | 2977 |
| 841 | 0.5005945 | 7.706e-04 | 2595 |
| 3201 | 0.5001562 | 8.385e-04 | 2385 |
| even | 0.5 | 8.630e-04 | 2318 |

The window's own constraint is the largest admissible `omega`,
`omega_max(3^11) = 0.506445` (from `q > p^2 e^2 g`), which admits every odd
`n >= 78` (check C2.5). By `n = 841` the odd-`n` penalty on `delta` is already
down to 11%. **The window costs essentially nothing; every remaining factor of
`n_0` is the implied constant.**

### 2.4 The slack trade-off, and why slack is not a lever

Allow `k` coefficients of slack, i.e. window `deg(f - T^n) <= floor(n/2) + k`,
so `r = ceil(n/2) - k` and `omega < 1/2` becomes available (`omega'` goes
negative, `eps` grows, `delta` grows). At `q = 3^11`, `n = 1001`: `delta` goes
`7.85e-04` (`k=0`), `9.42e-04` (`k=1`), `1.63e-03` (`k=5`), `2.60e-03`
(`k=10`) -- table (d) of `data/effq-delta-tradeoff.txt`. A genuine gain -- and
**entirely pointless**, because the *other* end
moves far faster. Hsu/Cohen with slack `k` and odd `n` is positive iff
`((n+1)/2 - k)^2 < q^{2k+1}`, i.e. `n < 2 q^{k+1/2} + 2k - 1` (check C1.4):

| slack `k` | Hsu/Cohen odd reach at `q = 3^11` |
| --- | --- |
| 0 | **839** |
| 1 | 149118215 |
| 2 | 26415844564135 |
| 3 | 4.68e18 |

One coefficient of slack turns the residual problem into nothing at all. The
gap therefore exists at, and only at, the exact endpoint -- the `~log_q n`
deficiency that note 00 calls Barrier III. Any "we can do `(1/2 - eps)n`
coefficients" statement, however strong, is on the wrong side of this line.

## 3. What actually blocks: the pointwise divisor bound

### 3.1 `n_0(3^11) ~ 10^{344.5}` from the argument as written

Bagshaw's Lemma (from Cilleruelo--Shparlinski):

> The number of divisors of any `x in F_q[T]` is `O_eps(q^{eps deg x})`.

It is used pointwise: in `lem:mobius_bound_bigr0` the Vaughan weights satisfy
"`abs(beta_y) <<_eps q^{n eps}`"; in `lem:weil_different_modulus`,
`lem:inverse_energy_k=2` and throughout Thms 2.1--2.3 each `q^{eps n}` is a
pointwise divisor loss; in SS it appears as `d_2(M_1 Q)` and `2^Gamma`.

The trouble is the value of `eps` the *same* proof then demands. In Cor. 2.5's
proof the surviving budget is `theta`, and sec. 2 optimises it to
`theta = 8.63 * 10^{-4}` at `q = 3^11`. The extremal constant in
`tau(x) <= C q^{gamma deg x}` at that `gamma` is what check C3.3 computes:

```text
max over m of  [ log_q max_{deg x = m} tau(x)  -  gamma m ].
```

The maximiser over all `m` is the `x` that is the product of every monic
irreducible of degree `<= J`: a fresh irreducible of degree `j` multiplies
`tau` by `2` at a cost of `j` in degree, so degree class `j` is worth taking
exactly while `2^{1/j} > q^gamma`. That gives
`J = floor(log 2 / (gamma log q)) = 66` and

```text
log_q C_div(3^11, 8.63e-04) ~ 10^{341.2},   hence
n_0(3^11) = 2 log_q(C)/delta ~ 10^{344.5}.
```

For orientation, the pointwise maximum is exactly `2^m` for `m <= q` (check
C3.2; the positive control is that this *fails* once `m > q` -- over `F_2` at
`m = 3` the maximum is `6`, not `8`, because there are only two linear monics).

### 3.2 The exact identity that fixes it

Over `F_q[T]` the *averaged* divisor sum is an identity, not an estimate:
`sum_{k} (sum_{x monic, deg x = k} tau(x)) u^k = zeta(u)^2 = (1-qu)^{-2}`, so

```text
sum_{x monic, deg x = m} tau(x) = (m+1) q^m       (check C3.1, brute-forced).
```

No `eps`, no constant. Every pointwise `q^{eps n}` in the chain sits inside a
sum over the very variable it bounds (`sum_y beta_y ...`, `sum_{d | F} ...`,
`sum_{deg x <= u} tau(x) |...|`), so each can be replaced by this identity at
a cost of a factor `m+1`. **That rewrite -- Bagshaw secs. 4--5 and SS sec. 4,
recast with averaged divisor sums -- is the entire remaining obstacle to an
explicit `n_0`.** It is bounded work with no new ideas in it. It is also not
something this note can do in passing, so no explicit `n_0` is claimed here.

### 3.3 It is not a large-`q` artefact

One might hope the catastrophe evaporates at larger `q`, since `log 2/log q`
shrinks. It does not, because `delta(q)` shrinks with it. Check C3.4 and
`data/effq-divisor-audit.txt`:

| `l` | `log10(log_q C_div)` | best `J` | `log10(n_0` as written`)` | `K_max` (sec. 6) |
| --- | --- | --- | --- | --- |
| 11 | 341.17 | 66 | 344.54 | 0.36 |
| 14 | 102.82 | 16 | 105.69 | 5.96 |
| 20 | 54.09 | 6 | 56.73 | 270.2 |
| 30 | 39.99 | 3 | 42.53 | 84385 |

`n_0` as written is `10^{42}` even at `q = 3^30`, against a budget of
`10^{4.9}`. **The divisor step has to be rewritten whichever `q` you choose.**

## 4. The Hsu/Cohen end, exactly

Prescribing the top `L` coefficients (below the leading one), the Hayes/Weil
count in its sharp form (Hsu 1996 Thm 2.4 = Cohen 2005 Thm 2.1) is
`I_q(n; L) >= q^{n-L}/n - (L+1) q^{n/2}/n`, and with `L = ceil(n/2) - 1` this
is exactly the Kaser--Lemire window. Positivity is, in exact integer
arithmetic and with no square roots (check C1.1),

```text
q^{n - 2L} > (L+1)^2,
```

which for `L = ceil(n/2)-1` reads

```text
even n:  n - 2L = 2,  so  q > n/2         =>  n <= 2q - 2,
odd  n:  n - 2L = 1,  so  q > ((n+1)/2)^2 =>  n <= 2 floor(sqrt(q-1)) - 1.
```

At `q = 3^11 = 177147` (check C1.2; `n+2` fails in both cases):

```text
even n <= 354292      odd n <= 839.
```

Positive control C1.3: for small `(q, n)` where the bound is positive an
in-window irreducible is found by exhaustive search; and at `q = 3, n = 5` the
bound is *negative* while a witness exists, so a failure of the bound is not a
failure of the conjecture -- the criterion is sufficient only.

**Exact gap at `q = 3^11`:** even `n` is covered by Hsu/Cohen out to `354292`
and by Bagshaw from `n_0` on, so if `n_0 <= 354292` the even case is complete.
The odd case leaves

```text
odd n in [841, n_0),
```

with `n_0` unknown, `>= 180 log_q C` in all cases (sec. 2.2) and `~10^{344.5}`
from the argument as written (sec. 3.1).

## 5. How much of the gap is closed computationally

Direct construction, at `q = 3^11`, of a monic irreducible `f` of odd degree
`n` with `deg(f - T^n) <= floor(n/2)`, for `n` above the Hsu/Cohen reach.
The window holds `q^{floor(n/2)+1}` polynomials of which about `1/n` are
irreducible, so a randomised search needs `O(n)` trials.

**The subfield shortcut.** `11` is prime, so the only proper subfield of
`F_{3^11}` is `F_3`, and a degree-`n` irreducible over `F_3` factors over
`F_{3^11}` into `gcd(n, 11)` factors of equal degree. Hence:

- if `11` does not divide `n`, an in-window irreducible over `F_3` **is** an
  in-window irreducible over `F_{3^11}` -- and the search runs in `F_3[T]`,
  which is two orders of magnitude cheaper;
- if `11` divides `n`, no `F_3` witness can work and the search must run in
  `F_{3^11}[T]` directly.

Check C5.1 is the positive control on both halves of that lemma (a random
`F_3`-irreducible of degree `5, 7, 9, 13, 21` stays irreducible; one of degree
`11, 22, 33` splits into exactly `11` equal factors).

**Method.** Random monic `f = T^n + g`, `deg g <= floor(n/2)`; reject on a root
in the ground field; reject on a factor of degree `<= 6` (`F_3` route, by
iterated Frobenius `x -> x^3` and `gcd`) or `<= 8` (`F_{3^11}` route, by
modular composition with `x^q mod f`); then a full irreducibility test. The
filter removes about `90%` of candidates at a small fraction of the cost.

**Certificate scheme.** `data/effq-witnesses-3p11.txt` stores, per `n`, the
carrier (`F3` or `F3^11`) and the tail `g` as one integer: its coefficient
vector written in base 3 (low degree first, `11` trits per `F_{3^11}`
coefficient) and printed in hex. Verification (check C5.2) decodes it, checks
monicity, degree, and the window, and then re-establishes irreducibility by
**two independent routines**: flint's `factor()` (must return one factor of
degree `n` and multiplicity 1) and a hand-rolled Rabin test
(`x^{q^n} = x mod f` plus `gcd(x^{q^{n/pr}} - x, f) = 1` for every prime `pr |
n`) that shares no code with it. For `F_3` witnesses C5.2 additionally refuses
the row if `11 | n`. C5.3 checks that the covered odd range is contiguous and
C5.4 that it starts at `841`, immediately above the Hsu/Cohen reach.

**Coverage.** See `data/effq-witness-summary.txt` for the exact set. The
contiguous odd range certified here is recorded there; beyond it the `F_3`
route continues cheaply for `n` not divisible by `11`, while the `11 | n` rows
cost `O(n^{3.2})` and are the binding constraint. A row marked `MISS` is an
`n` for which the search budget was exhausted, not an `n` for which no witness
exists.

**A free corollary, and a structural remark.** Every `F3`-carrier row is *also*
a Kaser--Lemire witness over `F_3` itself, for that `n`. The lane's certified
finite handoff (note 00, `n <= 3000`) is over `F_2`; this is the `F_3` analogue
over the searched range. More generally the subfield lemma says: **for every
`n` coprime to `11`, Kaser--Lemire over `F_{3^11}` is implied by Kaser--Lemire
over `F_3`** -- so the genuinely `F_{3^11}`-specific part of the conjecture is
the set `11 | n`, of density `1/11`. The same holds for any `q = p^l` with `l`
prime and any `n` coprime to `l`. That is a small structural gain over note 16,
and it is the reason the computational end is affordable at all.

## 6. Which `q` is the right target

Write `C(q)` for the implied constant in Bagshaw Cor. 2.5 at the optimal
`(theta, beta)` for that `q`. Then `n_0(q) = 2 log_q(C(q)) / delta(q)`, and the
Bagshaw and Hsu/Cohen ranges meet with **no gap at all** exactly when

```text
n_0(q) <= (odd Hsu/Cohen reach)  <=>  log_q C(q) <= K_max(q),
K_max(q) := delta(q) * (2 floor(sqrt(q-1)) - 1) / 2.
```

`K_max` grows like `q^{1/2}` (the reach) times a factor that saturates at
`1/(30p)`, so it grows without bound; whether the gap closes is entirely a
question of how big `C(q)` is. Computed (check C2, column `K_max`):

| `q = 3^l` | odd reach | `delta` | `K_max` | i.e. gap closes if `C <=` |
| --- | --- | --- | --- | --- |
| `3^11` | 839 | 8.630e-04 | 0.362 | `q^{0.36} = 10^{1.9}` |
| `3^12` | 1455 | 1.611e-03 | 1.172 | `10^{6.7}` |
| `3^13` | 2523 | 2.221e-03 | 2.802 | `10^{17.4}` |
| `3^14` | 4371 | 2.728e-03 | 5.963 | `10^{39.8}` |
| `3^16` | 13119 | 3.523e-03 | 23.11 | `10^{176}` |
| `3^17` | 22725 | 3.839e-03 | 43.62 | `10^{354}` |
| `3^20` | 118095 | 4.575e-03 | 270.2 | `10^{2578}` |

Solving `n = (2/delta)(B + A log_q n)` for the illustrative shape
`C = q^B n^A`, the smallest `l` at which the gap closes is:

```text
     B =   0    1    2    3    5   10   20
A=0:      11   12   13   14   14   15   16
A=2:      12   13   14   14   15   15   16
A=4:      13   14   14   14   15   16   16
A=6:      14   14   14   15   15   16   17
A=8:      14   14   15   15   15   16   17
```

So:

- **`q = 3^11 = 177147` is the smallest admissible `q`, but the worst target**:
  it needs `C <= 10^{1.9}`, which no argument of this kind will give.
- **`q = 3^14 = 4782969` is the first `q` at which the two ranges plausibly
  meet** (`C <= 10^{39.8}` suffices).
- **`q = 3^17 = 129140163` closes the gap for every constant shape in the grid
  above** (`C <= 10^{354}`), and `q = 3^20` for anything up to `10^{2578}`.

Note also, from sec. 2.2 table (c), that no other characteristic competes: at
`p = 5, 7, 11, 13, 23` the factor `n_0/log_q C` is 2 to 17 times worse than at
`p = 3`, and their smallest admissible `q` are all larger.

**Does a better constant than `961 e^2` bring `q = p^2` or a prime field into
range?** No, and for a structural reason. The `31` in `961 = 31^2` is
`(2+eps)/eps` at `eps = 1/15`, and `1/15 = (16/15)(1/16)` is exactly the
savings `q^{r/16}` that Bagshaw Thm 2.3 delivers at `n ~ r`. If that savings
were improved from `1/16` to `1/c`, the same proof would give
`eps = 1/(c-1)` at the endpoint, hence `(2+eps)/eps = 2c - 1` and threshold

```text
q > (2c-1)^2 e^2 p^2,   c -> 1  giving  q > e^2 p^2 = 7.389 p^2.
```

(The limit is a consistency check: `q > p^2 n^2 e^2` at `n = 1` is exactly
Sawin--Shusterman's own `ChowlaThm` hypothesis.) But `q = p^l > e^2 p^2` still
forces `p^{l-2} > 7.389`, so `l >= 3` regardless. **No improvement of the
exponent in Thm 2.3, however large, can admit a prime field or a quadratic
extension**; the threshold is a condition on `q/p^2` and the constant stays
above `1`. Only a proof that drops the `p^2` -- i.e. that removes the
Artin--Schreier `p`-th-power splitting `g = r + s^p` from SS's method -- could.

## 7. The theorems that can actually be stated

**Theorem A (unconditional, `q = 3^11`).** Let `q = 3^11 = 177147`. For every
even `n` with `2 <= n <= 354292`, and for every odd `n <= 839`, there is a
monic irreducible `f in F_q[T]` of degree `n` with
`deg(f - T^n) <= floor(n/2)`. *(Hsu 1996 Thm 2.4 = Cohen 2005 Thm 2.1; the
threshold arithmetic re-derived exactly in check C1.)*

**Theorem B (unconditional, computational, `q = 3^11`).** The same conclusion
holds for every odd `n` in the certified range recorded in
`data/effq-witness-summary.txt`, by exhibited and independently re-verified
witnesses (sec. 5). Every witness with `F3` carrier is simultaneously a
Kaser--Lemire witness over `F_3`.

**Theorem C (conditional on a size bound, `q = 3^l`).** Suppose the implied
constant `C` in Bagshaw arXiv:2401.10399 Cor. 2.5, at the parameters
`(omega, theta, beta)` optimal for `q` (sec. 2), satisfies `C <= q^{K}` with
`K <= K_max(q)` from sec. 6. Then `n_0(q)` is at most the odd Hsu/Cohen reach,
which is itself below the even reach, so every `n < n_0` is covered by
Hsu/Cohen and every `n >= n_0` by Cor. 2.5: **Kaser--Lemire holds over `F_q`
for every `n >= 1`**, with no residual interval and no computation. In
particular `K <= 5.96` suffices at `q = 3^14` and `K <= 43.6` at `q = 3^17`.

**What is *not* proved.** No explicit `n_0(q)` for any `q`. Theorem C's
hypothesis is not verified for any `q`; sec. 3 shows it is *false* for the
argument as literally written (which gives `K ~ 10^{341}` at `q = 3^11`) and
gives the specific rewrite that would make it true. The residual interval at
`q = 3^11` is odd `n` from just above the certified range up to `n_0`, and
`n_0` is not known.

## 8. Work list, in dependency order

1. **Recast every pointwise divisor bound as an averaged one.** Bagshaw
   `lem:mobius_bound_bigr0` (the Vaughan weights), `lem:weil_different_modulus`,
   `lem:inverse_energy_k=2`, and the `q^{eps n}` factors in Thms 2.1--2.3; SS's
   `d_2(M_1 Q)` and `2^Gamma`. Tool: `sum_{deg x = m} tau(x) = (m+1) q^m`, and
   for our modulus `F = T^r` the even simpler `tau(T^r) = r+1`,
   `omega(T^r) = 1`. Expected output: `C = q^{O(1)} n^{O(1)}`.
2. **Write out `BounNumSqArithProgProp` over `F_q[T]`** by the square-root
   count of sec. 1.3, with the degree normalisation the application supplies.
   This is a short lemma and removes the only citation to an unproved input.
3. **Make `cor:Han+BLL` explicit** from `lem:BLL` and `lem:Han`, both of which
   are already literal inequalities, and propagate through `cor:mobius_arith`.
4. **Make Bagshaw2023 Lem. 5.3 and Lem. A.13 explicit** (arXiv:2304.05014) --
   the only external inputs left after 1--3.
5. **Then compute `n_0(3^14)` and check it against `4371`.** If it lands below,
   Kaser--Lemire is a completely proved theorem over `F_{3^14}` for all `n`.
6. Only then is it worth extending the sec. 5 witness search; below `3^14` the
   gap is not closable by computation anyway (sec. 6).

## 9. Reproducibility

- Checker: `scripts/lemire-signed-trace/lemire_effective_largeq.py`
  (`/data0/axeyum/scratch/lemire-signed-trace-lemire-venv/bin/python`). Exits
  nonzero on failure. Five check groups; five of the individual checks are
  positive controls (C1.3, C2.4, C3.2, C4.2, C5.1) and one is an adversarial
  fixture (C4.3).
- Search mode: `--search LO HI BUDGET [PROCS [FLAGS]]` regenerates
  `data/effq-witnesses-3p11.txt`, merging with what is already there. `FLAGS`
  is a comma list of `skip11` (leave `11 | n` alone -- those rows are the
  expensive ones) and `onlymiss` (retry only the `n` with no witness yet).
- Data: `data/effq-hsu-cohen-reach.txt`, `data/effq-delta-tradeoff.txt`,
  `data/effq-divisor-audit.txt`, `data/effq-bounnumsq-control.txt`,
  `data/effq-witnesses-3p11.txt`, `data/effq-witness-summary.txt`.
- Mutation controls performed out of tree (a copy under the session scratch
  dir, never the shared checkout); see sec. 10.
- Runtime of the checker: about 6 minutes, most of it CHECK 5 (parallelised).
- Primary sources read as LaTeX: arXiv:2401.10399 `Files/Results.tex`,
  `ProofVonMangoldt.tex`, `CharSums.tex`, `Proofsetup.tex`, `mobius1.tex`,
  `mobius2.tex`, `forms.tex`, `energy.tex`, `IrvingProof.tex`, `Weil.tex`,
  `divisor.tex`, `comments.tex`; arXiv:1808.04001 `Geometric_Mobius.tex`
  (secs. "Character sums", "The Mobius Function", "Linear forms in Mobius",
  "Level of distribution", bibliography).
- Not verified from primary sources: Hsu 1996 Thm 2.4, Cohen 2005 Thm 2.1
  (taken, as in note 16, from the lane's diary literature section); Bagshaw
  arXiv:2304.05014 Lem. 5.3 and A.13; Cilleruelo--Shparlinski Lem. 1;
  Bombieri--Granville--Pintz and Cilleruelo--Granville.

## 10. Mutation controls

Performed on a copy under the session scratch directory -- never in the shared
checkout, per the repository's rule about in-place mutants breaking sibling
lanes' builds. Baseline: all checks pass. Each mutation below kills **exactly
one** named check and leaves the rest green.

| mutation | subject | dies |
| --- | --- | --- |
| `hsu_cohen_positive` ignores its `slack` argument (`- slack` -> `- min(slack,0)`) | the slack arithmetic | C1.4 only |
| `eps_of` drops the `- 2*theta` term | Bagshaw's `eps` | C2.3 only |
| `omega_max` uses `31R + 1` instead of `31R - 1` | the `q`-threshold inversion | C2.5 only |
| `tau_sum_bruteforce` multiplies by `e` instead of `e + 1` | the divisor oracle | C3.1 only |
| `bounnumsq_bound` drops the `q^{m/2}` allowance | the degenerate-square-root case | C4.3 only |
| one witness's tail in `effq-witnesses-3p11.txt` replaced by `0x0` (so `f = T^n`) | a witness | C5.2 only |
| one row deleted from `effq-witnesses-3p11.txt` | witness coverage | C5.3 only |

Two of these deserve a note.

**`bounnumsq_bound` was removable until C4.3 was written.** The `q^{m/2}`
factor exists only for a non-squarefree `M` -- and `T^r`, the modulus the whole
application rests on, is the extreme non-squarefree case. The parameter grid in
C4.1 (including `T^2`, `(T+1)^2`, `T^3` as moduli) *never reaches* the case:
deleting the factor left every one of its rows still satisfied. C4.3 is the
adversarial fixture found by scanning for a case that needs it
(`M = T^3`, `A = T`, `a = 0`, `d = 5`: count `27` against `25` without the
allowance, `73` with). This is the CLAUDE.md failure mode exactly -- a guard
whose grid does not distinguish the case the producer distinguishes.

Note also that a *single-hex-digit* corruption of a witness is **not** a
reliable control: at small `n` the perturbed polynomial is often still an
in-window irreducible, so the check correctly passes. Measured: flipping the
last hex digit of an `n = 11` witness left it irreducible; the same flip at
`n = 33` broke it. The control therefore zeroes the tail, which is
deterministic (`T^n` is never irreducible for `n > 1`).

**`omega_max` and `eps_of` both feed `delta`, so they are not independent by
construction** -- what makes each kill exactly one check is that C2.5 reads
`omega_max` only and C2.3 pins `delta` to four digits. A cruder pair of checks
(say "delta > 0" and "omega_max > 1/2") would have survived both mutations.

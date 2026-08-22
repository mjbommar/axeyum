# Lemire signed-trace lane: mechanism hunt, rung 2

Status: research note, 2026-08-21. Nothing here is a proof. This note records
what the exact data say about the open layers, four further exact
reformulations of the target found while looking for a mechanism, and the
shortcuts that the data or a two-line argument kill. It is written so that no
idea here has to be re-derived or re-refuted.

Companion: [01-target-and-toolkit.md](01-target-and-toolkit.md) (target,
formulations, literature, tooling). Data: `scripts/lemire-signed-trace/data/` (layer, cylinder and twisted-sum tables to `ell = 24`).

## 1. What the exact layer data say (`ell <= 24`)

Source: class-population dumps of the branch CAS
(`axeyum-gf2-dump-populations`, source in `scripts/lemire-signed-trace/`),
analysed by `lemire_layers.py`. The ratio is
`|T_{j,s}| / (#X_{j,s} (j-1) 2^{ceil(n/2)})`; `(HWO)` asks `<= 1/(4 ell)`.

```text
worst ratio over a <= j <= ell, relative to the threshold 1/(4 ell)
ell  n    orders >= 2^3      orders >= 2^4
12   25   2.20 x             2.20 x
14   29   1.81 x             1.17 x
14   30   3.54 x             3.54 x
16   33   0.92 x             0.92 x
16   34   0.98 x             0.96 x
18   37   0.53 x             0.53 x
18   38   0.53 x             0.46 x
20   41   0.45 x             0.45 x
20   42   0.46 x             0.16 x
22   45   0.23 x             0.23 x
22   46   0.22 x             0.22 x
23   47   0.21 x             0.10 x   (orders >= 2^5: 0.04 x)
23   48   0.81 x             0.81 x   (orders >= 2^5: exact zero at (17,5))
24   49   0.19 x             0.19 x   (orders >= 2^5: 0.03 x; all orders 0.60 x)
24   50   0.12 x             0.12 x   (orders >= 2^5: 0.12 x; all orders 1.17 x at (23,1))
```

Orders `2` and `4` sit at `1--3 x` threshold throughout; for `ell >= 200`
those orders are `<= Q` and already paid by Weil, so they are not part of the
open statement. The open high-order layers satisfy the needed bound with a
margin that grows with `ell`. Inside a layer the sparse imbalances are at the
square-root scale of their populations (`|Delta_{j,s}| ~ 10^3 -- 10^4` against
populations `10^6 -- 10^9` at `ell = 20`), i.e. the data follow the random
model; the allowance is larger by a factor that grows like `2^{ell/2}/ell`.
So `(HWO)` is not delicate; a proof needs any uniform power saving over the
trivial bound on the four-term alternating sums, of strength about
`population^{1-0.055}` across the window, and no known method gives any power
saving at this scale.

Exact reduction, corrected. With `q = 2^s`:

```text
q does not divide j, q/2 does not divide j:  T = h_{j-1,s} Delta_{j,s} - h_{j-1,s-1} Delta_{j,s-1}
q does not divide j, q/2 divides j:          T = h_{j-1,s} Delta_{j,s}
q divides j:                                  layer empty
```

The first unconditional two-term form fails in the resonant middle case
(`(j,s) = (7,1)` is the first counterexample; the analyzer asserts the correct
form on every row). Resonant rows occur in the target range (`j = 200`,
`q = 16`). The naive "squaring" recursion `chi -> chi^2` does not map the
layer `X_{j,s}` onto `X_{floor(j/2),s-1}` (the conductor of `chi^2` can drop
below `j/2` when `j` is odd), so there is no clean tower recursion beyond the
four-population identity; `T_{17,3} != 0` at `(ell,n)=(20,41)` witnesses that
the would-be recursion is wrong.

### 1.1 The one-sided route, measured: no cylinder is special

`lemire_cylinders.py` evaluates the branch's `(ICV)` object directly. With
`a = ell - ceil(log2 ell) - 1` and `K = ker(E_ell -> E_{a-1})`
(`|K| = 2^{ell-a+1}`, elementary abelian since `a > ell/2`), put
`SSD_h = sum_{g in hK} (N(g) - mean_{hK})^2` for each of the `2^{a-1}`
cylinders `h`. `(REL)` follows from `SSD_1 < 2^{2 ell - 2}` (identity
cylinder). Measured (`data/cylinder-variances-ell12-24.txt`):

```text
ell n   a  |K| cylinders  SSD_id/avg  rank of id   max/avg  SSD_id/2^{2ell-2}  avg/SatoTate
14 29   9  64      256     0.82       215/256      1.62     0.30              0.84
16 33  11  64     1024     1.23        91/1024     1.62     0.13              0.87
18 37  12 128     2048     1.15       265/2048     1.44     0.072             0.89
18 38  12 128     2048     0.93      1444/2048     1.49     0.12              0.88
20 41  14 128     8192     1.09      1869/8192     1.59     0.019             0.90
20 42  14 128     8192     1.18       664/8192     1.77     0.042             0.90
22 45  16 128    32768     1.03     12773/32768    1.59     0.0050            0.90
22 46  16 128    32768     1.05     10742/32768    1.69     0.010             0.90
23 47  17 128    65536     0.96     39139/65536    1.63     0.0025            0.91
23 48  17 128    65536     1.12     10904/65536    1.74     0.0057            0.91
24 49  18 128   131072     0.92     94045/131072   1.59     0.0012            0.91
24 50  18 128   131072     1.09     29889/131072   1.78     0.0029            0.91
```

Three facts. (i) The identity cylinder is typical: within 25% of the average
and ranked mid-pack every time. (ii) The average matches the diagonal
(Sato--Tate) prediction `ell 2^{n-a+1}` to within 10--16%, i.e. the second
moment is at its random value and the off-diagonal pair term is small
(`-10%`). (iii) The maximum over all cylinders is at most `1.8 x` the
average: the variance is spread uniformly, so the required statement "the
identity cylinder carries at most a `1/(16 ell^2)` fraction of the total
variance" holds with a margin `2^{a-1}/(16 ell^2 x 1.8)`.

The same dump gives the twisted cylinder sums
`A_psi^{(h)} = sum_{g in hK} N(g) psi(g h^{-1})`, `psi in K^dual`, i.e. the
prime mass of the cylinder interval twisted by a sign character of the
`log2 ell + 2` middle coefficients; `(REL)` follows from
`|A_psi^{(1)}| < 2^{ell-1}` for every `psi != 1`, and every class then lies
within `2^{ell-1}` of its cylinder mean. Measured at `(ell,n) = (20,41),
(20,42), (22,45)`: the rms of `A_psi` over cylinders equals the random-phase
prediction `2^{(n-a+1)/2} sqrt(ell)` to three digits (e.g. `72787` vs
`73271`); the maximum over all `(h, psi)` is `0.63, 0.94, 0.36` of the
threshold `2^{ell-1}`, consistent with Gaussian tails over
`2^{a-1}(|K|-1)` samples; the identity cylinder's maximum is `0.46, 0.61,
0.20` of threshold. Weil gives `(ell-1) 2^{ceil(n/2)}`, i.e. `76 x`, `76 x`,
`84 x` the threshold. So the minimal true statement is a uniform
`1/(16 ell)`-relative equidistribution of primes in a `16 ell sqrt(X)`-long
interval against sign patterns of the next `log2 ell + 2` coefficients, and
it holds for every cylinder with margin growing like `2^{ell/2}/ell`.

The full sweep (`lemire_twists.py`, exact Walsh transforms,
`data/twisted-sums-ell14-24.txt`), reported as `max |A_psi| / 2^{ell-1}`:

```text
ell n   rms/random-phase   identity cylinder   sup over all cylinders
14 29   0.923              1.31                2.51
14 30   0.933              2.42                2.91
16 33   0.940              0.92                1.50
16 34   0.939              1.21                2.32
18 37   0.945              0.81                1.18
18 38   0.944              0.87                1.71
20 41   0.951              0.46                0.63
20 42   0.951              0.61                0.94
22 45   0.954              0.20                0.36
22 46   0.954              0.30                0.50
23 47   0.957              0.15                0.27
23 48   0.957              0.23                0.41
24 49   0.959              0.09                0.21
24 50   0.959              0.15                0.31
```

The identity-cylinder statement of the open fact
`F:gf2-lemire-cylinder-twist-sup-bound` holds from `ell = 16` (odd) and
`ell = 18` (even) on; the uniform-in-cylinder version holds from `ell = 20`;
both margins double roughly every two steps of `ell`, as the random model
(`2^{ell/2}/ell` against Gaussian tails over `2^{a-1}(|K|-1)` samples)
predicts.

## 2. Four further exact reformulations

### 2.1 Type I is exact; the top layer is a second difference of Moebius interval sums

Let `h = n - j` and `Phi(y) = sum_{deg r < h} Lambda(x^n + y + r)` (prime mass
of the short interval `x^n + y + I(h)`). The top layer at conductor `j`,
`m = floor(log2 j)`, is the mixed second difference

```text
T_top  prop.  Phi(0) - Phi(x^h) - Phi(x^{n-2^m}) + Phi(x^{n-2^m} + x^h).
```

Writing `Lambda = mu * deg`, every divisor `d` with `deg d <= h` contributes to
`Phi(y)` a count that is independent of `y` (the cofactors form a full
interval), so

```text
Phi(y) = C + sum_{deg e < j} deg(e) . M(I_{y,e}),    M(I) = sum_{d in I} mu(d),
I_{y,e} = { d : d e in x^n + y + I(h) }   (an interval of length 2^{h - deg e}).
```

All `y`-dependence, hence the whole layer, lives in Moebius sums over intervals
shorter than the square root of their location; this is exact but gives no
bound (those sums are below the Weil range). Checked by
`scripts/lemire-signed-trace/lemire_typeI_check.py`: at `(n,j) = (11,5),
(13,6), (15,7)` the difference `Phi(y) - RHS(y)` is the constant `2^h` on
all four top-layer shifts, and the mixed second differences agree
(`46 = 46` at `(15,7)`).

### 2.2 Witt-vector geometry: Teichmueller curve against the trace-zero subgroup

The reciprocal of the class condition is `charpoly(beta) = 1 mod x^{ell+1}`
with `beta = alpha^{-1}`, i.e. `N(1 + gamma x) in U^{(ell+1)}` for the norm
from `1 + x F_{2^n}[[x]]` to `1 + x F_2[[x]]`, `gamma = beta^{-1}`. Under
Katz's splitting over `F_{2^n}`, `1 + gamma x` is the point
`([gamma^k])_{k odd <= ell}` of the "Teichmueller curve" in
`prod_k W_{e_k}(F_{2^n})`, and the norm is the coordinatewise Witt trace. So

```text
N_ell(1) - 1 = #( Teichmueller curve  intersect  ker(Witt trace) ),
```

a curve of `2^n - 1` points against a subgroup of index `2^ell` in a group
isomorphic to `prod_k (Z/2^{e_k})^n`. Local class field theory says the norm
is surjective and its kernel is `(sigma - 1)`-torsors; this explains the
structure but supplies no count.

### 2.3 Power-map pullbacks (n prime)

For `n` prime every odd `k <= ell` is coprime to `2^n - 1`, so `t -> t^k` is a
bijection of the Teichmueller group `T` and

```text
A = intersection over odd k <= ell of  (H_{e_k})^{1/k},
H_e = { t in T : Tr_{GR(2^e,n)}(t) = 0 mod 2^e },   |H_e| ~ 2^{n-e}.
```

The identity class is the intersection of `k`-th roots of the nested basic
trace-zero sets. `(HWO)`/`(REL)` then read as an "independence" statement for
these multiplicative dilates of additive objects; `H_1` is a hyperplane,
`H_2` the Kerdock set, `H_e` for `e >= 3` has no known rigid structure (the
Teichmueller-trace Gauss sums measured in note 01 are generic).

### 2.4 Coding-theory form

`N_ell(1)` is the number of zero columns of the `Z/2^{e}`-linear code spanned
by the functions `t -> Tr([t]^k) mod 2^{e_k}`, equivalently (MacWilliams) the
number of weight-one words of its dual. For the order-two part alone (the
squares subgroup, `delta = ceil(ell/2)` binary conditions) Weil already
suffices with room (`delta + log2 delta < n/2 - 1`); every higher Witt digit
adds the remaining `ell - delta` conditions and the barrier. The full object
is a Kerdock/BCH-like `Z/2^e` code of designed degree `~ ell ~ n/2`, whose
weight distribution is unknown in this range.

## 3. Shortcuts killed in this rung

- **Parity / algebraic count.** `I_n(1)` (irreducible `x^n + g`,
  `deg g <= floor(n/2)`) for `2 <= n <= 38` is odd for
  `n = 2,3,4,5,7,10,14,17,18,19,20,22,23,28,29,31,33,34,35,37` and even
  otherwise; no congruence rules out `I_n(1) = 0`. The normalised count
  `n I_n(1) / 2^{n - ceil(n/2) + 1}` stays within 5% of `1` from `n = 20`
  on (table `data/irreducible-counts-n2-38.txt`). No involution on the
  witness set exists: translation moves the class unless `n` is a power of
  two, reciprocal moves to the other end, Frobenius orbits only give
  `N = 1 + n I`.
- **Swan / Stickelberger.** The discriminant character gives the number of
  polynomials in the class with an odd number of factors exactly, but
  separating `r = 1` from `r >= 3` odd needs the same `1/n`-relative
  estimate; no gain.
- **Explicit-formula / Oesterle linear programming** on the Carlitz curve
  `Y_ell` (genus `(ell-2)2^{ell-1}+1`, `#Y(F_{2^r}) = 2^ell + 1` for
  `r <= ell`): the known low-degree power sums are `-2^ell`, weighted
  `2^{-r/2}`, and any nonnegative test polynomial has `c_0 >= |c_n|`, so the
  bound never beats `g 2^{n/2}`; the low-field information is too weak.
- **Cauchy--Schwarz over the low twists** for the cylinder variance
  (`(ICV)`/`(PL2)`): loses exactly the factor `2^{a-1}` it must not; the
  truth is `ell 2^{n-a+1}`, the bound is `ell 2^n`, the requirement
  `2^{2 ell - 2}`.
- **Second moments over cosets of the sparse subgroup**: the coset
  imbalance function is not a character (the `x^j`-coefficient sign is a
  cocycle, not a homomorphism), so the naive Parseval bound is not even
  defined; the data show the imbalances are at the square-root scale of the
  populations, not of `2^n`.
- **Large-q machinery** (Katz monodromy, Sawin's Betti bounds) is
  structurally the wrong direction: symmetry forces Frobenius toward scalars
  on isotypic pieces and removes cancellation; cancellation at fixed `q` must
  come from genericity that monodromy cannot certify.

## 4. Where this leaves the proof

Literature check of 2026-08-21 on the two integer-side templates (primary
sources; details in the lane transcript). (i) Least prime in a progression to
a prime-power modulus `q = p^k`, `p` fixed: Barban--Linnik--Chudakov 1964
exponent `8/3`, Gallagher 1972 `5/2`, Huxley 1975 `12/5` (Chang 2014 restates
it for any `q` with small prime factors), Banks--Shparlinski 2019 `2.1115` via
Postnikov's formula, Korobov double Weyl sums and Ford's explicit Vinogradov
mean value theorem; for fixed `p` there is no Siegel zero, which is exactly
why the constants depend on `p`. Nothing reaches `2 + o(1)`; that needs GRH
(Lamzouri--Li--Soundararajan `(phi(q) log q)^2`) or GLH (`q^{2+eps}`), and an
*asymptotic* at `x = q^2` is known only under GRH plus a pair-correlation or
Montgomery-type hypothesis (Kandhil--Languasco--Moree 2026). (ii)
Drappeau--Pratt--Radziwill's one-level density beyond support 2 averages over
moduli `q ~ Q` with smooth weights and says so explicitly ("no progress on
the de-averaging hypothesis"); Fiorilli--Miller's extensions are all
hypotheses about primes `= 1 mod q` beyond `x = q^2`. (iii) Function fields,
`q` fixed: Rosen's Weil bound `deg P <= 2 deg M + 2 log_q deg M + O(1)` is the
record; nothing published improves it by a logarithm for `M = x^k` over
`F_2`. The open fact `F:gf2-lemire-cylinder-twist-sup-bound` records the
minimal sufficient statement in the ledger with empty evidence.

The statement is a one-level-density assertion for the family of characters
mod `x^{j+1}` at exactly the edge of the Hughes--Rudnick support (`|P| ~ |Q|^2`,
the `primes = 1 mod Q up to Q^2` regime), restricted to exact-order Witt
layers, at fixed `q = 2`. Its integer analogues (Legendre's conjecture under
RH; Linnik's constant `2` for the residue `1` mod a prime power) are open
under every standard hypothesis, and for function fields it is open for every
fixed `q` (Sawin: "not yet nontrivial in the large `n` limit"). The data say
the estimate holds with growing margin and that the populations behave
randomly; the proof therefore has to manufacture cancellation from one of the
exact structures above (the Witt-digit tower, the Teichmueller/trace-zero
geometry, the power-map pullbacks, or the `Z/2^e` code), not from any
general family-average theorem.

The next experiments are the ones that could expose such a structure:
(a) the conditional distribution of one Witt digit given all lower digits on
the sparse sets `A_{s-1}`, across `s`, to see whether the nested
conditional biases carry any relation beyond the four-population identity;
(b) the joint statistics of `(S_n(chi), S_n(chi^2), S_{2n}(chi))` across a
layer; (c) the exact energies `#{(alpha,beta) : same Witt profile}` inside
the identity cylinder, to price the one-sided `(ICV)` route without Fourier
loss.

## 5. Mechanism verdicts from three parallel attempts (2026-08-21, late)

Three independent forks of this lane each took one surviving structure and
were required to return an exact identity or inequality, or the precise
obstruction. Scratch only; nothing below is proof credit.

**A. Witt-digit tower.** Exact calculus found and checked: in characteristic
two the Witt sum of two Teichmueller lifts is `[a] + [b] = sum_k V^k [c_k]`
with `c_0 = a + b` and `c_k = a b (a+b)^{2^k - 2}` for `k >= 1`; hence the
Galois-ring traces `T_s(a) = Tr_{GR(2^s,n)}([a])` obey the carry formula

```text
T_s(a+b) = T_s(a) + T_s(b) - 2 T_{s-1}(ab) - 4 T_{s-2}(ab(a+b)^2)
           - 8 T_{s-3}(ab(a+b)^6) - ...            (mod 2^s),
```

the `Z/4` case being the Kerdock identity; verified mod 16 on 3000 random
pairs in `F_{2^13}` (`data/witt-carry-formula-check.txt`). Every sparse
imbalance has an exact Galois-ring form (`Delta_{6,2}(13) = -64`,
`Delta_{5,3}(13) = -38` both ways). Squaring an imbalance and applying the
carry formula gives an exact pair expansion over `A x A`, but it is
tautological: its right side is a constrained sum-product character sum whose
only trivial bound is `|A|^2`, and dropping the constraint collapses it to a
Kerdock-type `|G_s|^2`. `A` is not additively closed and the carries are
nonlinear, so no shift-averaging identity with a bounded side exists;
Parseval over cosets returns Weil. Verdict: exact calculus, no inequality.

**B. Coset-product Weil polynomial.** For `P_psi(T) = prod_{chi_0}
L(chi_psi chi_0, T)` (degree `2^{a-1}(j-1)`; integral iff the coset is
Galois-stable, i.e. `cond(chi_psi^2) <= a-1`, else take the Galois orbit),
exact computation at `(7,15), (7,16)` confirms Newton power sums equal the
twisted cylinder sums `-2^{a-1} A_psi^{(m)}` for every `m` and exhibits the
2-adic Newton polygons (slopes `1/2` at `j = 3,5`; `1/4,1/2,3/4` at `4,6`;
`1/3,2/3` at `7`). Obstruction: `Q(T) = 1 - 2^{(n+1)/2}T^n + 2^n T^{2n}` is an
integral Weil polynomial with `p_m(Q) = 0` for all `m < n` and `p_n(Q) = n
2^{(n+1)/2}`, so multiplying any admissible polynomial by `Q^k` preserves
degree type, integrality, RH, the functional equation and *all* low power
sums while pushing `|p_n|` to about `0.7` of the trivial bound `D 2^{n/2}`
(target `D 2^{n/2}/(4 ell)`); and RH forces the minimal slope `<= 1/2`, so
2-adic information stops at `2^{ceil(n/2)} | p_n`. Verdict: no generic
invariant of `P_psi` can give the saving; only the specific arithmetic of the
Hayes characters can.

**C. Additive/multiplicative structure and constructions.** The summand and
the cylinder are both additive objects; the only multiplicative structure
(the class map on polynomials) is destroyed by primality, so no sum-product,
energy, or uncertainty argument applies, and the required saving, though
only a power `log2(ell)/ell`, is not produced by any of them (Weil is a
constant factor below trivial). Power-map pullbacks give only the trivial
inclusions `|A_ell| <= |A_{floor(ell/k)}|`. Every constructive or lifting
route is closed (branch ledger plus two new closures: the Carlitz-cyclotomic
Euclid argument yields primes of degree `~2^ell deg F`, and Hensel lifting at
`x` fails because irreducibility is not a local condition in the residue).
Verdict: no inequality, no construction covering prime `n`.

**D. Hidden exact relations across Witt orders (rank test).** For every
`(ell, n, j)` with `ell >= 14` and `j` in the window, the normalized
deviations `P_{j,s}/2^{n-j+floor(j/2^s)} - 1`, `s = 1..5` (60 data points),
span a matrix of exact rational rank `5` of `5` (`6` of `6` with a constant
column), and the signed imbalances `Delta_{j,s}`, `s = 1..5`, likewise have
rank `5`. So no universal linear relation among consecutive Witt orders exists
beyond the four-population identity and the resonance identities; the nested
populations are linearly free. Verdict: no identity to exploit.

**Net.** The exact machinery is now complete on all three fronts (Witt carry
calculus, integral coset products with exact power sums and Newton polygons,
the pullback/coding descriptions), and each front ends at the same wall: a
constrained character sum over a sparse set of size `~2^{n/2}` whose only
provable bound is trivial or Weil. The chain remains open at
`F:gf2-lemire-cylinder-twist-sup-bound`.

### 5.1 The Adams/Liouville degree-doubling relation is tautological

Candidate B's tempting identity is real but supplies no recursion.  Let
`lambda` be the completely multiplicative polynomial Liouville function,
`lambda(P^r)=(-1)^r`.  Euler factors give, for every Hayes character `chi`,

```text
L(lambda chi,u) = L(chi^2,u^2) / L(chi,u),
S_m(lambda chi) + S_m(chi) = 1_{2 | m} 2 S_{m/2}(chi^2).
```

Equivalently, `S_n(chi^2) = (S_{2n}(chi) +
S_{2n}(lambda chi))/2`.  The second summand is not a ray-class character sum:
it is exactly the Liouville-weighted prime-power sum that the Euler-product
identity introduces.  Therefore replacing `S_n(chi^2)` by degree `2n` trades
the original target for an equally uncontrolled term; applying the identity
again simply returns the first one.  Squaring also fails to preserve an exact
conductor layer, as noted above.  This is an algebraic identity, not a
conditional-balance theorem.  `lemire_adams_check.py` sums prime powers
directly for every character of `E_j`, `j <= 5`, and degrees `m <= 10`;
it asserts all 620 instances of the displayed equation.

## 6. Certified finite handoff extended to `n = 3000`

Using the branch CAS's own search and checker (`axeyum-gf2-search`,
`axeyum-gf2-check`; snapshot at `47fd7b440` with the two resource caps
`max_word_ops` and `max_coefficient_ops` raised 1000x -- resource admission,
not soundness guards), every degree `401 <= n <= 3000` now has a sparse
witness `x^n + sum x^e + 1` with all `e <= floor(n/2)`, carrying a
Frobenius/Bezout certificate that passes both the primary and the independent
checker: 2600 of 2600 `PASS`, 1334 trinomials and 1266 pentanomials. The
compact replayable table (degree, tail exponents, SHA-256 of the artifact,
check status) is `scripts/lemire-signed-trace/data/witnesses-401-3000-sha256.tsv` (the collaborating session committed the same witnesses as `witnesses-401-3000.txt`);
the 9.4 GB of artifacts live outside the repository at
`/data0/axeyum/scratch/lemire-signed-trace-witnesses-401-3000/`. An
independent flint-based search (`lemire_witness_search.py`, pure-Python Rabin
re-verification) agrees on existence for every degree in `401..842` (identical
trinomial witnesses; pentanomials differ by search order). Meaning (note: this
is insurance, not evidence for the open step): the chain is now complete for
`n <= 3000`, and for all `n` if `(HWO)`/`(CYL)` holds for `ell >= 1500`; the
open estimate itself is unchanged.

# AC-Bridge phase 3, workstream 20: adversarial verification of the load-bearing chains

Charge: break, if they can be broken, the "PROVED" claims phase 3 is about to
build on -- workstream A's `(CAB-L) -> (SPLIT-L) -> (ENV-L) -> (L4-LAYER) ->
(SUP-L)` collapse with its `K = 2` endpoint arithmetic (diary 11), workstream
C's `q_j` product machinery and the `(CDL)` sufficiency derivation (diary 13),
and Lemmas A/B (diary 04), W (diary 12), `E_1 = 0` (diary 13), D1/D1a/D3/D4 and
Theorem D2 (diary 14).

Date opened: 2026-08-20 (phase 3).
Board: `10-angles-board.md`, "Phase 3 assignments", item `20-verify-chains.md`.
Charter: `00-charter.md`.

Every audited claim gets exactly one of **CONFIRMED** (I re-derived the proof
myself and it is written out below), **GAP** (the proof has a hole, exhibited
precisely) or **FALSE** (counterexample witness).  Verdict table in FINDINGS
(a).  I did not trust any diary's own controls: every number below comes from
an implementation I wrote for this file.

New files written by this workstream:

```text
crates/axeyum-cas/examples/acb_ver_supl.rs   independent re-derivation of the
                                             conductor machinery + the a-priori
                                             ceiling; FAIL-CLOSED (exit 1 on a
                                             violated lemma, exit 3 if K=2 is
                                             refuted on a measured row)
```

## Method: two independent engines, neither sharing anything with the repo

**Engine A (sympy brute force).**  Enumerate every monic `F` of degree `n` over
`GF(2)`, factor with `sympy.Poly(...).factor_list()` over `GF(2)`, apply the von
Mangoldt weight, bin by reciprocal truncation.  Shares no code, no algorithm and
no convention with the CAS or with any `acb_*` example.

**Engine B (group-algebra Dirichlet series).**  `N(z) = z A'(z) / A(z)` in
`Z[E_ell]`, using the **closed form**

```text
A_d = 1_(V_d)              for d <= ell        (V_d = {1+a_1 t+...+a_d t^d})
A_d = 2^(d-ell) * 1        for d >  ell
```

so it never enumerates a polynomial at all, and it computes `N_n` by series
inversion `B = A^(-1)`, `N_n = sum_(d=1)^n d (A_d * B_(n-d))`.  Conductor
components come from **direct subgroup averaging** over cylinders, never from
the sibling recursion `R_(j-1) = R_j + R_j g_j` that diary 11 uses.

Engine B was validated against engine A on `(4,9)`, `(4,10)`, `(5,11)`,
`(5,12)`, `(6,13)`, `(6,14)`: `N_n(e)` agrees **entry by entry**, all `2^ell`
classes, both parities.  Every row below is engine B; every row up to
`ell = 13` reproduces diary 04's master table `M_2`, `M_4`, `R_0`, `N_n(1)` to
the digit, and diary 11's `V_j`, `kappa_j`, `(L4-LAYER)` and `(ENV-L)` ratios to
the printed precision.

`Pi_n` and `I_n(1)` were rebuilt a third time, from a hand-written Rabin
irreducibility test plus a hand-written principal-unit power map.

**A near-miss of my own, recorded because project law requires it.**  My first
Rabin test compared `x^(2^d) mod f` against the literal word `2`, which is wrong
whenever `deg f = 1` (the residue of `x` mod `x+1` is `1`, not `x`).  It
declared `x+1` reducible and produced `Pi_16 = 23` against the true `24` --
i.e. a *fabricated disagreement* with diary 04 at exactly one row.  Caught by an
irreducible-count control against `sum_(k|d) mu(d/k) 2^k / d` for `d = 1..12`,
not by the disagreement itself.  The diary was right; I was wrong.  (Diary 04
records an almost identical Rabin defect of its own.  Two independent agents,
same trap.)

## Priority 1 -- A's reduction chain to (SUP-L)

### The chain, re-derived line by line

```text
D = sum_(j=1)^ell D_[j]                       [P_0 D = mean D = 0]
M_4 = sum_e D_e^4 <= sum_e U_L(e)^4,   U_L = sum_j |D_[j]|      (ENV-L)
||U_L||_4 <= sum_j ||D_[j]||_4                                  (Minkowski)
||D_[j]||_4^4 = sum_e D_[j]^4 <= (max_e D_[j]^2)(sum_e D_[j]^2) = sup_j^2 V_j
      =>  ||D_[j]||_4 <= sup_j^(1/2) V_j^(1/4)
(SUP-L):  sup_j <= K (j-1) 2^((j-1)/2) 2^(n/2) 2^(-ell)
Lemma 6:  V_j  <= 2^(n-ell) 2^(j-1) (j-1)^2
      =>  ||D_[j]||_4 <= K^(1/2) (j-1) 2^((j-1)/2) 2^((2n-3ell)/4)
```

The exponent check: `n/4 + (n-ell)/4 - ell/2 = (2n - 3 ell)/4`.  Correct.  So

```text
M_4 < ( K^(1/2) S(ell) 2^((2n-3ell)/4) )^4 ,   S(ell) = sum_(j=2)^ell (j-1) 2^((j-1)/2)
```

and the chain closes iff `K^(1/2) S(ell) 2^((2n-3ell)/4) < mu - P_n`.

**Every inequality above is CONFIRMED.**  All four are elementary and I
re-derived each; `P_0 D = 0` because `sum_e N_n(e) = 2^n = 2^ell mu`, which my
engines assert on every row.  `D_[1] = 0` (so the sum may start at `j = 2`) is
Lemma 6's `V_1 = 0`, asserted on every row of mine.

### The `K = 2` endpoint arithmetic -- CONFIRMED, to the level

Recomputed at 80-digit precision with `S(ell)` exact, `P_n = 1` at the odd
endpoint (Lemma A) and `P_n = P_n^sharp = (ell+1)2^ceil(ell/2) + n 2^ceil((ell+1)/2)`
at the even endpoint (Lemma B), "first `ell` from which it holds for every
larger `ell`":

```text
   K      odd endpoint    even endpoint      diary 11 claims
  1.6         21               19               21 / 19
  2.0         22               20               22 / 20
  2.5         23               21               23 / 21
  4.0         25               23               25 / 23
```

Reproduced exactly, all eight entries.  Boundary detail at `K = 2`, odd:
`ell = 21` gives `lhs = 4.680025e6` against `rhs = 4.194303e6` (fails);
`ell = 22` gives `8.318030e6 < 8.388607e6` (holds, margin `0.8%`).  Even:
`ell = 19` fails by `1.9%`, `ell = 20` holds by `9.2%`.  The crossovers are
genuinely tight at the first level, as the table implies.

### Does the chain bound `N_n(1) > Pi_n`, or only `N_n(1) > 0`?

**It bounds `N_n(1) > Pi_n`.  CONFIRMED -- A did not repeat the error diary 04
refuted.**  The chain terminates in `M_4 < (mu - P_n)^4` with `P_n` from
Lemma A/B, not in `M_4 < mu^4 = 2^(4(n-ell))`; diary 11's crossover table, its
"strict" column and the `(L4-LAYER)` / `(ENV-L)` closure tables are all computed
against the diary-04 budget.  I re-derived the crossovers with `mu^4` as a
control: they move to `ell >= 22` (odd, unchanged, since `P_n = 1`) and
`ell >= 20` (even) -- i.e. numerically indistinguishable at the crossover, which
is why the distinction has to be checked by reading the statement rather than
the table.

**GAP (statement, not chain): `(CAB)` and `(CAB-L)` are still stated against the
insufficient budget.**  Diary 11 defines

```text
(CAB-L):  A_L  <  2^(ell + 4(n-ell)) - 3 M_2^2
```

and says it is "a sufficient statement of exactly the same type as `(CAB)`".
Taken literally it yields `2^ell M_4 = 3M_2^2 + K_4 <= 3M_2^2 + A_L < 2^ell mu^4`,
i.e. `M_4 < mu^4` -- **precisely the criterion diary 04 proved insufficient**
(it gives `N_n(1) > 0`, and `N_n(1) = 1` from `x^n` is consistent with
`I_n(1) = 0`).  The fix is one substitution, `2^(ell+4(n-ell)) -> 2^ell (mu-P_n)^4`,
and diary 11 already measures that column; but the named candidates `(CAB)` and
`(CAB-L)` that the board's phase-2 results row advertises are, as written, the
refuted form.  Size of the correction: at the odd endpoint it is a factor
`(1 - 2^(-(ell+1)))^4`, invisible; at the even endpoint it is a factor
`0.488` at `ell = 13` and `-> 1` thereafter.  Harmless numerically, wrong as a
statement.

### `(SPLIT-L)`, `(ENV-L)`, `(L4-LAYER)` -- CONFIRMED

`(SPLIT-L)` is `|Klev| <= |2^ell raw| + |P_lev|` summed, plus Lemma 4's exact
`sum mult |P_lev| = 3 M_2^2`; then `(CAB-L)` follows from
`R_L + 6 M_2^2 < 2^ell (mu-P_n)^4`.  Arithmetic correct.  `(ENV-L)` and
`(L4-LAYER)` are the two displayed steps of the chain above.  My independent
`(ENV-L)` ratio at `(6,13)` is `0.29552` against diary 11's `0.2955`, and
`(L4-LAYER)` at `(6,13)` is `0.841350` against `0.841`; at `(12,25)`/`(12,26)`
I get `0.786966`/`0.789920` against `0.787`/`0.790`.

### Lemmas 1-7 of diary 11 -- all CONFIRMED

* **Lemma 1** (`hat T_d = d a_d m_(n-d)`): `A_d = 1_(V_d)` for `d <= ell` because
  the class of a monic degree-`d` polynomial records every non-leading
  coefficient; `A * M = delta` gives `hat M(chi,z) = 1/L(chi,z)`.  My engine B
  *is* this identity, and it reproduces engine A entry-by-entry -- so Lemma 1 is
  independently confirmed by construction on six rows.
* **Lemma 2** (`a_d(chi) = 0` for `d >= level(chi)`): the truncation
  `V_d -> E_j` is onto with fibres `2^(d-j)`, and `chi` descends to a
  *nontrivial* character of `E_j`, whose full sum vanishes.  Correct.
* **Corollary 3**: `hat A_d(1) = 2^d`, `L(1,z) = 1/(1-2z)`, so
  `m_j(1) = the z^j coefficient of (1-2z), = 0` for `j >= 2`, and `n - d >= ell + 2 >= 2`.  Correct.
* **Lemma 4** (orthogonality): asserted by my code as an exact rational identity
  `<D_[j], D_[k]> = 0` for **every** pair `j < k` on every row `ell = 4..13`,
  both parities, plus `sum_j V_j = M_2`.  Zero violations.
* **Lemma 5** (parity selection rule): I rebuilt the full conductor cell tensor
  and checked every cell.  Zero violations on `(5,11)`, `(5,12)`, `(6,13)`,
  `(6,14)`, `(7,15)`, `(7,16)`, `(8,17)`, `(8,18)`.  The restriction-to-`H_(J-1)`
  argument is correct.
* **Lemma 6**: `V_1 = 0` and `V_2 = 2^(n-ell+1)` **exactly** on every row of
  mine; `V_j <= 2^(n-ell) 2^(j-1) (j-1)^2` never violated (`ell = 4..13`).
* **Lemma 7** (the exact `1/4` recursion): I verified it **cell by cell** at
  fixed `n`, comparing `Klev^(ell)` against `Klev^(ell-1)/4` on every cell with
  all levels `<= ell-1`: 35, 70, 126, 210 cells at `ell = 5..8`, both parities,
  zero violations.  The proof is right; the displayed multiplier
  `2^(1+1)/2^4 * 2` is a typo for `2 * 2 / 2^4 = 1/4` (two factors of two, one
  from the class sum and one from the `2^ell` prefactor, against `2^(-4)` from
  the four halved layers).  The stated value `1/4` is correct.

## Priority 1(b) -- the attainment structure of the `2.0000` maximum

This is the part with real consequences for the `(SUP-L)` assault.

### There is an a-priori ceiling, and it is `2^((j-1)/2)`

`(SUP-L)`'s own inputs already bound `kappa_j`.  Level `j` carries exactly
`2^(j-1)` characters and Weil gives `|S_chi| <= (j-1) 2^(n/2)`, so

```text
max_e |D_[j] at e|  <=  2^(-ell) sum_(level j) |S_chi|  <=  2^(-ell) 2^(j-1) (j-1) 2^(n/2)
```

and dividing by `kappa`'s denominator `(j-1) 2^((j-1)/2) 2^(n/2) 2^(-ell)`,

> **(CEIL).  PROVED.**  `kappa_j <= 2^((j-1)/2)` for every level, given exactly
> the inputs diary 11 already assumes.  In particular
> `kappa_2 <= sqrt 2`, `kappa_3 <= 2`, `kappa_4 <= 2 sqrt 2`.

**Consequence: `(SUP-L)` with `K = 2` is a THEOREM at `j <= 3` and carries no
information there.**  Only `j >= 4` is open at `K = 2`.

### `kappa_2` is not merely bounded, it is *forced*

> **(K2-EXACT).  PROVED.**  `kappa_2 = 1` at every odd endpoint and
> `kappa_2 = sqrt 2` at every even endpoint, for every `ell >= 2`.

*Proof.*  `E_2 = G/H_2` is the principal units of `F_2[x]/x^3`, cyclic of order
4 (`(1+t)^2 = 1+t^2`, `(1+t)^4 = 1`), so the two level-2 characters are a
conjugate pair of order 4 and `S := S_chi in Z[i]` with `|S|^2 = 2^n` exactly
(Lemma 6).  Then `D_[2] at e equals 2^(1-ell) Re(S conj(chi(e)))` takes the four values
`2^(1-ell) {a, b, -a, -b}` with `S = a + bi`, so
`max_e |D_[2]| = 2^(1-ell) max(|a|,|b|)`.  A power of two has an essentially
unique representation as a sum of two squares in `Z[i]` (2 is ramified):
`a + bi = unit . (1+i)^n`.  For `n` odd this gives `|a| = |b| = 2^((n-1)/2)`, for
`n` even `{|a|,|b|} = {2^(n/2), 0}`.  Substituting `n = 2ell+1` / `n = 2ell+2`
gives `sup_2 = 2` / `4` and hence `kappa_2 = 1` / `sqrt 2`.  QED

Measured `sup_2` is `2` on every odd row and `4` on every even row of mine,
`ell = 4..13`.  Note `kappa_2 = sqrt2` *equals* the ceiling: at the even
endpoint level 2 exhibits **no cancellation at all**, and cannot.

### Where the `2.0000` lives, and what it is

Diary 11's global maximum is at `(ell, n, j) = (11, 24, 3)`.  I reproduce it
exactly, from engine B, in Python and again in Rust:

```text
ell=11 n=24 j=3:  sup_3 = 16 (exact integer)   kappa_3 = 2.0000
                  V_3   = 131072  =  2^(n-ell) 2^(j-1) (j-1)^2  = the Weil
                                     envelope, SATURATED to the digit
                  argmax set: 512 classes = 2 cosets of H_3, and the identity
                              class e = 1 IS among them:  D_[3] at 1  = -16
```

So the global maximum of the whole `kappa` table is a **double degeneracy**:

1. every one of the four level-3 characters attains the extremal Weil size
   `|S_chi| = (j-1) 2^(n/2) = 2 . 2^12 = 8192` (`V_3` equals its envelope
   exactly, which forces this);
2. all four align in phase at the **identity class**, so
   `|D_[3] at 1| = 2^(-ell) . 4 . 8192 = 16` is the full triangle sum.

That is exactly `kappa_3 = 2^((3-1)/2) = 2`, the ceiling of (CEIL).  **The
global maximum `2.0000` is the a-priori bound being attained, not a measurement
about cancellation.**  It is structural (the answer the charge asked for): it is
the identity class at the lowest level where the ceiling reaches 2, and it
constrains `K` not at all in the regime where `(SUP-L)` is open.

### The number that actually matters, and it is worse than advertised

Separating the trivially-true levels from the open ones:

```text
 (ell,n)     max_j kappa_j    max_(j>=4) kappa_j     at j
  (5,12)        1.8750             1.8750             5
  (6,14)        1.5321             1.5321             4
  (8,18)        1.5000             1.3637             8
  (10,22)       1.7825             1.7825             4
  (11,23)       1.1500             1.1500             6
  (11,24)       2.0000             1.9922             5
  (12,25)       1.1186             1.1186            12
  (12,26)       1.5234             1.5234             9
```

`max_(j>=4) kappa_j = 1.9922` at `(11,24)`, `j = 5` -- a margin of **0.4%**
below `K = 2`, on the open part of the statement, inside my (small) range.
Diary 11 reports "`K = 2` -- the value that fits all measured data with a `31%`
margin"; that `31%` is `2 / 1.5234`, the margin over the `j >= 6` maximum.  The
levels `j = 4, 5` are neither reported in diary 11's per-`j` table (which prints
even `j` only: 2, 4, 6, ..., 20) nor covered by the `j >= 6` statement, and
`j = 5` is where the open-regime maximum sits.  **GAP (presentation, with
consequences for the assault):** the reported margin structure hides the binding
row.  The honest statement of the measured evidence is

```text
 j <= 3 :  K = 2 is proved (CEIL); measured kappa saturates the ceiling.
 j >= 4 :  K = 2 is open; measured max 1.9922 at (11,24,5) in my range,
           1.8994 at some j = 4 row in diary 11's larger range.
           No measured margin worth quoting.
```

Diary 11's own next experiment E-A1 ("falsify `(SUP-L)` hard") is therefore the
right call, and it should be run at `j = 4, 5` specifically, not only at large
`j`.  My `acb_ver_supl` exits **3** the moment any row produces `kappa > 2`.

## Priority 2 -- C's `q_j` machinery and the `(CDL)` chain

### `R_0 = prod_j (1 + q_j)` and `0 <= q_j <= 1` -- CONFIRMED

Re-derived: with `m = m_(j-1)(b)` the parent cylinder mass, `u + v = m`,
`t = (u-v)/m`, one has `u^2 + v^2 = m^2 (1 + t^2)/2`, hence

```text
C_j = 2^j sum_b (u_b^2 + v_b^2) = 2^(j-1) sum_b m_b^2 (1 + t_b^2) = C_(j-1) (1 + q_j)
```

with `q_j` the `m^2`-weighted mean of `t_b^2 in [0,1]`.  `C_0 = M_2^2` (one
cylinder) and `C_ell = 2^ell M_4` (singleton cylinders), so telescoping gives
`R_0 = prod (1+q_j)`.  `C_j = sum_(cond chi <= j) |fhat(chi)|^2` is Parseval on
`E_j` applied to the pushforward of `D^2`, so `E_j = C_j - C_(j-1)` really is
the exact-conductor level energy of the `D^2`-spectrum.  Lemma D1
(`C_(j-1) <= C_j <= 2 C_(j-1)`) is the same computation.

My code asserts, as **exact rationals** and fail-closed, on every row
`ell = 4..13` both parities: `C_0 = M_2^2`, `C_ell = 2^ell M_4`,
`0 <= q_j <= 1` per level, and `prod_j (1+q_j) = R_0` as an identity between
`BigRational`s.  Zero violations.

### `E_1 = 0` at the odd endpoint (Result C4) -- CONFIRMED

Re-derived independently.  `F(x) -> F(x+1)` is a degree- and
Mangoldt-preserving bijection of the monic degree-`n` polynomials.  The
coefficient of `x^(n-i)` in `F(x+1)` is `sum_(m<=i) a_m binom(n-m, i-m)`, which
for `i <= ell` involves only `a_0..a_ell`, so it descends to a map `sigma` on
classes; the induced map on `(a_1,...,a_ell)` is unitriangular, hence bijective.
Therefore `D_(sigma e) = D_e`.  At `i = 1` the coefficient is `a_1 + n`, so for
`n` odd `chi_1(sigma e) = -chi_1(e)` where `chi_1 = (-1)^(a_1)` is the unique
level-1 character (`a_1` is additive under the group law).  Re-indexing
`e -> sigma(e)` in `fhat(chi_1) = sum_e D_e^2 chi_1(e)` gives
`fhat(chi_1) = -fhat(chi_1) = 0`, and `E_1 = |fhat(chi_1)|^2 = 0`.  QED

Measured: `q_1 = 0` on every odd row `ell = 4..13` and `q_1 != 0` on every even
row (e.g. `q_1 = 0.209086` at `(5,12)`, `0.00228128` at `(6,14)`), exactly as the
proof predicts.  My example asserts `q_1 = 0` at odd endpoints fail-closed.

### `(CDL) => (WR) => (W4)` with the corrected budget -- CONFIRMED

`(CDL)` says `E_j <= M_2^2/ell` for `j <= c log2 ell`.  Since `C_(j-1) >= C_0 =
M_2^2` (Lemma D1 monotonicity), this gives `q_j = E_j/C_(j-1) <= 1/ell`, so
Lemma D5's hypothesis is met on `J = {1,...,floor(c log2 ell)}` with `Q = 1/ell`.
Lemma D5 (`R_0 <= 2^(ell-|J|)(1+Q)^|J|`) is immediate from `(D-PROD)` and
`q_j <= 1` off `J`.  The conclusion is `R_0 < G` with

```text
G = 2^ell (mu - P_n)^4 / (mu Sigma(ell))^2 ,
```

i.e. `(WR)`, which uses **Lemma A/B's `P_n`, not `mu`**.  So yes: `(CDL)` feeds
the corrected `(mu - P_n)^4` budget, and through `M_2 <= mu Sigma(ell)` it
lands on `(W4-exact)`, hence `N_n(1) > Pi_n`.  CONFIRMED.

Independent recomputation of `log2 G` (80-digit): `171.4824` at `(200,401)`,
`173.4824` at `(200,402)`, `367.4535` at `(400,801)`, `369.4535` at `(400,802)`
-- diary 13 and diary 04 both quote `171.482426 / 173.482426 / 367.453465 /
369.453465`.  Agreement.  Asymptotics `log2 G = ell + 2 - 4 log2 ell + o(1)`
confirmed, and the measured `log2 G` runs *above* that approximation on every
finite row (e.g. `4.6302` vs `4.0083` at `ell = 19`), so using the approximation
is conservative in the right direction.

### The constant `4.1 log2 ell` -- CONFIRMED

Lemma D5 needs `|J| (1 - log2(1+Q)) > ell - log2 G`.  With `Q = 1/ell` and
`|J| = floor(4.1 log2 ell)` -- I used **floor**, which is the count `(CDL)`
actually supplies for `j <= 4.1 log2 ell`, and is one weaker than diary 13's
`ceil` -- the inequality holds at every `ell` I tested:

```text
  ell     parity   ell - log2 G   required |J|   floor(4.1 log2 ell)
   14      odd        12.3798        13.7483            15
   20      odd        14.6975        15.8103            17
   50      odd        20.3424        20.9406            23
  200      odd        28.5176        28.7243            31
  400      odd        32.5465        32.6642            35
 1000      odd        37.8516        37.9062            40
10000      odd        51.1497        51.1571            54
```

and every even row is easier (`log2 G` is ~2 bits larger).  Asymptotically
`required |J| -> 4 log2 ell - 2` while `floor(4.1 log2 ell) >= 4.1 log2 ell - 1`,
so the margin `0.1 log2 ell + 1` grows.  `(CDL-a)` (`Q = 1/2`,
`ceil(9.7 log2 ell)`) also checked: no violations over `ell = 14..60` plus
`100, 200, 400, 1000, 10000`, both parities.

### GAP found in the twist identity, harmless

Diary 13 writes `(TWIST)` as

```text
fhat(chi) = 2^(-ell) sum_psi S_psi conj( S_(psi chi) ) .
```

Carrying out the stated derivation (Fourier inversion, square, sum against
`chi`, orthogonality, `S_(psi^(-1)) = conj(S_psi)`) gives

```text
fhat(chi) = 2^(-ell) sum_psi S_psi S_(chi psi^(-1))
          = 2^(-ell) sum_psi S_psi conj( S_(psi chi^(-1)) ) ,
```

i.e. the displayed formula computes `fhat(chi^(-1)) = conj(fhat(chi))`, not
`fhat(chi)`.  **GAP (typo-grade), no consequence**: `chi -> chi^(-1)` preserves
conductor level and `|fhat(chi^(-1))| = |fhat(chi)|`, so `E_j`, the pointwise
sufficient form and the "shifted second moment" identification are all
unaffected, and for the order-2 characters the two forms coincide.  Worth
fixing before `22-cdl-assault.md` builds on the displayed form.

## Priority 3 -- Lemmas A, B, W, D1-D4/D2

### Lemma A (odd endpoint `Pi_n = 1`) -- CONFIRMED

The argument is right (`k | n`, `n` odd `=> k` odd `>= 3 => d = n/k <= ell`;
`d <= ell` makes `P -> <P>` record every non-leading coefficient; `g -> g^k` is
an automorphism of the 2-group `G` for odd `k`, so `<P>^k = 1 <=> P = x^d`, which
is irreducible only at `d = 1`, forcing `F = x^n`).  Independently measured
`Pi_n = 1` on every odd row `ell = 5..11` by direct enumeration of every proper
prime-power layer.

### Lemma B (even endpoint bound) -- CONFIRMED

Layer 1 (`k` odd `>= 3`): `n` even and `k` odd make `d = n/k` **even**, and
`d <= n/3 <= ell` for `ell >= 2`, so as in Lemma A `<P>^k = 1` forces `P = x^d`
with `d >= 2` even -- not irreducible.  Layer empty.  Correct.
Layer 2 (`k = 2`): an irreducible of degree `ell+1 >= 2` has `P(0) = 1`, so
`<P>` (which sees `a_1..a_ell`) plus the forced `a_(ell+1) = 1` determines `P`;
the constraint is `<P> in G[2]`, and `|G[2]| = |G|/|G^2| = 2^ell/2^floor(ell/2) =
2^ceil(ell/2)` because `(1+f)^2 = 1+f^2`.  Weight `ell+1` each.  Correct.
Layer 3 (`k` even `>= 4`): `d <= n/4 = (ell+1)/2`, at most `2^d/d` irreducibles
of degree `d`, weighted mass `<= 2^d <= 2^ceil((ell+1)/2)`, fewer than `n`
admissible `k`.  Correct (crude, valid).

Measured: `P_n^sharp >= Pi_n` on every even row `ell = 5..11`, with
`P_n^sharp / Pi_n` between `9` and `39` there; `mu - P_n^sharp > 0` first at
`ell = 7` (`512 - 384`), matching diary 04.  My exact `Pi_n` reproduces diary
04's column at every row I computed (`16, 22, 24, 37, 76, 45, 160` for
`ell = 5..11` even), and `Pi_n + n I_n(1) = N_n(1)` from engine B on all of them.

### GAP in `(WK)`: the non-strict form does not close

Diary 04 boxes

```text
(WK)   K_4 <= 2^ell (mu - P_n)^4 - 3 (mu Sigma(ell))^2
```

as the load-bearing target ("the one the ladder should carry", and the board
adopts it).  Chasing it: `2^ell M_4 = 3M_2^2 + K_4 <= 3(mu Sigma)^2 + K_4 <=
2^ell (mu-P_n)^4`, i.e. `M_4 <= (mu - Pi_n)^4` **non-strictly**, which yields
`|D_1| <= mu - Pi_n`, `N_n(1) >= Pi_n`, `n I_n(1) >= 0` -- not `>= 1`.  The
theorem `(W4-exact)` is stated with a strict inequality for exactly this reason.
**GAP (one hair), and diary 04 already owns the fix**: its own integrality
refinement `M_4 <= (mu - Pi_n - n)^4` makes the non-strict form sufficient.
`(WK)` should be restated either strictly or with `(mu - P_n - n)^4`.  Every
downstream chain I audited -- `(WR)`, Lemma D5, the `(SUP-L)` chain -- is
strict and unaffected.

### Lemma W (diary 12) -- **GAP**, and it bites exactly at `m = 4`

Lemma W bounds `dim Sing(Y_(m,n,h))` by
`max{ s + (m-2)(h+1), s + 2 delta + (m-3)(h+1) }` via three cases on a Jacobian
left-dependency `v_iota^T A_iota = 0` (all `iota`), `u^T A_1 = 0` with
`u = sum_(iota in V) v_iota`, `V = {iota >= 2 : v_iota != 0}`.

The third case is stated as "`u != 0` with `|V| >= 2`, **or** `u = 0` with
`|V| >= 3`: at least three of the `m` tuples lie in `T_(n-h-2)`", and is then
dimension-counted as *one tuple free in `T_s` (dimension `s`), two in
`T_s n Z_w` (dimension `<= delta` each), the remaining `m-3` free in `Z_w`*.

**That count silently assumes `z_1` is one of the three.**  It is, in the
sub-case `u != 0` (which is what forces `z_1 in T_s`).  It is **not** in the
sub-case `u = 0, |V| >= 3`: there the condition `u^T A_1 = 0` is vacuous and
`z_1` is unconstrained, of dimension `n`, while three of `z_2..z_m` lie in
`T_s n Z_(z_1)`.  That component has

```text
dim <= n + 3 delta + (m-4)(h+1) ,
```

which **exceeds** the claimed maximum by `delta + 1` and gives

```text
codim  =  (m-1)(h+1) - 3 delta ,   which for m = 4 is  3(h+1) - 3 delta ,
codim >= 2h+3   <=>   h >= 3 delta      (not  2 delta <= h+1) .
```

At the odd endpoint `h = ell` and diary 12's own proved lower bound
`delta >= ceil(ell/2) - 2` give `3 delta >= 1.5 ell - 6 > ell` for every
`ell >= 13`, so the missing case is **not** covered by Lemma W's hypothesis
`2 delta <= h+1` (which *is* satisfied there: `ell - 4 <= ell + 1`).  The
sub-case cannot arise for `m = 3` (then `V subset {2,3}`, so `|V| <= 2`), which
is why the lemma reads correctly at `m = 3` -- and `m = 4` is the only case this
project uses.

Verdict **GAP**, not FALSE: the dimension count is an upper bound and the
component may well be smaller, but no argument for that is given, and the
"PROVED (modulo one bookkeeping point OPEN(bk))" label is not earned at `m >= 4`.
Strategically this changes nothing -- diary 12 independently retires the
Hast--Matei architecture on the `(BUDGET)` grounds -- but Lemma W is advertised
in the board's phase-2 results and in `23-artifact.md`'s proved corpus, and it
should not ship with that label.

### Diary 14: Lemmas D1, D1a, D3, Theorem D2 -- CONFIRMED; Lemma D4 -- GAP with repair

* **Lemma D1** (fibres `xor s`-stable, `eps` invariant).  CONFIRMED, given the
  identification the text implies: the fibre-keying shift `s` *is* the
  autocorrelation shift `h`, so `eps(m xor s) = mu(f_(m xor s)) mu(f_m) = eps(m)`
  by symmetry of the product.  As written ("`eps` is symmetric in
  `f_m <-> f_(m+h)`, i.e. invariant under `m -> m xor s`") the "i.e." is only an
  identity if `s = h`; worth saying out loud, because the sentence is otherwise
  a non-sequitur.
* **Corollary D1a** (`sum_F c_F^2 = 2 N_sf + Theta`).  CONFIRMED, and the
  correction to sweep-08's `(E2')` identity is real: the diagonal contributes
  `N_sf` (nonzero-`eps` points), not `N_points`, and D1 forces a second equal
  contribution off-diagonal.
* **Theorem D2**.  CONFIRMED.  I re-derived the kernel dimension of
  `z -> z^2 + h z mod x^(r-v)` by hand in both regimes: for `3v < r` the kernel
  is `span{h, x^(m-v), ..., x^(m-1)}` of dimension `v+1` (`m = r-v`); for
  `3v >= r` it is `{z : v(z) >= ceil(m/2)}` of dimension `floor(m/2)`.  Both
  match the stated formula, and the additive `max(0, d-(r-v)+1)` term is the
  automatically-admitted high-valuation directions.  Claim 3 (`2^(d-v)` shifts
  with `v(h) = v`) is immediate.
* **Lemma D3** (`(x+1)^2 | f  <=>  f(1) = f'(1) = 0`, both `F_2`-linear, affine
  fibre, `2^(n-2)` Moebius zeros, `|c_F| <= (3/4) 2^n`).  CONFIRMED.
* **Lemma D4** -- **GAP** in the proof, conclusion repairable.  The claim
  "`T_h` contains `span{x^j : max(1, ell+1-2v) <= j <= d}`, of dimension
  `min(2v-1, d)`" is **false** whenever `3v > ell+1`.  Witness: `ell = 13`
  (`r = 14`, `d = 12`), `v = 5`, `h = x^5`, `tau = x^4`.  Then
  `max(1, ell+1-2v) = 4`, so `x^4` is in the claimed span; but
  `v(tau) + v(tau+h) = 4 + 4 = 8 < r - v = 9`, so `x^4 notin T_h`.  Theorem D2's
  own dimension formula confirms it: `dim T_h = floor(9/2) + 4 = 8`, against the
  claimed span's dimension `min(9,12) = 9`.  The step that fails is the
  unstated assumption `v(tau) > v` in "for `v(tau) > v` we have `v(tau+h) = v`".

  **Repair (mine), which restores the conclusion for every `2 <= v <= d`:**
  restrict to `tau = x^j` with `j > v`, where the condition really is
  `j >= r - 2v`.  Then `T_h contains span{x^j : max(v+1, ell+1-2v) <= j <= ell-1}`,
  of dimension `2v-1` when `3v < ell` and `ell-1-v` when `3v >= ell`; that is
  `>= 2` for `2 <= v <= ell-3`, and the two remaining values `v = ell-2, ell-1`
  are checked directly (`x^(ell-1)` and `x^(ell-2)` both satisfy the condition,
  since `r - v <= 3` there).  Two consecutive powers `x^j, x^(j+1)` always
  survive, on which `lambda_1 = (1,1)` and `lambda_2 in {(1,0),(0,1)}` are
  independent.  So **Lemma D4's statement is CONFIRMED with a corrected proof**,
  and its corollary ("no fibre of dimension `>= 4` is zero-free") stands.

## Priority 4 -- numerical spot-verification, from scratch

All values below are engine B, cross-validated against engine A (sympy) where
affordable, and re-derived a third time by `acb_ver_supl` in Rust with exact
`BigRational` arithmetic.

```text
 (ell,n)   M_2          M_4                    R_0        N_n(1)  Pi_n  I_n(1)
  (5,11)   4384         765472                 1.274495    45      1      4
  (5,12)   23584        73638400               4.236619   160     16     12
  (6,13)   20832        20044320               2.956034    79      1      6
  (6,14)   63648        194446464              3.071924   288     22     19
  (11,24)  163626016    41067019870720         3.141365  7840    160    320
  (13,28)  3033730976   3400462499438720       3.026731    --     --     --
```

Every entry reproduces diary 04's master table exactly, including the two
`(W4)`-failure witnesses diary 04 pinned (`M_4 = 357265460654496` at `(12,26)`,
`M_4 = 3400462499438720` at `(13,28)`).

Level data at the two rows the charge names:

```text
(5,11)  j:      1      2      3      4      5
        V_j:    0    128    256   2448   1552
        sup:    0      2      4     11     11
        kappa:  --  1.0000 0.7071 0.9167 0.4861
        q_j:    0  7.672e-3 1.523e-2 8.041e-2 1.531e-1     (q_1 = 0, Result C4)

(6,13)  j:      1      2      3      4      5      6
        V_j:    0    256    512   2064   3088  14912
        sup:    0      2      4      6      9     32
        kappa:  --  1.0000 0.7071 0.5417 0.4198 0.8000
        q_j:    0  2.570e-3 8.706e-2 2.823e-1 4.044e-1 5.061e-1
        (L4-LAYER) sum_j ||D_[j]||_4 / (mu - P_n) = 0.841350   [diary 11: 0.841]
        (ENV-L)    sum_e U_L^4 / ((mu-P_n)^4 - 3M_2^2/2^ell) = 0.29552  [0.2955]
```

`V_2 = 2^(n-ell+1)` exactly on both (`128 = 2^7`, `256 = 2^8`), and `V_1 = 0`.

The `kappa` sweep, `ell = 4..13`, both parities, with the ceiling of (CEIL):

```text
 (ell,n)   max_j kappa   at j   ceiling there   max_(j>=4) kappa   at j
  (4,9)      1.0607        3        2.000           0.7500          4
  (4,10)     1.4142        2        1.414           0.5893          4
  (5,11)     1.0000        2        1.414           0.9167          4
  (5,12)     1.8750        5        4.000           1.8750          5
  (6,13)     1.0000        2        1.414           0.8000          6
  (6,14)     1.5321        4        2.828           1.5321          4
  (7,15)     1.0607        3        2.000           0.9944          5
  (7,16)     1.5000        3        2.000           1.1667          7
  (8,17)     1.0625        4        2.828           1.0625          4
  (8,18)     1.5000        3        2.000           1.3637          8
  (9,19)     1.2723        8       11.31            1.2723          8
  (9,20)     1.4142        2        1.414           1.1719          9
 (10,21)     1.1767        5        4.000           1.1767          5
 (10,22)     1.7825        4        2.828           1.7825          4
 (11,23)     1.1500        6        5.657           1.1500          6
 (11,24)     2.0000        3        2.000           1.9922          5
 (12,25)     1.1186       12       45.25            1.1186         12
 (12,26)     1.5234        9       22.63            1.5234          9
 (13,27)     1.3423       12       45.25            1.3423         12
 (13,28)     1.4984       11       32.00            1.4984         11
```

Global max `2.0000` at `(11,24,3)`, exactly diary 11's value.  `1.5234` at
`(12,26,9)` is exactly diary 11's "global max over `j >= 6`", from a different
implementation.  Note `ell = 20` even is missing from diary 11's 341 pairs
(`341 = 2 sum_(ell=6)^20 (ell-1) - 19`), consistent with its own row list.

## Priority 5 -- the exact relation between `(SUP-L)`, `q_j` and `(CDL)`

### They are statements about *different functions*

`(SUP-L)` constrains the level-`j` Fourier block of `D`.  `q_j` and `(CDL)`
constrain the level-`j` Fourier block of `D^2`:

```text
V_j = 2^(-ell) sum_(cond chi = j) |S_chi|^2 ,      S_chi = sum_e D_e chi(e)
E_j = sum_(cond chi = j) |fhat(chi)|^2 ,           fhat(chi) = sum_e D_e^2 chi(e)
q_j = E_j / C_(j-1) .
```

The squaring map is not level-preserving (a product of two high-level
characters can have any level), so no formal implication runs in either
direction.  The useful question is quantitative, and it has a clean answer.

### `q_j <= 1` does NOT imply `(SUP-L)` at any level, with any absolute `K`

The strongest sup bound derivable from the *entire* cylinder-`L^2` machinery is

```text
|P_j D(b)| = |s_j(b)| / 2^(ell-j) <= sqrt( m_j(b) / 2^(ell-j) )   [Cauchy-Schwarz]
max_b m_j(b) <= sqrt( C_j ) 2^(-j/2)                              [one term of C_j]
=>  max_e |D_[j]|  <=  sqrt(max_b m_j / 2^(ell-j)) + sqrt(max_b m_(j-1) / 2^(ell-j+1))
```

and feeding `C_j <= 2^j C_0 = 2^j M_2^2` (the *only* thing `q_j <= 1` gives) plus
the proved `M_2 <= mu Sigma(ell)` yields
`max_e |D_[j]| <~ 1.71 ell 2^(n/2) 2^((j-ell)/2)`, against `(SUP-L)`'s
`K (j-1) 2^((j-1)/2) 2^(n/2-ell)`.  The ratio is

```text
   loss  ~  1.71 . ell . 2^(ell/2 + 1/2) / ( K (j-1) )  --  exponential in ell.
```

Measured (using the *exact* `C_j`, not the `q_j <= 1` relaxation, so this is the
best the second-moment machinery can ever do):

```text
 loss = (cylinder-L^2 route) / ((SUP-L) RHS at K=1)
 (ell,n)      j=2     j=3     j=4     j=6     j=ell
  (9,19)     81.9    31.8    17.1     5.8     2.2
  (9,20)     87.8    32.2    16.6     6.2     2.9
 (10,21)    130.1    47.6    22.9     8.4     2.7
 (10,22)    133.1    48.1    24.4     8.5     3.0
 (11,23)    192.5    70.1    34.4    11.8     2.5
 (11,24)    207.9    76.2    37.0    12.2     3.3
```

The loss grows like `2^(ell/2)` at fixed low `j`, decays in `j`, and is **still
above 2.2 and still growing in `ell` at the top level `j = ell`**.

> **(REL-1).  PROVED (as a quantitative separation).**  `q_j <= 1`, and indeed
> the exact conductor energies `C_1 <= ... <= C_ell` together with the proved
> Weil envelope, do not imply `(SUP-L)` with any absolute `K` at **any** level.
> The deficit is `~ ell 2^(ell/2) / (j-1)` at level `j`, i.e. exponential in
> `ell` at every fixed `j` and `>= 2.2` even at `j = ell`.

Conversely `(SUP-L)` (all levels) `=> M_4 < (mu-P_n)^4 => R_0 < G =>
prod_j (1+q_j) < G`, an **aggregate** constraint on the `q_j` with no per-level
content.  So:

> **(REL-2).**  `(SUP-L) => ` the `(D-PROD)` conclusion, but not `(CDL)`;
> `(CDL) => ` the same conclusion, but not `(SUP-L)` at any level.  They are two
> independent sufficient hypotheses for the *same* endpoint, reached by
> different routes -- `(SUP-L)` through `M_4` directly, `(CDL)` through the
> kurtosis product.  Neither is a lemma for the other.

### `(CDL)` vs `(SUP-L)` at low `j`

Also independent, and for a sharper reason.  At low `j`, `(SUP-L)` is *already
proved* at `K = 2` by (CEIL) for `j <= 3` and is worth `~1.5` at `j <= 6`
measured; `(CDL)` at the same `j` asks for `E_j <= M_2^2/ell`, i.e. a
`poly(ell)` cancellation in the shifted second moment
`2^(-ell) sum_psi S_psi conj(S_(psi chi^(-1)))`.  The only transfer I could
construct from layer data to `E_j` is
`|fhat(chi)| <= (sum_L sqrt(V_L))^2 ~ ell^2 2^n ~ ell M_2`, which is **worse than
the trivial `|fhat(chi)| <= M_2`**.  So layerwise sup/energy information is
strictly useless for `(CDL)`, and `(CDL)`'s content is genuinely the
character-sum decorrelation diary 13 identifies, not a delocalization statement.

Practical consequence for `21-supl-assault.md` and `22-cdl-assault.md`:
**they may not borrow from each other.**  The one thing they share is the target
`(W4-exact)` and the constant `P_n` in it.

## FINDINGS

### (a) Verdict table

| # | Claim | Source | Verdict | Note |
|---|-------|--------|---------|------|
| 1 | Lemma 1 (order-grading Fourier form) | 11 | **CONFIRMED** | is literally my engine B; matches sympy entry-by-entry, 6 rows |
| 2 | Lemma 2 (`a_d(chi)=0` for `d >= level`) | 11 | **CONFIRMED** | surjective truncation `V_d -> E_j`, nontrivial induced character |
| 3 | Corollary 3 (`sum_(d<ell) T_d = D`) | 11 | **CONFIRMED** | `L(1,z)=1/(1-2z)`, so `m_j(1)=0` for `j>=2` |
| 4 | Lemma 4 (conductor orthogonality, `sum mult\|P_lev\| = 3M_2^2`) | 11 | **CONFIRMED** | exact-rational assertion, all pairs, `ell=4..13`, 0 violations |
| 5 | Lemma 5 (parity selection rule) | 11 | **CONFIRMED** | full cell tensor rebuilt, 0 violations, `ell=5..8` both parities |
| 6 | Lemma 6 (`V_1=0`, `V_2=2^(n-ell+1)`, Weil envelope) | 11 | **CONFIRMED** | exact on every row; `V_3` *saturates* the envelope at `(11,24)` |
| 7 | Lemma 7 (exact `1/4`-per-level recursion) | 11 | **CONFIRMED** | verified cell-by-cell, not just in aggregate; displayed multiplier is a typo, value right |
| 8 | Chain `(CAB-L) <= (SPLIT-L) <= (ENV-L) <= (L4-LAYER)` | 11 | **CONFIRMED** | all four steps elementary and re-derived |
| 9 | `(SUP-L)+Lemma 6 => (W4-exact)`, exponent `(2n-3ell)/4` | 11 | **CONFIRMED** | |
| 10 | `K=2` gives `ell >= 22` odd / `20` even (and `1.6/2.5/4` rows) | 11 | **CONFIRMED** | 8/8 crossovers reproduced at 80 digits, with Lemma A/B `P_n` |
| 11 | The chain bounds `N_n(1) > Pi_n`, not `> 0` | 11 | **CONFIRMED** | uses `(mu-P_n)^4`; A did **not** repeat the sweep-09 error |
| 12 | `(CAB)` / `(CAB-L)` **as stated** (budget `2^(ell+4(n-ell))`) | 11 | **GAP** | that budget yields only `M_4 < mu^4`, the criterion diary 04 refuted; fix is one substitution |
| 13 | "global max exactly 2.0000 over 341 pairs" | 11 | **CONFIRMED** (value) / **GAP** (reading) | value reproduced at `(11,24,3)`; but `2` is the *a-priori ceiling* at `j=3`, so the max is not evidence about the open regime |
| 14 | "`K=2` fits all measured data with a 31% margin" | 11 | **GAP** | the `31%` is over `j >= 6`; measured `max_(j>=4)` is `1.9922` at `(11,24,5)`, a `0.4%` margin. Odd `j` is absent from the printed table |
| 15 | `R_0 = prod_j (1+q_j)`, `0 <= q_j <= 1` (Lemmas D1/D2) | 13 | **CONFIRMED** | exact-rational identity asserted on every row |
| 16 | `E_1 = 0` / `q_1 = 0` at the odd endpoint (Result C4) | 13 | **CONFIRMED** | involution `F(x) -> F(x+1)` re-derived; holds on all odd rows, fails on all even rows |
| 17 | Lemma D5 and `(CDL) => (WR) => (W4)` with `(mu-P_n)^4` | 13 | **CONFIRMED** | corrected budget is used |
| 18 | The constant `4.1 log2 ell` (and `9.7` at `Q=1/2`) | 13 | **CONFIRMED** | holds with **floor**, `ell = 14..10^4`, both parities; margin grows |
| 19 | `(TWIST)` `fhat(chi) = 2^-ell sum_psi S_psi conj(S_(psi chi))` | 13 | **GAP** | the derivation gives `chi^(-1)`; harmless (`\|fhat\|` unchanged) but should be fixed |
| 20 | Lemma A (`Pi_n = 1`, odd) | 04 | **CONFIRMED** | proof re-derived; measured on every odd row `ell=5..11` |
| 21 | Lemma B (`P_n^sharp`, even) | 04 | **CONFIRMED** | all three layers re-derived; `P_n^sharp >= Pi_n` on every measured row |
| 22 | `(WK)` as boxed (non-strict `<=`) | 04 | **GAP** | yields `n I_n(1) >= 0`, not `>= 1`; fixed by strictness or by diary 04's own `-n` refinement |
| 23 | Lemma W (char-free replacement for HM Thm 2.7) | 12 | **GAP** | case `u=0, \|V\|>=3` is dimension-counted as if `z_1 in T_s`; the true bound is `codim >= 3(h+1)-3delta`, needing `h >= 3 delta`, which FAILS at the endpoint for `ell >= 13`. Vacuous at `m=3`, bites at `m=4` |
| 24 | Lemma D1 / D1a (shift-stable fibres; `2N_sf + Theta`) | 14 | **CONFIRMED** | needs the (implied) identification `s = h`; the "i.e." in the text is not self-contained |
| 25 | Theorem D2 (twist-orbit closed form) | 14 | **CONFIRMED** | both kernel-dimension regimes re-derived by hand |
| 26 | Lemma D3 (`(x+1)^2` forces `2^(n-2)` Moebius zeros) | 14 | **CONFIRMED** | |
| 27 | Lemma D4 (`lambda_1, lambda_2` independent for `v >= 2`) | 14 | **GAP**, statement survives | the claimed span inclusion is **false** for `3v > ell+1` (witness `ell=13, v=5, tau=x^4`); repaired proof given above restores the conclusion for all `2 <= v <= d` |
| 28 | `q_j <= 1` implies `(SUP-L)` for some levels | new | **FALSE** | exponential deficit `~ ell 2^(ell/2)/(j-1)`, measured 208x at `j=2` and still `3.3x` at `j=ell`, `(11,24)` |
| 29 | `(CDL)` and `(SUP-L)` are comparable | new | **FALSE** | different functions (`D` vs `D^2` spectrum); best layer-to-`E_j` transfer is worse than trivial |

Nothing in this audit falsifies the two load-bearing chains.  The two chains
themselves -- A's collapse to `(SUP-L)` and C's `(D-PROD)`/`(CDL)` sufficiency --
are **CONFIRMED end to end, including every constant**.  The four `GAP`s that
touch them (#12, #13/#14, #19, #22) are all statement-level or
presentation-level and each has a one-line fix.  The two mathematical `GAP`s are
in the *side* results: Lemma W (#23, real and unrepaired) and Lemma D4 (#27,
repaired here).

### (b) The attainment structure of the `2.0000` maximum

**(CEIL), PROVED.**  `kappa_j <= 2^((j-1)/2)` for every level, from Weil plus
the triangle inequality over the `2^(j-1)` level-`j` characters -- exactly the
inputs diary 11 already assumes.  Hence:

* `(SUP-L)` at `K = 2` is a **theorem** for `j <= 3` and open only for `j >= 4`;
* `kappa_2 = 1` (odd) / `sqrt 2` (even) **exactly, for every `ell`** -- proved
  above from `|S_chi|^2 = 2^n` and the uniqueness of `2^n = a^2+b^2` in `Z[i]`.
  At the even endpoint level 2 *saturates* the ceiling and can never do better.

**The global maximum is at `(ell,n,j) = (11,24,3)` and is structural:**

1. `V_3 = 131072` equals the Weil envelope `2^(n-ell) 2^(j-1)(j-1)^2` **exactly**,
   so all four level-3 characters have the extremal `|S_chi| = 2 . 2^(n/2)`;
2. they align in phase at the **identity class**: `D_[3]` at `1` equals `-16`, the full
   triangle sum `2^(-ell) . 4 . 8192`, and the argmax set is `512` classes
   (two `H_3`-cosets) containing `e = 1`;
3. `16 . 2^ell / (2 . 2 . 2^(n/2)) = 2 = 2^((j-1)/2)` -- the ceiling.

So the headline `2.0000` is *the a-priori bound being met*, at the identity
class, at the lowest level where the ceiling reaches 2.  It is a fact about the
level-3 `L`-functions all being extremal at one row, not about the delocalization
that `(SUP-L)` is really asking for.

**Direct input to `21-supl-assault.md`:**

* prove `(SUP-L)` outright at `j = 2` (done above, exactly), and at `j = 3` it
  is (CEIL) with `K = 2`; that is two of the levels for free, and it explains why
  the measured table's extremes sit there;
* the open statement is `max_(j>=4) kappa_j <= K`.  Measured maximum in my range
  is `1.9922` at `(11,24)`, `j = 5`; diary 11's `j = 4` maximum is `1.8994`.
  **`K = 2` has essentially no measured margin on the open levels.**  Either the
  assault targets a larger `K` (the chain is insensitive: `K = 4` costs three
  levels, `ell >= 25/23`), or E-A1 must be run at `j = 4, 5` first.
* the low-`j` extremes are attained at the **identity class**, and the identity
  class is precisely where the endpoint conclusion is read off (`|D_1|^4 <= M_4`).
  A per-level bound at `e = 1` only would already feed a Chebyshev-free version
  of the chain; that is a strictly weaker target worth stating.

### (c) The exact `(SUP-L)` / `(CDL)` / `q_j` relation

```text
                  object                       what it constrains        proved?
 (SUP-L)   D-spectrum, level j, sup norm      max_e |D_[j] at e|            open, j>=4
 q_j <= 1  D^2-spectrum, level j, energy      E_j / C_(j-1)               PROVED
 (CDL)     D^2-spectrum, level j, energy      E_j <= M_2^2/ell, j small   open
```

* `q_j <= 1` (even with the exact `C_j` and the proved Weil envelope) is
  **exponentially short** of `(SUP-L)`: deficit `~ 1.71 ell 2^(ell/2+1/2)/(K(j-1))`,
  measured `208x` at `(11,24) j=2`, `37x` at `j=4`, `3.3x` at `j=ell` and
  *increasing* in `ell` at every fixed `j`.  No level is covered.
* `(SUP-L)` implies the `(D-PROD)` conclusion `prod(1+q_j) < G`, but nothing
  per level, so it does not imply `(CDL)`.
* `(CDL)` and `(SUP-L)` sit on the same filtration but on different functions
  (`D^2` vs `D`); the best transfer from layer data to `E_j` I could build,
  `|fhat(chi)| <= (sum_L sqrt V_L)^2 ~ ell M_2`, is worse than the trivial
  `M_2`.  Independent.
* Both feed the *same* final constant `(mu - P_n)^4` of Lemma A/B.  That, and
  `mu`, is the entire shared surface.

Diary 13's own verdict ("incomparable, and deliberately so") is **CONFIRMED**,
and now with a quantitative separation rather than a taxonomic one.

### (d) The instrument

`crates/axeyum-cas/examples/acb_ver_supl.rs`.  Independent of `gf2_hayes.rs`,
of `acb_cab_levels.rs` and of `acb_dic_profile.rs` by construction (closed-form
Dirichlet series + direct subgroup averaging).  Asserts, fail-closed:
population invariant, `sum_e D_e = 0`, the layer reconstruction, Lemma 4
(orthogonality **and** `sum_j V_j = M_2`), Lemma 6 (`V_1 = 0`,
`V_2 = 2^(n-ell+1)` exact, the Weil envelope per level), Lemma D2
(`C_0 = M_2^2`, `C_ell = 2^ell M_4`, `0 <= q_j <= 1`, and
`prod_j (1+q_j) = R_0` as an exact rational identity), Result C4 (`q_1 = 0`,
odd).  Reports `kappa_j`, the ceiling `2^((j-1)/2)`, the fill ratio, and
whether `K = 2` is a theorem at that level; prints `max_(j>=4) kappa_j`
separately from the global max.

**Exit status depends on the finding**, per CLAUDE.md: `1` on any violated
lemma, `3` if any row produces `kappa > 2` (i.e. `(SUP-L)` at `K = 2` refuted).
Mutation controls run, and each kills exactly one thing:

```text
threshold 2.0 -> 1.0                       exit 0 -> 3     (the kappa guard)
V_2 target  2^(n-ell+1) -> 2^(n-ell+2)     exit 0 -> 1     (the Lemma 6 guard)
restore                                    exit 0
```

```sh
cargo build --release -p axeyum-cas --example acb_ver_supl
./target/release/examples/acb_ver_supl sweep 4 12
# ACB_VER|verdict|failures=0|global_max_kappa=2.0000|global_max_kappa_open_levels=1.9922
```

`ell = 4..12` in `2.8 s`, `< 200 MB`.  Cost is `O(n 4^ell)` (the series
inversion), so `ell = 13` is `~20 s` and `ell = 14` is the practical ceiling for
this route; the example refuses `ell > 16` outright.  Diary 11's sibling
recursion is far cheaper -- that is the point of having both.

### (e) What I did not do

* No re-verification of the lane's "certified finite range through degree 400",
  which both diary 11's `ell <= 21` gap-filling and diary 13's `ell >= 200`
  handoff depend on.  It is an **unverified external dependency of both chains**
  and should be audited by someone before `23-artifact.md` claims the endpoint
  is reduced to `(SUP-L)` or `(CDL)` alone.
* No re-verification of the lane's proved `L`-degree distribution (the input to
  Lemma 6's `|S_chi| <= (j-1) 2^(n/2)`) or of `M_2 <= mu Sigma(ell)`.  I checked
  both against data (`V_j` never exceeds the envelope on 20 rows; `V_2` is exact
  on all of them) but not against their proofs.  (CEIL) inherits the same
  dependency.
* No row above `ell = 13`: engine B is `O(n 4^ell)` and the charter budget
  binds.  So I could not test `(SUP-L)` where diary 11's `j = 4` maximum
  `1.8994` lives, nor extend the table.  E-A1 remains open and is now the
  highest-value experiment in the project.
* No independent reading of Hast--Matei or of Sawin's Lemma 2.3 from the primary
  texts; Lemma W's gap (#23) is internal to diary 12's own case analysis and
  needs no external source, but the `delta` upper bound it is conditioned on
  does.

### Epistemic ledger for this file

**PROVED here (new)**: (CEIL) `kappa_j <= 2^((j-1)/2)`; (K2-EXACT) `kappa_2 = 1`
(odd) / `sqrt 2` (even) exactly for every `ell`; (REL-1) the exponential
separation of the cylinder-`L^2` machinery from `(SUP-L)`; the repaired proof of
diary 14's Lemma D4.

**CONFIRMED by independent re-derivation** (verdict table, 20 entries):
diary 11's Lemmas 1-7, the four reductions, the `(SUP-L)` implication and all
eight crossover constants; diary 13's Lemmas D1/D2/D5, `(D-PROD)`, Result C4 and
the `4.1`/`9.7` constants; diary 04's Lemmas A, B; diary 14's D1, D1a, D2, D3.

**GAP** (proof hole or wrong statement, each exhibited precisely): diary 12's
Lemma W at `m >= 4` (the `u = 0, |V| >= 3` component); diary 14's Lemma D4's span
inclusion for `3v > ell+1` (witness `ell=13, v=5, tau=x^4`); diary 11's `(CAB)` /
`(CAB-L)` budget; diary 11's `31%`-margin reading of the `kappa` table; diary
13's `(TWIST)` conjugation; diary 04's non-strict `(WK)`.

**FALSE**: "`q_j <= 1` implies `(SUP-L)` for some levels"; "`(CDL)` and
`(SUP-L)` are comparable".  (Neither was asserted by a diary; both were the
charge's open questions, and both answers are negative.)

**EVIDENCE ONLY**: every table in this file; `ell = 4..13`, both parities,
engine B, cross-validated against a sympy brute force on six rows and against a
third from-scratch `Pi_n`/`I_n(1)` enumeration on fourteen rows.

**NO THEOREM CREDIT** is claimed for the Lemire endpoint, for `(SUP-L)`, for
`(CDL)`, or for any uniform estimate.

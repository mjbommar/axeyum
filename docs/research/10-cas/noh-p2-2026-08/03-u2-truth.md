# 03 -- the true U_2 valuation profile at p = 2 (attack C: measure the truth)

Workstream 03. Date: 2026-08-20. Status of this file: FINDINGS, complete for
m = 1 and m = 2.

Everything below is computed exactly (no floating point anywhere in the
mathematics). Primary implementation:
`crates/axeyum-cas/examples/noh_u2_matrix.rs` (self-checking, all assertions
must pass). Independent cross-checks: a from-scratch Python/`Fraction`
implementation and a sympy implementation that differs in *every* algorithm
(series-expansion instead of ODE recurrence, bitwise Hensel instead of Newton,
a different irreducible polynomial for `F_{2^k}`). See "Reproduction" at the
end.

---

## 0. Headline

**The p = 2 loss is not in the U_2 operator.** Measured exactly, on the local
Dwork operator itself, at Witt length m = 1 *and* m = 2:

- the optimal diagonal lattice certifies **exactly the Hodge polygon** -- rate
  `1/D` in `v_2` units, `D` = Swan conductor -- with **no floors and no loss**;
- **no lattice change of any kind** (diagonal, triangular, arbitrary) can do
  better: the rate is capped by the Newton polygon, which is a similarity
  invariant, and the diagonal certificate already attains the cap;
- the profile is the **same function of `(p, m, conductor)` as at odd p**. The
  only p-dependence in the whole computation is `v_p(pi_m) = 1/(p^{m-1}(p-1))`,
  and at p = 2 this is measured to be `v_2(pi_1) = 1`, `v_2(pi_2) = 1/2` --
  exactly the odd-p formula. Nothing anywhere produces a `1/3`.

The crux is a **splitting-function correction** (section 2): at p = 2, m = 1
Dwork's `pi` is the root of `E_2(x) = -1`, which lies in `Z_2` with
`v_2(pi_1) = 1`. It is **not** `-2`, and it is **not** a `pi` with
`pi^2 = -2` (that is the m = 2 uniformizer). The charter's and Note 4's
`pi^2 = -2` is the order-4 object; using it at m = 1 halves the rate for free.

Consequences for the project's predictions:

| prediction | verdict |
| --- | --- |
| P2 (03): m = 1 supports `floor(k/2)`-type rates on the monomial basis after diagonal rescaling, no exotic lattice | **CONFIRMED, and strictly stronger.** The optimum is the full Hodge rate, exactly linear with no floor, from an explicit *integral diagonal* lattice. |
| P3: genuine p = 2 loss first appears at Witt length m = 2 in the cross terms | **REFUTED (witness).** m = 2 measured for `(t^{s0}, t^{s1})` with both components nonzero (the cross-term case): same exact Hodge rate `1/D`, verified against real order-4 Witt exponential sums. |
| Coordinator retarget: does a diagonal/triangular integral lattice achieve `a(2l+r) - a(l+r) = l`? | **YES at Swan conductor 1, exactly, by the integral diagonal lattice `L = (+) pi^{2k} t^k`, with `a(k) = k >= k-1`.** At conductor `s` the exact optimum is `a(k) = k/s`, increment `l/s`, which is the same statement re-indexed by Hodge weight `u = k/s` (see section 6 for the unit dictionary and why the raw-index reading cannot be KMU's). |

---

## 1. The model, stated exactly

Local model at a wild point, local parameter `t`; equivalently the
local-at-infinity model of `A^1/F_2`. Dwork's operator on monomials:

    psi(t^j) = t^{j/2}  if j even,   0 otherwise.

Order-`2^m` character <-> length-m Witt vector `(f_0, ..., f_{m-1})` of Laurent
polynomials; Swan conductor `D = max_j 2^{m-1-j} deg f_j`. Splitting function

    Theta(t) = prod_{j=0}^{m-1} E_2(pi_{m-j} f_j(t)),

`E_2` = Artin-Hasse exponential `exp(sum_{i>=0} x^{2^i}/2^i)`, and `pi_r` the
root of `E_2(x) = zeta_{2^r}`. The operator is `M = psi o mult(Theta)`; on the
monomial basis

    M[i][j] = Theta_{2i-j}          (i, j >= 0; Theta_n = 0 for n < 0).

Truncation: `M` is nuclear (coefficient valuations grow linearly), so the
`N x N` truncation agrees with the operator to `v_2`-precision `~ N/D`. Every
number below is reported with its truncation bound and each check asserts
agreement *above* that bound.

Convention chosen and used throughout: **basis `{t^k}` indexed by `k >= 0`,
`U_2` halves the index**, valuations in `v_2` (so `v_2(2) = 1`) unless a
`v_pi` unit is named explicitly. Reconciling this index with KMU's `k` is
workstream 01's job; section 6 gives the dictionary as a function of the
convention, so the finding survives either answer.

## 2. The p = 2 splitting function: pi_1 is in Z_2 and has v_2 = 1

`E_2(x)` has 2-integral coefficients (verified, not assumed: computed over
`BigRational` / `Fraction`, all denominators odd, degree <= 150; two
independent routes -- the ODE `E' = L'E` and the Euler product
`prod_{n odd} (1-x^n)^{-mu(n)/n}` -- agree coefficient by coefficient).

`E_2(x) + 1 = 2 + x + x^2 + (2/3)x^3 + ...` has a unique root of valuation 1,
which is therefore in `Z_2` by Weierstrass. Newton iteration and (independently)
bitwise Hensel lifting agree:

    pi_1 = 0x0e6b37af39b848aa  (mod 2^64),   v_2(pi_1) = 1 = 1/(p-1)
    control: E_2(-2) + 1 has v_2 = 2 (finite), so pi_1 != -2.

Since `lambda_m = c_m pi_1^m` with `c_m in Z_2`, this gives `v_2(lambda_m) >= m`
*for free* -- the full classical rate `m/(p-1)`. Measured:

    v_2(lambda_m), m = 0..24:
    0, 1, 2, 4, 5, 5, 10, 7, 11, 9, 11, 19, 12, 13, 16, 16, 16, 21, 19, 20, 21, 22, 22, 24, 24
    >= m for all m: CONFIRMED;  equality at m = 0,1,2,5,7,9,12,13,16,22,24

The equality set is exactly `{m : c_m in Z_2^x}` and coincides with Note 4's
list -- so Note 4's numbers were right, but they were the profile of
**`theta_2`** (the order-4 splitting function, `v_2(pi_2) = 1/2`), not of the
m = 1 one. Confirmed directly: with `pi_2` (section 5) the doubled valuations
`2 v_2(lambda^{(2)}_m)` are `0,1,2,5,6,5,14,7,14,9,12,27,...`, i.e.
`v_2(lambda^{(2)}_m) >= m/2` with equality on the same index set.

**This is the whole "p = 2 problem" at the level of the splitting function: at
p = 2 the naive `pi` guesses (`-2`, or `pi^2 = -2`) both fail, but the correct
Dwork `pi` exists, is 2-adically explicit, and gives the odd-p rate.**

## 3. Anchor: the trace formula against real point counts (m = 1)

Not a plausibility check -- an exact identity, verified. `S_k^*(x^s) = sum_{x in
F_{2^k}^x} (-1)^{Tr(x^s)}` computed from scratch by enumerating `F_{2^k}`
(and, in the sympy cross-check, over a *different* irreducible polynomial),
against `(2^k - 1) Tr(M^k)`:

| s | N | tail bound N/s | v_2(LHS - RHS), k = 1..6 |
| --- | --- | --- | --- |
| 1 | 30 | 30 | 32, 48, 55, 62, 62, 64 |
| 3 | 90 | 30 | 32, 47, 55, 60, 62, 64 |
| 5 | 140 | 28 | 32, 45, 52, 61, 59, 60 |
| 7 | 140 | 20 | 23, 35, 36, 45, 43, 42 |

Every difference vanishes to well beyond the truncation bound: the trace
formula holds **exactly**. (64 = full precision of the `Z/2^64` model.)

Second, independent anchor -- the L-function. From the same point counts,
`L(x^s, T) = prod (1 - alpha_i T)` of degree `s-1`; and from the operator,
the Fredholm determinant `det(1 - TM)`. Dwork theory predicts
`slopes(det(1-TM)) = union_{j>=0} ( {j} u {j + slopes(L)} )`. Measured
(`v_2`-normalized, `v_2(2) = 1`):

| s | L(x^s, T) | NP(L) | NP(det(1-TM)), leading | Hodge i/s |
| --- | --- | --- | --- | --- |
| 3 | `1 + 2T^2` | 1/2, 1/2 | 0, 1/2, 1/2, 1, 3/2, 3/2, 2 | 0, 1/3, 2/3, 1, 4/3, 5/3, 2 |
| 5 | `1 + 4T^4` | 1/2 x4 | 0, (1/2)x4, 1, (3/2)x4, 2 | i/5 |
| 7 | `1 - 2T^3 + 8T^6` | (1/3)x3, (2/3)x3 | 0, (1/3)x3, (2/3)x3, 1, (4/3)x3, (5/3)x3, 2 | i/7 |

The predicted union matches the computed determinant slopes exactly (the final
hull segment of each truncation is a boundary artifact and is excluded).
`s = 3` reproduces the known supersingular elliptic curve `y^2 + y = x^3 / F_2`
(NP `{1/2,1/2}` strictly above HP `{1/3,2/3}`), which is an external correctness
check on the whole pipeline. `NP >= HP` holds in every case.

## 4. a_true: the exact optimum over diagonal rescalings, and its optimality

**Set-up (exact, no heuristics).** Let `V[i][k] = v(M[i][k])`. A diagonal
rescaling `w` gives `v(N[i][k]) = V[i][k] + w_k - w_i`; the U_2-improvement of
basis element `t^k` is `a_w(k) = min_i v(N[i][k])`. Feasibility of
`a_w(k) >= a(k)` for a target profile is a difference-constraint system: it
holds for some `w` iff the digraph with edge `k -> i` of weight
`V[i][k] - a(k)` has no negative cycle. For `a(k) = c k` this makes the optimum
a **minimum-ratio-cycle** problem, solved exactly by Lawler binary search +
Bellman-Ford over `Fraction`s (never floats).

**Result (m = 1, v_pi units, `pi = pi_1`, so `v_pi = v_2`).** The optimum is
attained and is *exactly linear with no floor*:

    c_max = 1/s   exactly   (feasible at 1/s; infeasible at 1/s + eps)
    a_true(k) = k/s   for every k, with equality (no floor loss anywhere)

verified for `s = 1, 3, 5, 7, 9, 11` and truncations `N = 16, 24, 32, 48, 60`
(the value is independent of `N`, i.e. it has converged).

`a_true(k)` for `k = 0..24`:

| s | a_true(k), k = 0,1,2,...,24 |
| --- | --- |
| 1 | 0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24 |
| 3 | 0,1/3,2/3,1,4/3,5/3,2,7/3,8/3,3,10/3,11/3,4,13/3,14/3,5,16/3,17/3,6,19/3,20/3,7,22/3,23/3,8 |
| 5 | 0,1/5,2/5,3/5,4/5,1,6/5,...,24/5 (exactly k/5) |
| 7 | 0,1/7,2/7,...,24/7 (exactly k/7) |

**The certifying lattice, explicitly.** `w_k = 2k/s` in `v_pi` units, i.e.

    L_s = (+)_k  pi^{2k/s} t^k         (equivalently: substitute t -> w t with w^s = pi^2)

For `s = 1` this is **integral with integer weights**:

    L_1 = (+)_k pi^{2k} t^k,   U_2-stable,   U_2(t^k) in pi^k L_1,   a(k) = k.

For `s > 1` it is integral over `K(pi^{1/s})` (the classical Dwork
radius normalization); if one insists on integer weights in `K` itself, take
`w_k = ceil(2k/s)`, which costs at most an additive 1: `a(k) >= k/s - 1`. That
is a bounded constant, **not** a rate loss. The single integer inequality

    s * v_2(M[i][k]) + k - 2i >= 0

certifies simultaneously (i) the improvement `a(k) >= k/s` and (ii) the row
bound `v(N[i][k]) >= i/s`, i.e. **the Hodge polygon itself**. Asserted in the
Rust example for all `i, k <= 96` and `s = 1,3,5,7,9,11` (tight entries:
5361 / 1035 / 572 / 461 / 396 / 354 -- the certificate is saturated, not slack).

**Optimality among ALL lattices, not just diagonal ones (charge item 3).**
No triangular or other lattice can beat `1/s`, for a reason that does not
depend on searching:

> If in *any* basis the matrix `N` of `M` satisfies `v(N[i][k]) >= a(k)` for all
> `i`, then each `n x n` principal minor of `N` draws one entry from each of `n`
> distinct columns, so the Fredholm coefficient `c_n` of
> `det(1 - TN) = det(1 - TM)` has `v(c_n) >= sum of the n smallest a(k)`. With
> `a(k) >= ck` this is `>= c n(n-1)/2`. Hence `c <= 2 v(c_n)/(n(n-1))` for every
> `n`, and `det(1 - TM)` is a similarity invariant, so this bounds *every*
> lattice.

Evaluated on the measured Fredholm coefficients:

| s | n | v_2(c_n) | bound `2 v(c_n)/(n(n-1))` | 1/s |
| --- | --- | --- | --- | --- |
| 3 | 8 | 11 | 0.393 | 0.333 |
| 5 | 12 | 14 | 0.212 | 0.200 |
| 7 | 16 | 18 | 0.150 | 0.143 |

The bound descends to `1/s` as `n` grows (`v(c_n) ~ n^2/(2s)`, the Hodge sum),
and the diagonal lattice attains it. So `a_true(k) = k/s` is **the** answer, and
searching triangular lattices with bounded denominators is unnecessary: there
is nothing above `1/s` to find. (Charge item 3 is therefore answered in the
negative-for-need / positive-for-existence direction: a diagonal rescaling
*does* suffice; no exotic lattice is required or possible.)

## 5. m = 2: order-4 characters, length-2 Witt vectors (P3)

`pi_2` = root of `E_2(x) = zeta_4 = i` in `Z_2[i]`, found by Newton iteration in
`Z_2[i]/2^P`; measured `v_2(pi_2) = 1/2 = 1/(p^{m-1}(p-1))`. The Witt vector
`(f_0, f_1)` decomposes in `W_2` as `(f_0, 0) + (0, f_1)`, so

    Theta(t) = E_2(pi_2 t^{s0}) * E_2(pi_1 t^{s1}),    D = max(2 s0, s1).

**Anchor.** Order-4 exponential sums computed from scratch: Witt-vector
arithmetic over `F_{2^k}` (`(a_0,a_1)+(b_0,b_1) = (a_0+b_0, a_1+b_1+a_0b_0)`,
Frobenius componentwise squaring), Witt trace `sum_{i<k} F^i`, character
`psi_4(a_0,a_1) = i^{a_0 + 2a_1}`. Then
`S_k^* = sum_{x != 0} psi_4(Tr_W(Teich f_0(x))) (-1)^{Tr f_1(x)}` versus
`(2^k-1) Tr(M^k)` in `Z_2[i]`:

| (s0, s1) | D | N | tail N/D | v_2(LHS - RHS), k = 1..5 |
| --- | --- | --- | --- | --- |
| (1, 0) | 2 | 24 | 12 | 29/2, 16, 14, 35/2, 15 |
| (3, 0) | 6 | 72 | 12 | 29/2, 31/2, 14, 33/2, 15 |
| (1, 1) | 2 | 24 | 12 | 13, 29/2, 14, 35/2, 14 |
| (1, 3) | 3 | 36 | 12 | 25/2, 29/2, 14, 15, 14 |
| (3, 1) | 6 | 72 | 12 | 13, 15, 14, 16, 29/2 |
| (5, 0) | 10 | 96 | 9.6 | 25/2, 13, 23/2, 14, 13 |

All above the truncation bound: the m = 2 trace formula holds, **including the
cross-term cases** where both Witt components are nonzero.

**Profile and rate at m = 2** (`v_2` units; `D` = Swan conductor):

| (s0, s1) | D | `v_2(Theta_n) >= n/D` | max linear rate c | 1/D | NP(det) vs NP(L) | NP >= HP |
| --- | --- | --- | --- | --- | --- | --- |
| (1,0) | 2 | yes | 1/2 exactly | 1/2 | match | yes |
| (3,0) | 6 | yes | 1/6 exactly | 1/6 | match | yes |
| (5,0) | 10 | yes | 1/10 exactly | 1/10 | match | yes |
| (1,1) | 2 | yes | 1/2 exactly | 1/2 | match | yes |
| (1,3) | 3 | yes | 1/3 exactly | 1/3 | match | yes |
| (3,1) | 6 | yes | 1/6 exactly | 1/6 | match | yes |
| (3,5) | 6 | yes | 1/6 exactly | 1/6 | match | yes |

e.g. `(3,0)`: `NP(L) = [1/4,1/4,1/2,3/4,3/4]` (from real order-4 Witt sums) and
`NP(det(1-TM)) = [0, 1/4, 1/4, 1/2, 3/4, 3/4, 1, ...]` -- the predicted union,
exactly; `HP = i/6`; `NP >= HP` throughout.

**P3 is REFUTED**, with the cross-term cases as the witness. And the reason is
structural, not numerical -- here is the argument the data confirms:

> **Proposition (Hodge bound from the splitting function, any p, any m).**
> Write `Theta = prod_j E_p(pi_{m-j} f_j)` with `v_p(pi_r) = 1/(p^{r-1}(p-1))`
> and `D = max_j p^{m-1-j} deg f_j`. The coefficient of `t^n` is a sum over
> `(a_j)` with `sum_j a_j deg f_j = n` of products with
> `v_p >= sum_j a_j / (p^{m-j-1}(p-1))`. Term by term,
> `a_j/(p^{m-1-j}(p-1)) >= a_j deg f_j / D` because `D >= p^{m-1-j} deg f_j`.
> Hence `v_p(Theta_n) >= n/(D(p-1))`, and `w_k = pk/(D(p-1))` turns this into
> `v(N[i][k]) >= i/D`: **the Hodge polygon, uniformly in p and m.**

There are no cross terms to lose to: Witt length enters only through
`v(pi_r)`, which the p = 2 measurement confirms is the odd-p value.

## 6. The KMU increment condition, and the unit dictionary

Target (coordinator, from 02): a `U_2`-stable filtered lattice with
`a(pl + r) - a(l + r) = l`, i.e. `a(k) = (k - const)/(p-1)`, which at p = 2 is
`a(k) = k - 1`; KMU certify `floor((k-1)/3)`.

Measured increment of the exact optimum (m = 1, `v_pi` units, raw monomial
index), for `l = 1..6`, `r = 0, 1`:

| s | a(2l+r) - a(l+r) | ratio to `l` |
| --- | --- | --- |
| 1 | exactly `l` (1,2,3,4,5,6 for r = 0 and r = 1 alike) | **1** |
| 3 | exactly `l/3` | 1/3 |
| 5 | exactly `l/5` | 1/5 |
| 7 | exactly `l/7` | 1/7 |

So:

- **At Swan conductor 1 the required condition holds exactly, on the nose, from
  an integral diagonal lattice** (`L_1 = (+) pi^{2k} t^k`, `a(k) = k >= k-1`).
  Note it holds *without slack*: `a(k) = k` is the exact optimum, so at p = 2
  the margin over the requirement is a single additive unit and nothing more.
  (Same computation at odd p gives `c = (p-1)/s`, i.e. margin `(p-1)` -- at
  p >= 3 there is multiplicative room; at p = 2 there is none. If KMU's argument
  needs strict slack rather than `>=`, *that* is the real p = 2 tightness, and it
  is an additive/constant matter, not the `1/3` vs `1/2` rate matter.)
- At conductor `s > 1` the increment is `l/s` in the raw monomial index. This is
  the *same statement* re-indexed: in the Hodge-weight index `u = k/s` (the
  standard Dwork normalization, and the index in which the estimate is
  conductor-uniform) the increment is exactly `l`.
- The raw-index reading at `s > 1` cannot be KMU's convention, because the same
  computation gives `l (p-1)/s` at *every* p -- it would fail at odd p too,
  where their theorem is proved. Pinning the convention is 01's job; **under
  either convention the finding is the same, because the measured optimum has no
  floor and no p-dependent degradation.**

**Where `1/3` is not.** It is not in the AH splitting coefficients
(`v(lambda_m) >= m v(pi)`, exact rate `v(pi)`, equality infinitely often --
section 2), not in the operator's true spectrum (section 3), not in the best
lattice (section 4, with an optimality proof), and not in Witt length
(section 5). Combined with 02's finding that the `1/3` denominator comes from
KMU's auxiliary tame Belyi map (degenerate at `p - 1 = 1`): **these matrices are
computed without any auxiliary map, so the measured optimum is exactly the
quantity that decides the question, and it says the geometry fallback is not
forced by the local analysis.** What remains open is whether KMU's *global glue*
can consume the estimate in the form proved here.

## 7. Epistemic status

- **PROVED (exact computation + external anchor).** `E_2` 2-integrality to
  degree 150; existence/uniqueness and value of `pi_1` with `v_2(pi_1) = 1`;
  `pi_1 != -2`; `v_2(lambda_m) >= m` with the exact equality set; `v_2(pi_2) =
  1/2` and `v_2(lambda^{(2)}_m) >= m/2`; the Dwork trace formula at m = 1 and
  m = 2 against independently computed exponential sums; `NP(det(1-TM))` equal
  to the union predicted by the independently computed L-functions; `NP >= HP`
  in every case measured.
- **PROVED for the truncations, asymptotically for the operator.**
  `a_true(k) = k/s` exactly, `c_max = 1/s`, the explicit certifying lattice, and
  the no-better-lattice bound. The certificate is a finite verified inequality
  valid for all `i, k` (its proof `s v_2(M[i][k]) + k - 2i >= 0` follows from
  `v_2(lambda_m) >= m`, so it is not truncation-limited); the optimality bound is
  asymptotic in `n`.
- **REFUTED (witness).** P3 -- no Witt-length-2 loss, cross terms included.
- **OPEN.** (i) The dictionary between this index/unit convention and KMU's `k`
  (workstream 01). (ii) Whether KMU's local-to-global glue consumes the estimate
  in this form -- in particular whether it needs slack beyond `a(k) = k`, which
  at p = 2 is not available (section 6). (iii) m >= 3 (`pi_3` with
  `E_2(pi_3) = zeta_8`, `v_2 = 1/4`): the Proposition in section 5 covers it and
  the only input is `v_2(pi_m) = 2^{1-m}`, which follows from the Newton polygon
  of `E_2(x) - zeta_{2^m}`, but it has not been run.

## 8. Reproduction

```sh
cargo run --release --example noh_u2_matrix -p axeyum-cas   # ~15 s, self-checking
```

The example asserts: Artin-Hasse 2-integrality; `v_2(pi_1) = 1`; `pi_1 != -2`;
`v_2(lambda_m) >= m`; the lattice certificate `s v_2(M[i][k]) + k - 2i >= 0` for
`s = 1,3,5,7,9,11` and `i,k <= 96`; the trace formula against point counts for
`s = 1,3,5,7`, `k <= 6`, each to a precision above the stated truncation bound;
`v_2(pi_2) = 1/2` and `v_2(lambda^{(2)}_m) >= m/2`. A failure of any of these is
a failure of the finding, by construction -- the exit status depends on what the
run found, not on the run completing.

The Newton polygons, the minimum-ratio-cycle optimum, the increment tables and
the m = 2 Witt-sum anchor were computed by the session's Python/`Fraction` and
sympy implementations; their numbers are transcribed above and the Rust example
reproduces the parts that can be asserted cheaply.

Cross-check ledger (all passed):

| quantity | route A (primary) | route B | route C | agree |
| --- | --- | --- | --- | --- |
| `E_2` coefficients | ODE `E' = L'E` over `Fraction` (Python) and `BigRational` (Rust) | Euler product `prod_{n odd}(1-x^n)^{-mu(n)/n}` | `sum_n L^n/n!` over sympy `Rational` | yes, coefficient by coefficient to degree 40 |
| `pi_1` | Newton iteration mod `2^P` (Python, Rust) | bitwise Hensel lifting, one bit at a time (sympy) | -- | yes, `pi_1 = 968378538 mod 2^30` both ways |
| `v_2(lambda_m)` | Python | Rust | sympy | identical lists, and the same equality set |
| `S_k^*(x^s)` | `F_{2^k}` via bitmask arithmetic mod one irreducible (Python, Rust) | sympy `Poly`/`GF(2)` mod a *different* irreducible | -- | yes for `(s,k)` in `{3,5,7} x {3,4,5,6}` |

The `1/3` of Remark 6.5 never appears in any of these routes.

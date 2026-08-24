# Kaser--Lemire for almost all degrees: the target, and why every average over degrees is the same wall

Status: research note, 2026-08-23 (angle: almost-all over DEGREES, the analogue
of note 05's almost-all over CLASSES). Companions:
[05-almost-all-theorem.md](05-almost-all-theorem.md) (almost all `2^ell`
classes at a fixed `n`), [01-target-and-toolkit.md](01-target-and-toolkit.md)
(the open estimate `(HWO)` and the Haar telescope),
[03-uncertainty-analogy.md](03-uncertainty-analogy.md) section 5 (Barrier I),
[06-symmetry-barrier.md](06-symmetry-barrier.md) (Barrier II),
[09-construction-barrier.md](09-construction-barrier.md) (Barrier III),
[13-sieve-face.md](13-sieve-face.md) (exact Type I and the parity barrier),
[08-infinite-family.md](08-infinite-family.md) (the density-zero families).

Everything finite here is re-derived and asserted by
`scripts/lemire-signed-trace/lemire_almost_all_degrees.py` (exits nonzero on any
failed assertion; eight mutation controls, each shown to trip exactly one named
check). Data: `data/aad-endpoint-deviations.txt`, `data/aad-block-support.txt`,
`data/aad-slack-ladder.txt`, `data/aad-min-subdegree.txt`, `data/aad-margin.txt`.

**Nothing here proves the almost-all-degrees statement, and nothing here
disproves it.** What is proved is a reduction (Theorems 1--2), a support lemma
(Theorem 3), and a null result (Theorem 4) which together say: *averaging over
degrees is worth at most one or two coefficients of slack, never the factor
`~ell` that is missing, and no large sieve over degrees can establish the
statement at any prescribed degree.* Section 4.3 gives the exact quantity that
would have to be bounded instead -- a fixed-`q` pair correlation for the
Frobenius angles of one conductor -- which is the wall of note 00 reached from a
new direction.

## 0. Summary

1. **The target (AAD).** `#{n <= N : W_n has no irreducible} = o(N)`, where
   `W_n = {x^n + g : deg g <= floor(n/2)}`. It is a genuinely new statement:
   the lane has all `n <= 3000` (certified, finite), the composition families
   (density zero, note 08), and almost all *classes* at fixed `n` (note 05).
   Section 1 states exactly what AAD would and would not give -- in particular
   it would settle **no prime degree and no power of two**, since a density-one
   set may omit every one of them.
2. **The obstacle, made exact.** The character group depends on `n`
   (`ell = ceil(n/2)-1`, two degrees per group). Theorem 3: each conductor `j`
   lies in the *top block* -- the part of the telescope Weil cannot pay for --
   of at most `2 ceil(log2 j) + 4` degrees. So the data attached to one degree
   is private to `O(log n)` degrees, and the averaging parameter has size
   `O(log n)` against a block of `~j 2^{j-1}` Frobenius angles.
3. **Candidate 1 (average over `ell` through the nesting): exact obstruction.**
   The nesting is real and does pay for the low conductors (Theorem 1: they
   contribute `< 2^{-5/2}` for odd `n`, `< 2^{-3}` for even `n`, uniformly), but
   the top block is fresh at every `ell`. Theorem 4: for every `j >= 4`, every
   range of degrees and every threshold, the Montgomery--Vaughan large sieve
   returns an exceptional count `>= 4.32 (j-1)^2`, while the whole available
   range has `<= 2 ceil(log2 j) + 4` degrees. At `j = 200` that is a factor
   `8565` of vacuity. Measured: no correlation across consecutive `ell`
   (`r = -0.066` odd, `-0.056` even, 22 pairs each).
4. **Candidate 2 (moving exceptional set): the motion is real but has no
   handle.** Under the only canonical comparison between different `ell` -- the
   tower projections `E_{ell'} ->> E_ell` -- the identity is a fixed point of
   the whole tower (Prop. 6), so "the exceptional set moves" cannot be turned
   into "the target leaves it" without an independent probability measure on the
   family `{X_ell}`; the only structure-preserving source of one is a group
   action, and Barrier II caps the orbit of the identity at `2`. Measured, and
   new: the two degrees of one group are **anti-correlated**,
   `r = -0.657` (Spearman `-0.617`, permutation `p = 2.6e-4`, jackknife-stable
   in `[-0.701, -0.541]`, 23 groups) -- but even a *perfect* anti-correlation
   gives only "not both degrees of a group are bad", i.e. density `1/2`, not
   `o(1)`.
5. **Candidate 3 (slack `k`): the exact ladder, and averaging does not move it.**
   The pointwise Hsu (1996)/Cohen (2005) bound gives the window with slack
   `k*(n) ~ log_2 n - 1` for **all** `n` (`k* = 4` at `n = 64`, `8` at
   `n = 1024`, `18` at `n = 10^6`). Theorem 8: the slack at which the large
   sieve over degrees first becomes non-vacuous is `k*(n) + 1` or `k*(n) + 2`,
   never less. So averaging over degrees buys **zero** coefficients; `k = O(1)`
   and `k = c log n` with `c < 1` are out of reach by this route.
6. **Candidate 4 (sieve/large sieve, and the literature): moot for this route,
   and unavailable at `q = 2` anyway.** The function-field analogue of
   Selberg's almost-all-short-intervals theorem is the almost-all-over-*centres*
   statement, i.e. note 05, which is unconditional here and is not AAD. The
   integer analogue of AAD -- a prime in `[2^k, 2^k + 2^{k/2+1}]` for almost all
   `k` -- is not known and is not implied by RH: the averaging parameter has
   size `log X`, not `X`. Sawin, arXiv:1809.05137 (Duke 2021), is by its own
   abstract conditional on "the characteristic of the finite field [being]
   relatively large".
7. **Candidate 5 (cheap counting): closed, and AAD is not weaker there.**
   Prop. 9: by note 13 Lemma 1 the Type-I data of `W_n` is a function of the
   window length `h = n - ell` **alone** -- it does not see `n`, and it does not
   see the centre. A Type-I argument therefore cannot distinguish degrees at
   all; and the parity barrier (note 13 Thm 10) shows the associated LP is
   infeasible at every length computed. Constructions are density zero
   (Barrier III); the Q-transform `x^m f(x + 1/x)`, the one substitution not
   covered by note 08, is window-hostile (Prop. 10).
8. **The margin.** The conjecture asks for subdegree `<= floor(n/2)`. Measured
   here from scratch by an independent flint search over 479 degrees
   (every `n <= 400`, then `410..1000` step `10`, `1100..3000` step `100`), the
   *minimal* subdegree satisfies `s_min(n) <= 10` for every `n <= 410`
   (reproducing Arndt's table) and `s_min(n) <= 13` over the whole sampled
   range to `n = 3000`: `s_min(n)/log_2 n` lies in `[0.102, 1.400]` with mean
   `0.857`. The
   window bound is attained with equality at exactly four degrees,
   `n = 2, 3, 5, 8`, and nowhere else in the range. So the truth is `~log_2 n`
   and the conjecture asks for `n/2`: **the truth is not close to the
   conjecture; the conjecture is close to what the method can prove**, which is
   the whole difficulty.

## 1. The target, formalised, and what it would give

Throughout, `n >= 3`, `ell = ell(n) = ceil(n/2) - 1`, `h = h(n) = n - ell =
floor(n/2) + 1`, `W_n = {x^n + g : deg g <= floor(n/2)}` (so `|W_n| = 2^h`),
`I_n = #{f in W_n : f irreducible}`, `N(n) = sum_{f in W_n} Lambda(f) =
N_ell(1)`, `Theta_n = N(n) - n I_n` the proper-prime-power mass, and

```text
D_n = N(n) - 2^h,        d_n = D_n / 2^h.
```

**(KL)** Kaser--Lemire: `I_n >= 1` for every `n`.
**(AAD)** the target of this note: `#{n <= N : I_n = 0} = o(N)`.

`(KL) => (AAD)`, and the converse fails in the strongest way. Precisely, AAD
would give:

- the first statement of positive density of any kind about this problem
  (everything currently proved is either finite -- `n <= 3000` -- or of density
  zero -- the composition families of note 08, counting function
  `O((log N)^16)`);
- the applied consequence the conjecture was raised for: for every `eps > 0` and
  every large `L`, an in-window irreducible of some degree in
  `[L, (1 + eps) L]`.

and it would **not** give:

- the conjecture, nor any effective statement at a single degree. An `o(N)`
  bound never locates its exceptions, and AAD is consistent with `I_n = 0` for
  infinitely many `n`;
- **any prime degree.** The primes have density zero, so a density-one set of
  degrees may omit every prime. The same for `n = 2^a`. This matters more here
  than it usually would: Barrier III (note 09) shows the provable construction
  toolbox is *structurally* silent at exactly those two families (`n = mt` with
  `t >= 2` is composite, and `(i)` of note 08 Theorem A forces `t` odd). So AAD
  and the composition families are complementary and their union still misses
  every prime degree, which is where the problem is hardest;
- note 05, nor anything implied by it. Note 05 is almost-all over the `2^ell`
  classes at a fixed `n`; AAD is almost-all over degrees at the fixed identity
  class. Neither implies the other. Note 05 *plus* "the identity behaves like a
  typical class" would give AAD -- and that conjunction is exactly what
  Barriers I and II say is unavailable.

## 2. The block decomposition

Let `X_j` be the set of Hayes characters of exact conductor `j` (`|X_j| =
2^{j-1}`; a character of conductor `j` is the same object for every `E_m`,
`m >= j`, so the `X_j` are pairwise disjoint and independent of `ell`). By RH
(Weil) a `chi in X_j` has `L(u, chi) = prod_{i=1}^{j-1}(1 - alpha_i u)` with
`|alpha_i| = sqrt 2` -- the degree is exactly `j - 1` (Katz; verified exactly
for `3 <= j <= 11` in CHECK G) -- and `S_n(chi) = -sum_i alpha_i^n`. Write
`alpha_i = sqrt2 e(theta_i)`, let `A_j` be the multiset of the
`Sigma_1(j) = (j-1) 2^{j-1}` angles `theta_i` over all `chi in X_j`, and

```text
g_j(n) = sum_{theta in A_j} e(n theta),      so   sum_{chi in X_j} S_n(chi) = -2^{n/2} g_j(n).
```

Since `N_ell(1) = 2^{-ell} sum_chi S_n(chi)` and `S_n(1) = 2^n`,

```text
(BLOCK)     d_n = - 2^{-n/2} sum_{j=2}^{ell(n)} g_j(n),      |g_j(n)| <= (j-1) 2^{j-1}.
```

The trivial (Weil) bound is `|d_n| <= 2^{-n/2}[(ell-2)2^ell + 2]`, i.e.
`(ell-2)/sqrt2` at odd `n` and `(ell-2)/2` at even `n`: short of `1` by the
familiar factor `~ell/2`. With `c = ceil(log2 ell)` and the telescope cutoff
`a = a(ell) = ell - c - 1` of note 01, split

```text
d_n = d_n^low + d_n^top,   d_n^low = -2^{-n/2} sum_{j<a} g_j(n),
                           d_n^top = -2^{-n/2} sum_{j=a}^{ell} g_j(n).
```

**Theorem 1 (low block, unconditional and uniform).** For `ell >= 5`,

```text
|d_n^low| < 2^{-5/2} = 0.176777   (n = 2ell+1),      |d_n^low| < 2^{-3} = 0.125   (n = 2ell+2).
```

*Proof.* `sum_{j=2}^{a-1}(j-1)2^{j-1} = (a-3)2^{a-1} + 2`. Since
`2^{a-1} = 2^{ell-c-2} <= 2^{ell-2}/ell` and `a - 3 <= ell - c - 4`, the sum is
`< 2^{ell-2}` (the slack `(c+4)2^{ell-2}/ell` absorbs the `+2` for `ell >= 5`).
Multiply by `2^{-n/2} = 2^{-ell-1/2}` resp. `2^{-ell-1}`. QED

Both constants are attained in the limit along `ell = 2^k`: CHECK B measures the
suprema over `5 <= ell <= 10^6` as `0.17672` and `0.12496` against the caps
`0.176777` and `0.125`. This is the quantitative form of note 01's `B_{ell,n} > 0`:
the conductors below `a` are free, and the whole problem is `d_n^top`.

**Theorem 2 (reduction).** For every `n >= 26`, `|d_n^top| <= 0.34` implies
`I_n >= 1`. Consequently

```text
#{n <= N : I_n = 0}  <=  (0.34)^{-2} sum_{n <= N} |d_n^top|^2 + 25
                     <=  8.66 sum_{n <= N} |d_n^top|^2 + 25,
```

so **AAD follows from `sum_{n<=N} |d_n^top|^2 = o(N)`.**

*Proof.* `I_n >= 1` iff `N(n) > Theta_n`, i.e. `d_n > Theta_n 2^{-h} - 1`. For
odd `n` every proper power is `P^k` with odd `k >= 3`, so `Theta_n < 2^{n/3+1}`
and `Theta_n 2^{-h} <= 2^{1/2 - n/6}`; for even `n`,
`Theta_n <= 2^{n/2} + 2^{n/3+1}` and `Theta_n 2^{-h} <= 1/2 + 2^{-n/6}` (note
05 Theorem B; both bounds recomputed exactly for `6 <= n <= 28` in CHECK C).
With Theorem 1 it suffices that `d_n^top > -1 + 2^{-5/2} + 2^{1/2-n/6}` at odd
`n` and `d_n^top > -1 + 2^{-3} + 1/2 + 2^{-n/6}` at even `n`; both right-hand
sides are `< -0.34` for `n >= 26`. Markov on the squares finishes the count (the
`+25` absorbs `n < 26`, every one of which is certified anyway). QED

Unconditionally `|d_n^top| <= (ell-2)/sqrt2 + o(1)`, so the trivial bound on the
sum is `O(N^3)` and the required saving is a factor `~N^2/8.66` -- **exactly the
`ell^2` of the pointwise problem, with no `1/N` gain from averaging.** Sections
4--8 ask, candidate by candidate, whether anything supplies it.

## 3. Why the family offers almost no averaging: the block support lemma

**Theorem 3 (block support).** For `j >= 4`,

```text
#{ n : a(ell(n)) < j <= ell(n) }  <=  2 ceil(log2 j) + 4.
```

*Proof.* `j <= ell(n)` forces `n >= 2j+1`. `a(ell) < j` reads
`ell - ceil(log2 ell) - 1 < j`, which for `ell >= j` fails once
`ell >= j + ceil(log2 j) + 2` (for `j >= 8`: `j + log2 j + 2 <= 2j`, so
`ceil(log2 ell) <= ceil(log2 j) + 1`). So `ell` runs over at most
`ceil(log2 j) + 2` values and each carries two degrees. QED

Verified exactly for `4 <= j <= 400` and at `j in {1000, 1024, 2048, 10^4,
10^5}`: at `j = 200` the support is `9` values of `ell`, `18` degrees, against
the bound `20`. The lemma is the precise form of the structural obstacle:

- the `X_j` are pairwise disjoint, so the top blocks of two degrees share data
  only when their conductor intervals `[a(ell), ell]` overlap;
- above the support, conductor `j` contributes `<= (j-1)2^{j-1-n/2}` to `d_n`,
  which is `< 1/(4 ell)` -- i.e. the statement at `n` for that conductor is
  already a theorem (Hayes/Weil). **A block matters only at the `O(log j)`
  degrees where it is the frontier.**

So the averaging parameter available to a fixed block of `~j 2^{j-1}` Frobenius
angles has size `O(log j)`. That is not an inconvenience to be worked around;
Theorem 4 shows it is fatal.

## 4. Candidate 1: averaging over `ell` through the nesting `E_ell -> E_{ell-1}`

### 4.1 What the nesting does give

The nesting is genuine and is already used: `(BLOCK)` *is* the statement that the
`g_j` are shared across `ell`, and Theorem 1 is exactly the pay-off -- the
conductors below `a` are settled for every degree at once. What is not shared is
the frontier.

### 4.2 The null result

**Lemma 4.1.** Let `A` be a multiset of angles in `R/Z` with `D` distinct values,
multiplicities `m_1, ..., m_D`, `Sigma_1 = sum m_i`, `Sigma_2 = sum m_i^2`, and
minimal gap `delta`. Then `delta <= 1/D` and `Sigma_2 >= Sigma_1^2 / D`, hence
for every `T >= 1`

```text
(T + delta^{-1}) Sigma_2  >=  (T + D) Sigma_1^2 / D  =  Sigma_1^2 (1 + T/D)  >=  Sigma_1^2.
```

*Proof.* `D` points on a circle of circumference `1` have a gap `<= 1/D`;
Cauchy--Schwarz gives `Sigma_1^2 <= D Sigma_2`. QED

**Theorem 4 (large-sieve null result).** Let `S` be any set of `T` consecutive
degrees and `lambda > 0`. The Montgomery--Vaughan large sieve gives

```text
#{ n in S : |g_j(n)| > lambda }  <=  (T + delta_j^{-1}) Sigma_2(j) / lambda^2,
```

and by Lemma 4.1 the right-hand side is `>= Sigma_1(j)^2 / lambda^2`. Since
`|g_j(n)| <= Sigma_1(j)` holds trivially for every `n`, the bound is `< 1` --
i.e. says anything at a *prescribed* degree -- only when `lambda >= Sigma_1(j)`,
where the trivial bound already gives it. At the Kaser--Lemire threshold
(`lambda = tau_top 2^{n/2}` with `tau_top = 0.17`, half of Theorem 2's `tau` at
the top conductor `j = ell`, `n = 2ell+1`),

```text
Sigma_1 / lambda = (ell-1) 2^{ell-1} / (0.17 * 2^{ell+1/2}) = 2.079 (ell-1),
exceptional count  >=  4.32 (ell-1)^2.
```

Against Theorem 3's `T <= 2 ceil(log2 ell) + 4` degrees this is vacuous by a
factor `4.32(ell-1)^2 / (2 ceil(log2 ell) + 4)`: **`8565` at `ell = 200`**,
`1.9e5` at `ell = 1024`, `2.6e6` at `ell = 4096`. Verified for
`4 <= ell <= 400` and at `ell in {1024, 4096}` (CHECK E), together with the two
inequalities of Lemma 4.1 on the *measured* angle multisets for `3 <= j <= 11`.

Three consequences worth separating.

- **It is not a matter of the range.** `T` appears only in `(T + delta^{-1})`,
  and `delta^{-1} >= D`; enlarging `S` past `D ~ j 2^{j-1}` degrees changes the
  arithmetic but not the conclusion, because the degrees that need the estimate
  are the `O(log j)` smallest ones in the support. Lengthening the range moves
  the average away from the point one needs.
- **`delta` is not merely small; the separated form does not apply.** The angle
  multiset has *exact* coincidences. Measured (CHECK G, exact integer comparison
  of `L`-polynomial coefficient vectors in `Z[zeta_{2^E}]`): at `j = 9, 10, 11`
  the `2^{j-1}` characters of exact conductor `j` realize only `252, 488, 994`
  distinct `L`-polynomials, and the angle multiset has maximal multiplicity
  `33, 50, 130` with `Sigma_2/Sigma_1 = 3.04, 2.29, 6.02`. (Structural reason:
  the order-`4` layer is supersingular -- note 03 section 2, the Kerdock/`Z_4`
  row -- so its inverse roots pile up on a handful of angles.) Merging equal
  angles is therefore compulsory, and it inflates `Sigma_2`, which is the term
  Lemma 4.1 bounds from below.
- **The empirical side agrees.** Across `2 <= ell <= 24` the normalized
  deviations at consecutive `ell` are uncorrelated: Pearson `r = -0.066` (odd
  degrees, 22 pairs) and `-0.056` (even, 22 pairs). There is no cross-`ell`
  cancellation to find.

### 4.3 The exact reduction: what would have to be bounded instead

Theorem 4 kills only the *inequality*, not the *quantity*. Exactly,

```text
sum_{n=n_0}^{n_0+T-1} |g_j(n)|^2  =  T Sigma_2(j)
   +  sum_{theta != theta'} m_theta m_theta' e(n_0(theta-theta'))
         (e(T(theta-theta')) - 1)/(e(theta-theta') - 1).
```

The diagonal is harmless where it has been measured: `Sigma_2 = 61656` at
`j = 11` against the required `lambda^2 = 2.4e5`, and `Sigma_2/Sigma_1` runs
`1.18--6.01` over `4 <= j <= 11`, so `Sigma_2` is within a small factor of
`(j-1)2^{j-1} = o(2^{2j})`. (`Sigma_2 <= Sigma_1 max_i m_i` is all that is
proved; the growth of `max_i m_i` is itself unstudied at fixed `q`.) The whole
content is the off-diagonal at `T = O(log j)`, i.e. **a pair-correlation
estimate for the Frobenius angles of one conductor at fixed `q = 2`.** That is
precisely the input note 00 names as the wall and note 07 measures as
"pseudorandom, with no uniform bound available". So candidate 1 does not fail
for a new reason; it fails at the same place, and this is the exact reduction:

```text
AAD by a second moment over degrees   <=>   fixed-q pair correlation for A_ell at range T = O(log ell).
```

The one thing gained is a sharper diagnosis than "the family is bigger than the
range": the large sieve *cannot* be the tool, because its own error term already
contains the trivial bound (Lemma 4.1). A different tool would have to evaluate
the off-diagonal, not bound it.

## 5. Candidate 2: the moving exceptional set

Note 05 gives, for each `n`, an exceptional set `X_n subset E_ell` of size
`< 4 ell^2` out of `2^ell`, with the identity class `1` fixed. The idea: if
`X_n` moves "randomly" as `n` varies then `1 in X_n` for a summable fraction of
`n`, and AAD -- indeed all but finitely many `n` -- would follow. Two exact
obstructions and one measurement.

**Prop. 6 (the identity is a fixed point of the tower).** The groups `E_ell` for
different `ell` are compared only by the projections
`pi_{ell', ell} : E_{ell'} ->> E_ell` (`ell' > ell`), which are the unique maps
compatible with the arithmetic, i.e. with `<F>_ell = pi_{ell',ell}(<F>_{ell'})`
for every monic `F`. They are group homomorphisms, so `pi(1) = 1` at every
level. Hence, under the only canonical identification available, the target does
not move at all, and `X_{n}` moving inside `E_{ell(n)}` says nothing about its
position relative to `1`.

*Consequence.* "The exceptional sets are equidistributed" is not a statement one
can make without first putting a probability measure on the family `{X_n}`. The
only structure-preserving source of such a measure is a group acting on `E_ell`
and commuting with `N_ell`, and **Barrier II (note 06) caps the orbit of the
identity at `2`.** This is *not* the same statement as Barrier II -- Barrier II
is at fixed `n` and about moving `1` into the good set, while here we would be
moving `X_n` -- but it is the same input that is missing, and the conflation the
brief warns against is avoided precisely by Prop. 6: there is no motion of
`X_n` relative to `1` to speak of until one says what "relative to" means.

**Prop. 7 (the heuristic overshoots, which is the tell).** If `1` behaved like a
uniformly random class, `P(1 in X_n) <= 4 ell^2 2^{-ell}`, which is summable, so
the model predicts **finitely many** bad degrees, not `o(N)` of them. A
hypothesis that proves much more than the target, and whose only content is
"the identity is typical", is the delocalization statement of note 03 section 3
-- the wall again, not a route to it.

**The measurement, and what it is worth.** The two degrees `n = 2ell+1` and
`n = 2ell+2` share the group `E_ell`, and this is the one place where "the
exceptional set moves" is a well-posed question with data. Measured across the
23 groups `2 <= ell <= 24` (section 9.2), the normalized deviations are
**anti-correlated**: Pearson `r = -0.657`, Spearman `-0.617`, permutation
`p = 2.6e-4` (50000 shuffles), jackknife range `[-0.701, -0.541]`. We have no
mechanism for it and record it as an observation. Its *ceiling* is the point:
even a perfect anti-correlation would give only "at most one of the two degrees
of each group is bad", i.e. `#bad(N) <= N/2` -- a density statement, but density
`1/2`, not `o(1)`. Candidate 2's only measurable handle is off by an infinite
factor.

## 6. Candidate 3: slack `k`, and the exact ladder

Relax the window to `deg(f - x^n) <= floor(n/2) + k`, i.e. prescribe the top
`l = ell - k` coefficients. The sharp pointwise theorem is Hsu (1996) Thm 2.4 =
Cohen (2005) Thm 2.1 (in the form quoted by Gao, arXiv:2109.14154, Cor. 2):

```text
#{ irreducible of degree n, top l coefficients prescribed }  >=  2^{n-l}/n - (l+1) 2^{n/2}/n,
positive  <=>  2^{2(n-l)} > (l+1)^2 2^n.
```

Let `k*(n)` be the least `k` making this positive at `l = ell - k`, and
`kLS(n)` the least `k` at which Theorem 4's exceptional floor drops below `1`,
i.e. at which the large sieve over degrees is not vacuous
(`Sigma_1(ell-k) <= tau_top 2^{n/2}`).

**Theorem 8 (the slack ladder).** For every `n` in the computed range
(`32 <= n <= 400`, all `n = 2^m` up to `2^20`, and `n in {3000, 10^5, 10^6}`),

```text
0  <=  kLS(n) - k*(n)  <=  2.
```

Averaging over degrees therefore **never lowers the provable slack**, and in
fact costs one or two coefficients (the loss is the constant `tau_top`, worth
`log2(1/tau_top) = 2.56` in `k`). Verified in CHECK F, pinned against the
literature check in the diary (`n = 64`: `l_max = 27` against `ell = 31`, so
`k* = 4`).

```text
        n      ell     k*   kLS    l_max = ell - k*
       64       31      4     6              27
      256      127      6     8             121
     1024      511      8    10             503
     4096     2047     10    12            2037
    65536    32767     14    16           32753
  1000000   499999     18    20          499981
```

So the answer to "the smallest `k` for which an almost-all-`n` statement is
provable" is: **`k*(n) ~ log_2 n - 1`, the same as the pointwise threshold.**
Neither `k = O(1)` nor `k = c log_2 n` with `c < 1` is reachable, because
Theorem 4 applies verbatim with `ell` replaced by `ell - k` and `lambda` by
`2^k lambda`: the floor becomes `4.32((ell-k-1)/2^k)^2`, which drops below `1`
only when `2^k > 2.08(ell-k-1)`, i.e. exactly at `k ~ log_2 ell + 1`.

Independent concordance: the `k`-slack dictionary is note 18's, and diary entry
8 reports the smallest proved slack as `8` at `(ell, n) = (200, 401)` and `7` at
`(200, 402)`. The `k*` computed here from the Hsu/Cohen inequality agrees
exactly on both, by a different route and in a different script.

## 7. Candidate 4: sieve and large sieve over degrees, and the literature at `q = 2`

- **Selberg's almost-all short intervals is the wrong "almost all".** Under RH,
  almost all `x` have a prime in `[x, x + (log x)^{2+eps}]`; the average is over
  `X` centres. Its function-field analogue at the square-root scale is note 05,
  which is *unconditional* here because Weil replaces GRH, and which is
  almost-all over the `2^ell` centres at a fixed degree. **AAD is a different
  average**: over `n <= N`, i.e. over `log_2 X` values of the size `X = 2^n`,
  with the centre pinned at `x^n`. The integer statement it corresponds to is
  "for almost all `k`, `[2^k, 2^k + 2^{k/2+1}]` contains a prime" -- not known,
  and not implied by RH, for exactly the reason of Theorem 3: a geometric
  sequence of centres offers `log X` data points.
- **Unconditional short-interval technology does not reach `q = 2`.** Sawin,
  *Square-root cancellation for sums of factorization functions over short
  intervals in function fields*, arXiv:1809.05137 (Duke 2021), states in its own
  abstract that it obtains near-square-root cancellation "as long as the
  characteristic of the finite field is relatively large"; `p = 2` is outside
  its hypothesis, and its Betti-type constants are exponential in `n` (note 01
  section 4). Sawin--Shusterman (Annals 2022) needs odd `p` and
  `q > 685090 p^2`. Note 16 refuted, from primary sources, the transplant of the
  Bagshaw/Sawin--Shusterman line to `p = 2`: the indispensable Mobius input
  assumes odd characteristic (it is quadratic reciprocity), and the threshold
  `q > 7100.88 p^2` admits no prime field and no `q = p^2` at all. Carmon--
  Rudnick's Chowla-type theorem over `F_q[t]` likewise carries a standing odd-`q`
  hypothesis (recorded from the lane's literature sweeps; not re-read here).
- **And it is moot for this route.** Even granted a fixed-`q = 2` short-interval
  theorem for almost all `n`, it would have to supply the missing factor
  `~ell/2` at each frontier block; Theorem 4 says no averaging over degrees can
  supply it, so such a theorem would have to be pointwise in `n` -- i.e. it
  would be `(HWO)` or stronger, and AAD would be a corollary of the conjecture
  rather than a step towards it.

## 8. Candidate 5: a soft counting or pigeonhole route

**Prop. 9 (Type-I data does not see the degree).** By note 13 Lemma 1,
`A_d(n) = #{F in W_n : d | F} = 2^{h-k}` *exactly*, with no remainder, for every
monic `d` of degree `k <= h`; and by note 13 Cor. 4 the same holds for the
interval around *any* monic centre of degree `n`. Hence the vector
`(A_d)_{deg d <= h}` is a function of the window length `h` alone. Consequently:

1. any lower bound for `I_n` extracted from Type-I data is a function `psi(h)`,
   and since `h(2m) = h(2m+1) = m+1` it cannot even distinguish the two degrees
   of one level, let alone a density-one subset of degrees;
2. it is centre-blind, so it applies verbatim to every window of length `2^h`;
3. and note 13 Theorem 10 exhibits, for `10 <= n <= 15`, an explicit nonnegative
   rational weight with exactly this Type-I data and no primes, so `psi(h) <= 0`
   at every length computed.

**A soft counting argument therefore cannot produce a density statement**: there
is no quantity in the Type-I data whose positivity could hold for almost all
degrees and fail for the rest. This is the honest sense in which AAD is *not*
weaker than the conjecture for this class of methods.

**Constructions.** Note 08 Theorem A transports the conjecture from a seed
degree `m` to `mt` for admissible `t`; for a fixed finite ledger this reaches
`O((log N)^W)` degrees (`W = 16` here), density zero (Barrier III), never a
prime, never a power of two. Degree-multiplicative maps cannot raise density
without an input at positive density, which is the target itself.

**Prop. 10 (the Q-transform is window-hostile).** The one classical
irreducibility-preserving substitution not covered by note 08 is
`F(x) = x^m f(x + x^{-1})`, of degree `2m`. Then
`F = (x^2+1)^m + x^m (f - x^m)(x + x^{-1})`. Now
`deg((x^2+1)^m - x^{2m}) = 2m - 2^{v_2(m)+1}`, which is `<= m` **only when `m` is
a power of two** (checked for all `m <= 4096` in CHECK J); and for such `m`,
`(x^2+1)^m = x^{2m}+1` and `deg(F - x^{2m}) = m + deg(f - x^m) > m` unless
`f = x^m + 1`, which is never irreducible. So no seed passes through the
Q-transform into the window, and Barrier III's reach is not enlarged by it.

## 9. Measurements

### 9.1 Two producers, one anchor

CHECK A: an independent Python engine (Hayes group structure `E_j = prod_{k odd}
<1+x^k>` with `e_k = floor(log2(j/k))+1`, exact discrete log, `L(u,chi) =
sum_{m<j} c_m u^m` with `c_m = sum_{v in V_m} chi(v)`, `S_n = the u^n coefficient of u L'/L`)
reproduces the branch CAS `axeyum-gf2-hayes-endpoints` discrepancies `D_n`
**exactly** at all 18 endpoints `2 <= ell <= 10`, both degrees, with worst RH
deviation `9.05e-09`. CHECK H additionally cross-checks the CAS's
`hayes-endpoints` output against `data/cylinder-variances-ell12-24.txt` (a
different binary and a different computation) at the 13 shared endpoints: exact
agreement.

### 9.2 How far the identity class is from the mean, as a function of `ell`

`data/aad-endpoint-deviations.txt`; 46 endpoints, every `ell` in
`2 <= ell <= 24`, both degrees. `sd` is the Sato--Tate/Keating--Rudnick per-class
standard deviation `sqrt(2^{n-ell}(ell-2) + 2^{n-2ell+1})`, whose ratio to the
exact second moment note 05 section 4 measures at `1.00` for `ell >= 16`.

```text
 ell   n        D_n        2^{n-ell}       d_n      Weil        sd       z
  12  25        359             8192  +4.38e-02    7.071     286.2   +1.254
  16  33       2744           131072  +2.09e-02    9.900    1354.6   +2.026
  20  41       3115          2097152  +1.49e-03   12.728    6144.0   +0.507
  21  43     -20938          4194304  -4.99e-03   13.435    8927.0   -2.345
  22  45      -7582          8388608  -9.04e-04   14.142   12952.7   -0.585
  23  47      57574         16777216  +3.43e-03   14.849   18770.2   +3.067
  23  48     -88336         33554432  -2.63e-03   10.500   26545.1   -3.328
  24  49       1651         33554432  +4.92e-05   15.556   27169.8   +0.061
  24  50       4787         67108864  +7.13e-05   11.000   38423.9   +0.125
```

- `|d_n|` falls like `2^{-ell/2}`: from `4.4e-2` at `ell = 12` to `4.9e-5` at
  `ell = 24`. The Weil allowance for `|d_n|` is `7.07` and `15.56` at those two
  rows: **the truth is `1.6e2` and `3.2e5` times better than Weil**, and the
  needed threshold `0.34` is between them by a factor `~2 ell`.
- `z = D_n/sd`: rms `1.400`, `max|z| = 3.328` over 46 endpoints; the identity
  class deviates like an `O(1)`-sigma class, with no drift in `ell`. This is the
  data behind Prop. 7: the identity is empirically typical, and typicality is
  exactly what cannot be proved.
- Correlation across consecutive `ell`: `r = -0.066` (odd, 22 pairs),
  `-0.056` (even, 22 pairs). **No cross-`ell` structure** -- candidate 1 has
  nothing to average even heuristically.
- Correlation between the two degrees of the same `ell`: `r = -0.657`
  (Spearman `-0.617`, permutation `p = 2.6e-4`, jackknife `[-0.701, -0.541]`).
  Recorded as an observation; see section 5 for its ceiling.

### 9.3 The margin: minimal subdegree against `floor(n/2)`

`data/aad-min-subdegree.txt` (the search) and `data/aad-margin.txt` (the
margin). Independent engine: python-flint Rabin test, candidates enumerated by
*increasing* subdegree, so the value is the exact minimum; the checker
re-derives 59 of them from scratch and asserts every row against the window.

```text
      n   s_min   floor(n/2)   margin   s_min / log2 n
      8       4            4        0            1.333
     32       7           16        9            1.400
    100       6           50       44            0.903
    400       5          200      195            0.578
    800       9          400      391            0.933
   1300      11          650      639            1.063
   1900       6          950      944            0.551
   2000      13         1000      987            1.185
   3000      11         1500     1489            0.952
```

- `s_min(n) <= 10` for every `n <= 410` -- an independent reproduction of
  Arndt's `lowbit-irredpoly.txt`, which the conjecture's authors used for
  `n <= 400` -- and `s_min(n) <= 13` over the whole sampled range to `n = 3000`
  (the single value `13` is at `n = 2000`; every other sampled `n > 410` has
  `s_min <= 11`).
- `s_min(n)/log_2 n` in `[0.102, 1.400]`, mean `0.857`: the truth tracks
  `log_2 n`, as Elkies and Zaimi predicted on MathOverflow in 2011, not
  `n/2`.
- **The window bound is attained with equality only at `n = 2, 3, 5, 8`**
  (`s_min = 1, 1, 2, 4 = floor(n/2)`), and at no other degree in the range.
  Asserted as an exact equality of sets by the checker, so a new tight degree
  would fail the gate.
- The gap between the truth (`~log_2 n`) and the conjecture (`n/2`) is
  `n/2 - O(log n)`, while the gap between the conjecture and the best provable
  statement is `k*(n) ~ log_2 n - 1` coefficients (section 6). The problem is
  hard not because the assertion is delicate but because it sits `log_2 n` past
  the square-root barrier, which is exactly where every method stops.

### 9.4 One conductor, three numbers

At `j = ell = 11`, `n = 23` (CHECK G / CHECK E):

```text
Weil (trivial) bound   Sigma_1        = 10240
required by Theorem 2  tau_top 2^{n/2} =   492
rms over degrees       sqrt(Sigma_2)   =   248
truth                  |g_11(23)|      =    65
```

The ordering `truth < rms < required << Weil` is the whole problem in four
numbers: the truth beats even the diagonal, the requirement is a factor
`2.08(ell-1) = 20.8` inside Weil, and Lemma 4.1 says the large sieve's own error
term is never smaller than `Sigma_1^2`.

## 10. The ladder of what is proved about degrees

```text
rung                              degrees covered                     status
--------------------------------  ----------------------------------  ------------------
finite handoff (note 00)          all n <= 3000                       PROVED (certified,
                                                                      two checkers + flint)
composition families (note 08)    {mt : m certified in-window seed,    PROVED; density 0
                                   rad(t) | ord, gcd(t,(2^m-1)/e)=1}   (O((log N)^16));
                                                                      never a prime n,
                                                                      never a power of 2
Hayes/Weil with slack (sec. 6)    ALL n, window floor(n/2) + k*(n),    PROVED; k* ~ log_2 n - 1
                                   k*(64)=4, k*(1024)=8, k*(10^6)=18
this note                         nothing new about degrees           the reduction
                                                                      (Thm 2) and the
                                                                      null result (Thm 4)
--------------------------------  ----------------------------------  ------------------
AAD (the target)                  density-one set of n                OPEN; no averaging
                                                                      over degrees can
                                                                      reach it (Thm 4)
Kaser--Lemire                     every n                             OPEN; needs (HWO)
```

The gap, stated once: between rung 3 (all `n`, with `log_2 n` coefficients of
slack) and AAD (almost all `n`, with none) there is a factor `~ell/2` of
cancellation to be found at each frontier block, and Theorem 4 shows the only
generic tool for "almost all" -- a second moment over the averaging parameter --
cannot find it, because the averaging parameter has size `O(log n)` and the
block has `~n 2^{n/2}` angles. Between AAD and the conjecture there is
everything: AAD settles no prime degree and no power of two, the two families
where Barrier III already leaves nothing.

## 11. What this note does not do

- It does not prove AAD, and it does not prove AAD is impossible. Theorem 4 is a
  null result about the Montgomery--Vaughan large sieve and about second moments
  over degrees, not an independence statement. Section 4.3 names the input that
  would suffice.
- It does not re-read the primary sources for Carmon--Rudnick or Sawin's Duke
  paper beyond the latter's abstract; notes 15 and 16 own that ledger, and note
  16's corrections take precedence.
- The minimal-subdegree table is a search, not an exhaustive proof of
  minimality beyond the degrees where the search terminated; its assertions are
  upper bounds on `s_min(n)` and exact minimality only for the prefix the script
  re-derives.
- The endpoint table stops at `ell = 24` (`n = 50`), the reach of the branch
  CAS; `axeyum-gf2-hayes-endpoints 23` took 53 minutes on a contended host and
  each further `ell` roughly doubles that. The correlation statistics rest on 23
  groups, which is why section 5 reports a permutation test rather than an
  asymptotic p-value.

## Addendum (coordinator, 2026-08-23): two readings corrected by note 21

[Note 21](21-probabilistic-face.md) revisits two numbers in sec. C above and
reverses their interpretation. Both corrections are against this note, not
against its theorems, which stand.

1. **`rms z = 1.400` is a signal, not agreement.** This note read it as "the
   identity behaves like an `O(1)`-sigma class, no drift". A typical class has
   `rms z = 1` by construction, so `1.400^2 = 1.96` says the identity carries
   twice the typical variance. Note 21 measures the identity's rank among all
   `2^ell` classes directly (rank 1 = most extreme): quantile mean `0.311`
   against the uniform `0.500`, `3.08` sigma, and the identity is in the top
   `5%` of classes at 6 of 22 endpoints against `1.10` expected
   (Poisson `p = 9.7e-4`). **The identity is NOT a typical class.** Prop. 7's
   heuristic conclusion survives, but on a smaller margin and with the
   "typical class" hypothesis replaced by an atom-corrected one.
2. **The anti-correlation is explained.** Note 21 finds the mechanism: exact
   eighth-root repeats in the angle multiset, weighted by `m^2` and not by `m`
   -- which is precisely why this note's `g_j(1)` test came out two orders too
   small. Predicted vs measured lag-1 agree to about 1% over `ell = 8..13`,
   and there is a `mod 8` sign law `sign z_n = -sign P_ell(n mod 8)` holding at
   42 of 45 endpoints (`p = 4.3e-10`). This note's `-0.657` over 23 groups and
   the asymptotic `~ -0.45` are the same number (Fisher-`z` distance
   `1.41` sigma). The density-`1/2` ceiling stated here is unchanged.

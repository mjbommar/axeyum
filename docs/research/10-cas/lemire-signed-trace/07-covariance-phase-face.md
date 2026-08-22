# The cylinder covariance: the phase-aware face of (REL), measured

Status: research note, 2026-08-22. Exact measurements and one new exact
structural fact (the carry-formula collapse boundary); the verdict on
reachability is honest and negative. This is the third of the three
post-barrier approaches (almost-all theorem note 05, symmetry barrier
note 06, this). It isolates the single unblocked analytic target -- input (3)
of note 05, a phase-aware correlation -- in its weakest known form and shows
what it would take.

Companion: [03-uncertainty-analogy.md](03-uncertainty-analogy.md) section 5
(the barrier the target must clear), [02-mechanism-hunt.md](02-mechanism-hunt.md)
section 1.1 (the twisted cylinder sums measured here).

## Exact decomposition

For nontrivial `psi in K^dual` (`K = ker(E_ell -> E_{a-1})`, elementary
abelian), the identity-cylinder twisted sum
`A_psi = sum_{g in K} N(g) psi(g) = 2^{-(a-1)} sum_{chi in coset(psi)}
S_n(chi)`, the coset being the conductor-`cond(psi)` characters
`{chi_psi chi_0 : cond(chi_0) < a}`. At the `|A_psi|^2` scale,
`|A_psi|^2 = D_psi + C_psi` with diagonal
`D_psi = mean_h |A_psi^{(h)}|^2` and covariance
`C_psi = |A_psi^{(1)}|^2 - D_psi`; the exact ratio is
`C_psi/D_psi = |A_psi^{(1)}|^2 / mean_h |A_psi^{(h)}|^2 - 1`, how loud the
identity cylinder is against the cylinder-average. `(REL)` at cylinder level
is `|A_psi^{(1)}| < 2^{ell-1}` for every `psi != 1`. Parseval
`sum_psi |A[0,psi]|^2 = |K| sum_{g in K} N(g)^2` verified exactly on every
dump.

## The covariance is at the random scale in aggregate, bulk-negative per psi

```text
ell  n   mean C/D  median C/D   max C/D  frac(C/D<0) | aggregate C/D
12  25    -0.092    -0.431      +3.03    0.587       |  -0.066
16  33    +0.261    -0.338      +7.36    0.587       |  +0.234
20  41    +0.088    -0.548     +10.17    0.740       |  +0.088
22  45    +0.037    -0.607      +6.62    0.677       |  +0.029
24  49    -0.077    -0.480      +4.23    0.693       |  -0.076
```

Three facts. (i) Aggregate `C/D ~ 0` (`|.| <= 0.23`, oscillating sign): summed
over the coset, `|sum_chi S_n|^2 ~ sum_chi |S_n|^2`, the random-phase value --
the off-diagonal contributes nothing on average. (ii) The distribution is
skewed strongly negative: median `C/D ~ -0.55`, 59--74% negative, floor
exactly `-1` (attained when `A_psi^{(1)} = 0`); the typical identity cylinder
is about half as loud as its diagonal. (iii) A thin positive tail carries the
mean: `max C/D` grows `+3 -> +11` with `ell`, ~17% of `psi` have `C/D > +1`.
So **`|C| <= (1-eps) D` uniformly over `psi` is FALSE** -- the tail is
unbounded above; the negativity is distributional, not a per-`psi` law. The
identity-cylinder maxima of note 02 (`0.09..0.46` of threshold, halving every
two `ell`) are this quiet bulk realized.

## The population pair-correlation is pseudorandom

`R(t) = sum_g N(g) N(g+t)` (K-shifts `t`) is the Walsh dual of the diagonal.
The connected covariance, relative to the random value `2^{2(n-ell)}`:

```text
ell  n    mean         rms          max
12  25   -1.1e-5      3.2e-5       9.7e-5
16  33   -6.9e-7      1.4e-6       8.3e-6
20  41   -2.7e-8      5.5e-8       5.0e-7
24  49   -1.7e-9      3.4e-9       3.0e-8
```

rms shrinks `~2^{-1.1 ell}`, the mean is systematically negative (a sum-rule
from `sum N = 2^n`) but doubly tiny; no shift is exceptional. The covariance
`C = sum_{F1,F2} Lambda(F1)Lambda(F2)[psi]` reduces to these `R(t)`, and they
are pseudorandom.

## The carry formula collapses to Weil above the Kerdock level (new exact fact)

Testing the shape-A carry law `T_s(a+b) = T_s(a) + T_s(b) - 2T_{s-1}(ab) -
4T_{s-2}(...) - ...` as an inner sum: the derivative
`D_s(c) = sum_alpha zeta_{2^s}^{T_s(alpha) - T_s(alpha+c)}` factors through
the `-2T_{s-1}(ab)` term into an order-`(s-1)` Galois-ring Gauss sum. Measured
(`n = 13, 15`, `|.|/2^{n/2}`):

```text
s=1: inner |D(c)| = 2^n           (trivial derivative)
s=2: inner |D(c)| = 0 EXACTLY, all c   <- Kerdock: sum_alpha (-1)^{Tr(alpha c)} = 0
s=3: inner |D(c)| ~ 0.75 * 2^{n/2}     (full Weil magnitude)
s=4: inner |D(c)| ~ 0.8-0.95 * 2^{n/2}
```

So the `-2T_{s-1}(ab)` term delivers a small inner sum **only at `s-1 = 1`**
(`s = 2`, Kerdock, where the inner is an ordinary additive character sum,
identically `0`). For `s >= 3` the inner sum is an order-`>=2` Galois-ring
Gauss sum of full Weil magnitude, so Cauchy--Schwarz returns `|G_s| ~ 2^{n/2}`,
exactly Weil, no saving. This is an exact, sharply located proof that the
carry formula cannot give a constant-factor bound `|C| <= (1-eps) D` beyond
the quadratic (Kerdock) level -- the boundary is pinned at `s-1 = 1`,
confirming note 02's "Parseval over cosets returns Weil".

## What this reframing buys, and the honest verdict

The cylinder covariance is a much weaker sufficient statement than the
layer-level `(HWO)`. `D_psi ~ ell 2^{n-a+1}` and `threshold^2 = 2^{2ell-2}`
give `D_psi/threshold^2 ~ 32 ell^2 2^{-ell}`, so a violation would need
`C_psi/D_psi > 2^ell/(32 ell^2)` -- the identity cylinder louder than random
by `2^{ell/2}/ell`, against a measured `max C/D ~ +11`. The cylinder form
carries doubly-exponential margin; `(HWO)`'s `4 ell` log-over-Weil saving is
an artifact of the exact-order decomposition. The minimal statement is the
ledger fact `F:gf2-lemire-cylinder-twist-sup-bound`: no `psi != 1` makes the
identity cylinder anomalously loud.

Reachability: **not now.** The required input is a first-moment /
pair-correlation delocalization for a fixed-conductor character family at
fixed `q = 2`. Its integer analogue is conditional (GRH + a pair-correlation
hypothesis, Kandhil--Languasco--Moree arXiv:2607.14515, verified from source);
its function-field analogues (Keating--Rudnick, Hall--Keating--Roditty-Gershon,
Sawin, Hochfilzer arXiv:2102.06415, Roditty-Gershon arXiv:1811.04834) are all
`q -> infinity` matrix-integral limits; and the one exact fixed-`q` mechanism,
the Witt carry, collapses to Weil above the Kerdock level (proved above). The
margin is enormous and the phenomenology benign (mean covariance ~ 0, pair
correlation random), but the negative skew of the identity cylinder's
covariance is exactly the phase-aware fact -- true *because* `N` is a
`Lambda`-weighted prime count -- that no current fixed-`q` theorem provides.

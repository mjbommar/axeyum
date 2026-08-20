# ADR-0564: Measure, but do not credit, Efron--Stein hypercontractivity

Status: accepted
Date: 2026-08-20
Index-summary: Retain exact Efron--Stein spectral masses as a diagnostic, but reject the proposed constant-three product-hypercontractive bridge as neither supplied by the cited theorem nor numerically sufficient

## Context

After replacing the overstrong connected fourth-moment target by the weak
proper-power-aware threshold in ADR-0563, a review suggested decomposing the
Hayes discrepancy over the stable cyclic factors

```text
E_ell = product_i Z/(2^k_i),             sum_i k_i=ell,
```

and assigning a character the weight
`w(chi)=sum_(i in supp chi) k_i`.  If `f_w` denotes the fraction of spectral
second-moment mass at weight `w`, the proposed conditional estimate was

```text
R_0 <= (sum_w C^(w/4) sqrt(f_w))^4.       (H)
```

A character-count model, rather than the actual spectral mass, suggested
that a constant near the sharp two-point value `C=3` might suffice.  The
review cited Keevash--Lifshitz--Long--Minzer (KLLM), *Hypercontractivity for
global functions and sharp thresholds*, JAMS 37 (2024),
<https://arxiv.org/abs/1906.05568>, while explicitly noting that its theorem
statement had not been checked.

## Decision

Expose an exact bounded diagnostic that computes the Efron--Stein support
mass without roots of unity:

1. aggregate discrepancies over every coordinate projection;
2. apply subgroup Parseval to obtain the mass supported in each subset;
3. apply Boolean-lattice Moebius inversion to obtain exact-support masses;
4. group those exact integers by `sum k_i`.

The optional floating-point evaluation of `(H)` is named
`conditional_hypercontractive_root_ratio_proxy`.  It is not a certified
bound and has no theorem-crediting path.

Do not cite KLLM as proving `(H)`.  The primary LaTeX source states a
different result.  For a general discrete product space its Theorem
`thm:es` bounds the `q`-norm of the noised function `T_rho f`, with

```text
rho <= 1/(8 q^(3/2)),
```

by generalized Laplacian norms weighted by minimum atom probabilities.  Its
grading is the number of active coordinates, not `sum k_i`; at `q=4` it
controls `T_(1/64) f`, not the unnoised discrepancy.  Undoing that noise on
a high-support component introduces a factor exponential in its coordinate
support.  The paper therefore supplies neither the proposed `C=3` constant
nor `(H)` for the cyclic Hayes product.

## Evidence

The exact masses reconstruct full Parseval in a pinned unit test.  Both
endpoint offsets were then measured on independent fleet hosts.  Even the
more favorable hypothetical value `C=2` misses the corrected weak allowance
by a rapidly growing finite factor:

```text
ell  n       proxy C=2       allowed R_0       proxy/allowed
15   31      241558.214       4.482209          53892
15   32      242761.975       0.656887         369562
16   33      481584.335       6.686467          72024
16   34      479204.794       0.962520         497865
17   35      795433.340      10.174469          78179
17   36      799129.249       8.887318          89919
```

The values for `C=3` are larger by another two to three orders of magnitude.
These finite rows do not disprove every possible globalness argument.
They do refute the particular uniform-character-mass heuristic used to
motivate `(H)`, and the cited theorem does not repair the gap.

## Consequences

- Exact Efron--Stein masses remain useful for testing future, explicitly
  stated inequalities.
- The proposed constant-three hypercontractive route receives no endpoint
  proof credit and is deprioritized.
- Further computation in this grading is unwarranted unless a new theorem
  predicts a quantitatively sufficient bound before absolute values are
  taken.
- The live analytic obligation remains the weak fourth-moment estimate of
  ADR-0563.  The constructive Capell/composition route is the next bounded
  positive attack.

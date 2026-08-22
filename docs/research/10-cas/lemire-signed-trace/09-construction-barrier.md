# The construction barrier: provable window families are lacunary

Status: research note, 2026-08-22. The barrier below is proved for the known
degree-multiplicative construction toolbox and stated with honest scope (it is
not a logical impossibility for all conceivable seed families). Concrete
claims machine-checked (flint). It is the third barrier -- moduli (note 03
section 5), symmetry (note 06), construction (here) -- and together the three
explain why the proven infinite family (note 08) is density zero and why the
all-`n` statement needs the analytic phase-aware estimate, not a bigger box of
constructions.

## Barrier III (degree lacunarity)

Every explicit algebraic construction in the known toolbox that provably
preserves irreducibility multiplies the degree; hence its degree-set is
lacunary (`O(log X)` terms below `X`), and a finite union of such families has
density zero and cannot fill a residue class `n = a mod M`.

**Mechanism.** A degree-`m` irreducible over `F_2` is the minimal polynomial
of a generator of `F_{2^m}/F_2`. A fixed algebraic recipe `rho` of degree `e`
applied to a root `alpha` of a degree-`n` irreducible produces `beta =
rho(alpha)` algebraic over `F_2(alpha) = F_{2^n}` of degree at most `e`, so
`F_2(beta) subset F_{2^{ne}}` and `[F_2(beta):F_2]` divides `ne`. The specific
known recipes realize this as an exact multiplication: composition `f(g(x))`
with `deg g = d` gives degree `nd`; the Meyn `R`-transform and `Q`-transform
give `2n`; Moebius maps give `n` (the degree-preserving `PGL_2(F_2)` of the
symmetry barrier); composed-products (Brawley--Carlitz) and isogeny/Carlitz
towers likewise multiply. So a *fixed* recipe on a *fixed* seed family advances
the degree only multiplicatively, and the degree-set `{n_0 c^k}` is lacunary.

**Density corollary (exact).** A lacunary set `{n_0 c^k}` has at most
`log_c X` elements below `X`; a finite union of `r` such families has at most
`r log_2 X`. Verified: the union `{2*3^k} u {4*2^k} u {6*2^k}` below `10^9` has
**74** elements (`log_2 10^9 ~ 30`), density `7.4e-8 -> 0`.

**Window destruction under composition (machine-checked lemma).** For `f`
irreducible of degree `n >= 3` and `g = x^d + r` a non-monomial (`d >= 2`,
`r != 0`), over `F_2` the composition `f(g(x))` has `tail >= d(n-1) > nd/2 =
deg/2`, so it leaves the window; the only survivor is the degree-2 seed
`x^2+x+1` (an affine-additive image, rarely irreducible). Checked:
`(x^2+x+1)(x^2+x) = x^4+x+1` is in-window and irreducible; `(x^3+x+1)(x^2+x)`
has tail `5 > 3` (out of window); `(x^4+x+1)(x^2+x) = ` degree 8, in-window but
reducible. The Meyn tower from `x^2+x+1` gives degrees `2,4,8,16,32` with tails
`1,3,7,15,31` -- leaves the window at the first step.

## Directions closed (exact scans)

- **Cyclotomic `Phi_m` irreducible and in-window:** scan of all odd `m <= 2000`
  with `2` a primitive root mod `m` -- only `m in {3,9,27,81,243,729}`, i.e.
  the proven family `n = 2*3^k`, nothing else. Forced: `(Z/m)^x` cyclic needs
  `m = p^a`; the second term of `Phi_{p^a}` sits at degree `(p-2)p^{a-1} <=
  phi/2` iff `p <= 3`, and `p = 2` is reducible.
- **Factors of `Phi_m`:** in-window irreducible factors are exactly the known
  low-weight witnesses (`x^3+x+1` from `m=7`, etc.); every irreducible divides
  some `Phi_{ord(root)}`, so this is tautological and `m` does not predict the
  window. For prime `n` the in-window trinomial's root is primitive (order
  `2^n-1`), a generic prime with no small-conductor structure.
- **Artin--Schreier `x^{2^s}+x+1`:** irreducible only for `s = 1,2`; general
  `x^n+x+1` irreducible for a sparse set whose infinitude is open.
- **Carlitz/Drinfeld cyclotomic:** the Euclid/Carlitz argument yields
  irreducibles of degree `~ 2^ell deg F`, overshooting (note 02 section 5C).
- **Composition with linearized `L`:** window survives only for the degree-2
  seed; degrees are `2 deg L`, lacunary.

## Literature ceiling (why no AP seed is within reach)

The window prescribes the top `ell = ceil(n/2)-1 ~ n/2` coefficients. The
strongest provable prescribed-coefficient theorem at fixed `q` (Pollack 2013,
FFA 22; Bourgain; Ha 2016 needs `q -> infinity` for `(1/4-eps)n`) prescribes
only `(1-eps) sqrt n` coefficients. Prescribing `~ n/2` high coefficients at
`q = 2` is beyond every known explicit method -- exactly the gap Barrier III
explains: constructions move between fields multiplicatively, so they cannot
manufacture a prime of a prescribed nearby degree; that is the counting
problem itself.

## Honest scope

Barrier III rules out the *known* provable toolbox (cyclotomic order,
Artin--Schreier trace, composition, Meyn/Kyuregyan/`R`/`Q`, composed-products,
isogeny towers, Carlitz--Euclid), all of which are degree-multiplicative. It is
**not** a logical impossibility theorem: a genuinely new *seed* family whose
degrees run in an arithmetic progression would evade it. No such seed is known,
and the `sqrt n` prescribed-coefficient ceiling shows none is within current
reach. So the honest statement is: no positive-density provable family exists
among reachable constructions, and crossing to positive density (let alone all
`n`) requires the analytic phase-aware estimate.

## The four sides, mapped

- **Averaging** -> the almost-all theorem (note 05): all but `< 4 ell^2 2^{-ell}`
  patterns realized.
- **Symmetry** -> barrier (note 06): no action moves the identity class
  (orbit `<= 2`).
- **Phase correlation** -> isolated (note 07): the one unblocked analytic
  target, not reachable at fixed `q`; the Witt carry collapses to Weil above
  Kerdock.
- **Construction** -> barrier (here): provable window families are lacunary;
  the proven family `n = 2*3^k` (note 08) is the best reachable.

Each side goes exactly as far as it can and stops at the same wall: a
phase-aware cancellation estimate for a complete character family at fixed
`q = 2` and growing conductor, whose integer analogue is conditional (GRH +
pair correlation) and whose function-field analogues are all `q -> infinity`.

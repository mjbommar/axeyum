# The symmetry barrier: no degree-preserving action moves the identity class

Status: research note, 2026-08-22. The statement below is proved (the
characterization is standard; the descent criterion and orbit sizes are
machine-checked). It is the second of the two barriers -- the first
(note 03 section 5) rules out moduli-only analytic inputs; this one rules out
symmetry inputs -- and together they say Lemire needs a class-specific lower
bound or a phase-aware correlation.

Companions: [03-uncertainty-analogy.md](03-uncertainty-analogy.md) section 5
(the moduli barrier), [05-almost-all-theorem.md](05-almost-all-theorem.md)
(the almost-all theorem and the three admissible input types).

## Descent criterion

A bijection `phi` of the degree-`n` monic irreducibles over `F_2` induces a
permutation `sigma` of `E_ell` with `N_ell(sigma g) = N_ell(g)` if and only if
`phi` maps every irreducible of one `E_ell`-class into a single `E_ell`-class
(the block condition). `E_ell = (1 + x F_2[x])/x^{ell+1}`, and `<F>_ell` reads
the top `ell` non-leading coefficients; the identity class `1` is the pattern
`h = 0`.

## Theorem (symmetry barrier)

Let `phi` be any degree-preserving substitution symmetry of the degree-`n`
irreducibles over `F_2`. Then `phi in PGL_2(F_2)` (degree preservation forces a
Moebius map `x -> (ax+b)/(cx+d)`; `F_2`-rationality forces `F_2` entries, so
`|PGL_2(F_2)| = 6`). `phi` induces a permutation of `E_ell` commuting with
`N_ell` if and only if `phi` fixes the place at infinity, i.e. `phi` lies in the
Borel subgroup `B(F_2) = {id, x -> x+1} = Z/2` (the stabilizer of the top-
coefficient truncation, Garefalakis--Kapetanakis). Adjoining the Galois/Adams
action `g -> g^a` (`a` odd, which fixes `1`) does not enlarge orbits. Hence the
orbit of the identity class under the full group of structural symmetries has
size at most `2 < 4 ell^2`; and the multiplication (Hecke) action of the ray
class group, though transitive on `E_ell`, shifts the degree by `deg L` and
fixes no degree-`n` fibre. Therefore no symmetry can place the identity class
in the non-exceptional set of note 05, and none can prove `N_ell(1) > 0`.

## What was tested (exact, `3 <= ell <= 8`)

- **PGL_2(F_2), all six elements.** Each preserves degree and irreducibility
  (checked to `#irr = 7710`). Only `{id, x->x+1}` descends; the four elements
  with `c != 0` (`1/x`, `(x+1)/x`, `1/(x+1)`, `x/(x+1)`) fail the block
  condition on all `2^ell` classes -- they read the low coefficients of `f`,
  which `<f>_ell` does not see. `PGL_2(F_{2^k})`, `k > 1`, does not act on
  `F_2`-rational polynomials; scalar `x -> cx` is trivial (`F_2^* = {1}`);
  Frobenius fixes minimal polynomials (identity on the set).
- **Power maps `alpha -> alpha^k`, `gcd(k, 2^n-1) = 1`, `k` not a power of 2**
  (the largest transitive group on the primes): genuine degree-`n`
  bijections, but none descends -- every class conflicts (`2^ell` conflicts)
  at `(4,9), (5,11), (6,13)` for all 12 exponents tested. The one large
  transitive group scrambles the `E_ell` fibration maximally.
- **Translation, corrected.** `sigma(1) = <(1+x)^n>_ell`, and
  `N_ell(1) = N_ell(sigma(1))` exactly (a bijection): `sigma(1) = 15, 51, 255,
  3` at `(5,11), (6,13), (7,15), (8,17)` (odd), `85, 1` at `(6,14), (7,16)`
  (even). So **translation does NOT fix the identity class in general** -- it
  fixes it iff `(1+x)^n = 1 mod x^{ell+1}`, i.e. `C(n,k)` even for all
  `1 <= k <= ell` (as at `n = 16`, `ell = 7`). This corrects the earlier
  notes' claim that translation fixes the identity. The orbit is still `{1,
  sigma(1)}` of size `<= 2` (an involution over `F_2`), so both members can
  lie in the exceptional set and the conclusion is unchanged.
- **Adams `g -> g^a`** preserving `N_ell` (4/8/16/16 good exponents at
  `(5,11)/(6,13)/(7,15)/(8,17)`) all fix `1`; `<translation, Adams>`-orbit of
  `1` has size `2` at every `(ell, n)`.
- **Hecke `g -> g <L>`** is transitive on `E_ell` (a single prime `L` of
  degree `d` gives orbit `8, 8, 4` for the `L` tried), but the lift
  `P -> P L` sends a degree-`n` prime to a degree-`(n+d)` reducible; measured
  `N_{n+d}(g<L>)/N_n(g) ~ 2^d` (mean `4.1` for `d=2`, `8.2` for `d=3`), no
  closed loop at fixed `n`, so positivity is not transported between classes
  at the degree Lemire needs.

## Consequence

Both barriers now stand: moduli-only inputs (note 03 section 5) and symmetry
inputs (here) each fail for the same structural reason -- the identity class
is genuinely distinguished (the short interval `{x^n + g : deg g <= floor(n/2)}`
= the all-odd-power-traces-vanish locus), and nothing permutation-like moves
it. Lemire must come from a class-specific lower bound (note 05 input 2) or a
phase-aware correlation among the `S_n(chi)` (input 3, the roadmap's open
estimate), not from averaging and not from a group action.

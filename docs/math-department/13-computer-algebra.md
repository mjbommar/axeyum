# 13 — The computer algebra system, as a tool

Reviewer: the twelve chairs, each asked one question — *would you use
`axeyum-cas` to compute in your field, and what stops you?*
Verdict, 2026-09-05: **a deep single-variable calculus and elementary
number theory tool that overflows at 128 bits; every other chair finds
nothing to reach for**
Last measured: 2026-09-05 at `8f6c58420`

> "You built the one CAS whose answers can carry a proof, and then you
> built the parts of Mathematica a first-year calculus course uses. Where is
> the rest?"

This file is different from files 01 to 12. Those ask what the *library*
proves. This one asks what the *CAS* computes, judged as a computing tool by
the same twelve practitioners. It exists because the CAS roadmap under
[`docs/research/10-cas/`](../research/10-cas/README.md) was written
2026-07-20 to 07-23, its capability-parity push paused at wave 24 on
2026-07-22, and every CAS commit since 2026-08-26 has been trust work — the
[`cas-internal` residue](../research/09-decisions/adr-1617-exact-real-cost-and-cas-internal-residue-measured.md)
and the bridges that reduce it. That work is tracked in
[11-applied-and-computational.md](11-applied-and-computational.md) items 3
and 5 and in the roadmap rows W1-13 and W2-16. **This file tracks the other
axis: what the tool can compute at all.**

## What the CAS has today

Measured 2026-09-05 at `8f6c58420`; the commands are in *How to re-measure*.

| metric | value |
|---|---|
| source lines, `crates/axeyum-cas/src` | 80,851 |
| modules | 55 files plus 4 subdirectories |
| `pub fn` declarations | 691 (385 at column 0) |
| `#[test]` functions | 1,006 |
| `lib.rs` alone | 29,505 lines |
| `cas-certificate` ledger facts | 61: 16 kernel-reconstructed, 45 `cas-internal` (73.8%) |
| core coefficient arithmetic | `i128` rationals; overflow reported as `ZeroTest::Unknown` (`lib.rs:46`) |
| numeric evaluation | `evalf(expr, bindings: &[(&str, f64)]) -> Option<f64>` (`lib.rs:9903`) |

The surface, by area, is in the
[capability table](../research/10-cas/README.md#implemented): differentiation,
canonical forms and a decidable zero-test with sound transcendental folds;
factorization over ℚ (Berlekamp–Zassenhaus) and 𝔽ₚ; partial fractions;
Horowitz–Ostrogradsky rational integration plus a large elementary and
special-function integration table; series, Laurent and residues; limits
including L'Hôpital, squeeze and exponential dominance; Gosper and
Zeilberger summation; linear constant-coefficient and first-order ODEs;
Laplace, Fourier series and z-transforms; exact ℚ linear algebra through
Jordan form, Smith and Hermite forms, QR and Cholesky; Sturm real-root
isolation and real algebraic numbers; Gröbner bases over ℚ with cofactor
certificates; an elementary number-theory bundle through discrete logs,
Pell and continued fractions; plane geometry with a Nullstellensatz
certifier; GF(2) polynomial and tensor machinery; SOS, Lyapunov and barrier
certificates; exact descriptive statistics; permutations; boolean algebra.

Of the July roadmap's prioritized top 15, fourteen have code behind them.
The unbuilt ones are Lazard–Rioboo–Trager and Risch (zero files mention
either), CAD, and Meijer-G.

## What each chair would say

One line each, every absence re-checked against the crate on 2026-09-05
with the probe in *How to re-measure*, and paired with a positive control
(`smith_normal_form`, `laplace_transform`, `gosper_sum`, `count_real_roots`
each found by the same query shape).

| # | chair | would they use it | what stops them |
|---|---|---|---|
| 01 | number theory | for elementary work, yes | no Gaussian integers, no quadratic or number fields, no ideal factorization, no two-squares or Cornacchia, no elliptic curves; `i128` overflows on any real computation |
| 02 | constructive analysis | no | series are compute-only with no remainder bound; `evalf` returns a double and no enclosure |
| 03 | classical analysis | for one-variable calculus, yes | no Fourier transform, no asymptotic expansion past a leading term, no change of variables in multiple integrals, no PDE methods |
| 04 | algebra | no | Gröbner over ℚ only; factorization univariate plus two bivariate special forms; no ℚ(α) arithmetic beyond one real root; no finite-group computation beyond a single permutation; no Galois groups |
| 05 | geometry | for the rational plane, yes | no conics, no 3D, no projective coordinates, no isometries as objects |
| 06 | topology | no | nothing, and nothing expected, except that Smith normal form exists and simplicial homology is one module away |
| 07 | combinatorics | for sequences and triangles, yes | no formal power series object, no generating-function algebra, no recurrence guessing, no graph algorithms, no posets or tableaux |
| 08 | probability | for descriptive statistics, yes | no named distributions, no moment generating functions, no convolution of independent variables, no estimators or tests |
| 09 | category theory | no | nothing to ask for, and they would say so |
| 10 | logic | no | a proof-carrying CAS with no real quantifier elimination; Sturm and polynomial inequality solving exist, so the univariate existential fragment is close |
| 11 | applied | for exact rational work, yes | arbitrary precision and validated numerics absent; no published parity benchmark against SymPy with a denominator |
| 12 | the chair | — | the capability table's *certified* column is prose; no gate counts which of the 691 public functions carry a certificate |

## The Next Ten, in priority order

Ranked by how many chairs an item serves, then by what it unblocks. Items 1
and 2 are prerequisites for most of the rest being usable at scale; item 10
is what makes any of it citable.

- [ ] **1. Arbitrary-precision core.** `CasExpr` coefficients are `i128` and
      overflow reports `Unknown`. Chairs 01, 02, 03, 07, 11 hit this wall
      within minutes of real use. `num-bigint` is already a dependency and is
      used in eight modules (`telescoping`, `ratint`, `real_algebraic`,
      `mvpoly/big`, `sos/*`, …), so this is a migration with a measured cost
      curve, not a design.
- [x] **2. Validated numerics.** *Landed 2026-09-05 (`enclosure.rs`); `gamma`, Bessel, `erf` and non-integer powers still decline.* Replace the `f64` `evalf` with rational
      interval enclosures to a requested precision, with interval Newton for
      root enclosures. `interval_arith.rs` exists and is not wired in. Serves
      02, 03, 11, and answers the computable-analysis seat's W1-12 complaint
      without running series inside the kernel.
- [~] **3. Formal power series and generating functions as an object.** *Object, composition, reversion, rational expansion and Berlekamp–Massey landed 2026-09-05 (`fps.rs`); coefficient asymptotics and radius of convergence still open.*
      Radius of convergence, composition, coefficient extraction, coefficient
      asymptotics, recurrence guessing from initial terms. The private
      `series.rs::Series` struct becomes public. Serves 07, 02, and the
      asymptotics 03 asked for.
- [ ] **4. Algebraic extensions and algebraic number theory.** Arithmetic in
      ℚ(α) over a minimal polynomial, then ℤ[i] and quadratic fields with
      ideal factorization, two squares, Pell as a unit computation.
      Multivariate factorization follows. Serves 01 and 04, and unblocks the
      July roadmap's own Lazard–Rioboo–Trager item.
- [~] **5. Finite group computation.** *Permutation groups by Schreier–Sims landed 2026-09-05 (`permgroup.rs`); Sylow, presentations and isomorphism testing open.* Permutation groups with Schreier–Sims,
      subgroups, cosets, orbits and stabilizers, Cayley tables from
      presentations. Serves 04, and gives 05 its transformation groups.
- [ ] **6. Geometry beyond the rational plane.** Conics as quadratic forms,
      3D points and planes, homogeneous coordinates, isometries as maps. The
      cofactor certifier in `geometry_certify.rs` extends to all of these, so
      the certified route comes free. Serves 05.
- [ ] **7. Real quantifier elimination.** The univariate existential fragment
      over Sturm and the existing inequality solver first, then
      low-dimensional CAD. The July roadmap deprioritized it for a weak
      certificate; sample-point certificates are checkable. Serves 10, 11, 03.
- [x] **8. Simplicial homology over ℤ.** *Landed 2026-09-05 (`homology.rs`), and it exposed a non-terminating Smith normal form.* Boundary matrices into the existing
      `smith_normal_form`. The cheapest new subject on this list and the only
      thing 06 would use.
- [~] **9. Symbolic probability.** *Eight distributions with route-named certificates landed 2026-09-05 (`probability.rs`); Poisson and Geometric moments and `Normal(0,1)` decline on measured machinery gaps.* Named distributions with exact mean,
      variance and moment generating function through the existing
      `laplace_transform`; convolution of independent sums; the moment
      inequalities in symbolic form. Serves 08.
- [~] **10. A gated trust registry and a parity benchmark.** *Registry landed 2026-09-05 (`check-cas-trust-registry.py`, 41 of 730 public functions certified); the SymPy parity corpus is still open.* A script that
      derives, per public function, whether its result carries a certificate,
      ratcheted like `check-cas-internal-residue.py`. Beside it, a SymPy
      parity corpus with ground truth independent of this repository, in the
      style of
      [`docs/plan/cas-smt-capability-2026-08-12/`](../plan/cas-smt-capability-2026-08-12/README.md).
      Serves 12 and 11.

**What is deliberately not on this list.** Kernel bridges for the existing
certificates (the `cas-internal` residue, W1-13 and W2-16) — those are the
*trust* axis and are tracked in file 11 and the roadmap. Measure theory,
topology carriers, and category theory — not CAS-shaped. Risch — behind item
4, and the July roadmap's own sequencing (LRT first) still holds.

## The blocker

**None of a mathematical kind. Two of an engineering kind, and one of
discipline.**

- **`i128` in the core.** Every module that needed more precision grew its
  own `BigRational` path beside the core, which is why eight modules carry
  bignum code and the zero-test does not. Item 1 removes the reason for the
  duplication.
- **`lib.rs` is 29,505 lines.** Items 3 through 9 each want a module; landing
  them into `lib.rs` would make the next audit's job harder than this one's.
  Land each as its own file with its checker beside it.
- **Every new function ships with its certificate or its `uncertified`
  label** (the crate's standing rule, [`10-cas/README.md`](../research/10-cas/README.md#standing-rules-for-this-initiative-inherited-non-negotiable)).
  Item 10 is what makes that rule measurable instead of promised.

## Progress log

| date | change | evidence |
|---|---|---|
| 2026-09-05 | File created. Baseline: 80,851 lines, 55 modules, 691 `pub fn`, 1,006 tests, `i128` core, `f64` `evalf`; residue 61/16/45. Ten absence probes run with four positive controls; the two single-file hits (`gaussian_int`, `schreier`) were a test name and an Artin–Schreier doc comment, not capability. Capability-parity work has been paused since wave 24 (2026-07-22); all CAS commits since 2026-08-26 are trust work. | `8f6c58420`; `python3 scripts/check-cas-internal-residue.py --report` |
| 2026-09-05 | **Item 3 landed, first slice** (lane `cas-fps`, merged `3e6dd2b46`): `fps.rs`, a truncated ℚ[[x]] over `BigRational` with inverse, composition, compositional reversion, exact rational-function expansion, recurrence unrolling, Berlekamp–Massey guessing (recovers Fibonacci, Lucas, Padovan; declines on the primes) and a certified rational generating function. Three `TruncationIdentity` certificates plus a `RecurrenceCertificate`; 18 guards, each killing exactly one test after the lane found five that rejected through each other on its first sweep. Reused `series_coefficients` (so no transcendental expansion was duplicated) and re-derived the reversion recurrence over bignums because the i128 one overflows on Catalan. Radius of convergence deliberately not shipped: the rational case needs complex roots and Sturm certifies only real ones. | `fps::` 48 passed; crate sweep 989 passed, 0 failed; clippy exit 0 |
| 2026-09-05 | **Item 10 landed, first half** (lane `cas-trust-registry`, merged `a23a289ec`): `scripts/check-cas-trust-registry.py` scans every `pub fn` with a brace-aware scanner that skips `#[cfg(test)]` bodies, derives the certificate vocabulary from the source rather than a list, classifies each function certified / checker / uncertified, and ratchets the certified set with six guards each killed by exactly one control. Registered in `check.sh`, the justfile and `mutation_controls.py`. **The number chair 12 asked for: 698 public functions at the lane's base, 34 certified (4.9%), 26 checkers, 638 uncertified; on merged main with `fps` accepted, 730 / 41 / 29 / 660.** Of the README capability table's 28 rows, 25 claim a certificate for functions that classify uncertified: the column was a self-check discipline claim, not a certificate object. The scanner found and fixed two of its own bugs against the live crate (impl-of-pub-type pass never wired; a `;` inside `Option<[T; 2]>` silently dropped the next signature) and now matches a whole-crate regex 698/698. The gate refused the seven new certified `fps` functions on first run, as designed; accepted with `--write`. `check-aggregate-scope.sh` exits 1 before and after, byte-identical divergence list, pre-existing. | `python3 scripts/check-cas-trust-registry.py` OK floor 41; `mutation_controls.py cas-trust-registry` 6 of 6 killed by exactly one; `artifacts/measurements/cas-trust-registry-2026-09-05.md` |
| 2026-09-05 | **Item 9 landed, first slice** (lane `cas-probability`, merged `2b431eb34`): `probability.rs`, eight named distributions whose mass, mean, variance and mgf each carry a certificate naming the route that decided it, or an honest `Uncertified(reason)`. Convolution tables certified; Poisson+Poisson proved for all k by `prove_wz_sum`, a stronger certificate than the single Poisson's own total mass, which declines. **Three machinery gaps the lane measured rather than assumed, each a follow-up for the CAS itself:** Poisson moments decline because `λᵏ/k!` is not Gosper-summable and `infinite_sum` does not know the exponential series; Geometric mean and variance decline because `limit` cannot cancel a `k/k` factor the telescoped antidifference carries; `Normal(0,1)` declines because `integrate_gaussian` requires a perfect-square coefficient, so only variance 1/2 certifies. Every symbolic-parameter continuous mgf declines. | `probability::` 24 passed; clippy exit 0; 4 guards mutation-checked |
| 2026-09-05 | **Item 8 landed** (lane `cas-homology`, merged `449fc1399`): `homology.rs`, exact integer Betti numbers and torsion for a simplicial complex via the existing Smith form, with a certificate whose `verify` rebuilds every boundary matrix and re-derives every claim; eleven guard conditions each killing exactly one test; verified on the standard triangulations through the 9-vertex Klein bottle. **The finding that outranks the feature: `smith_normal_form` never terminated on the boundary matrix of any 3-cycle**, so the shipped normal form hung on any complex with a triangle in it, and `bareiss_determinant` panicked on the empty matrix. Both fixed with regression tests in `normalforms.rs` and `matrix.rs`. The topology chair now has one thing to reach for. Wall clock not measured; the module doc says so. | `homology::` 22 passed; crate sweep 966 passed, 0 failed; clippy exit 0 |
| 2026-09-05 | **Item 2 landed** (lane `cas-enclosure`, merged `e86eb5a1f`): `enclosure.rs`, certified interval enclosures with exact `BigRational` endpoints to a requested precision over a binding box, for rational arithmetic, integer powers, `sqrt`, `exp`, `ln`, `sin`, `cos`, `atan` and π, each step of the evidence re-derived by `verify` from the head, inputs and truncation order alone; `enclose_root` refines a Sturm-isolated root with the isolation itself re-checked. Thirteen guards each kill exactly one test. Measured, ADVISORY on a host at load 29: π to 500 bits in 20 ms to produce, 15 ms to verify. The constructive-analysis chair's first complaint (a double and no enclosure) is answered for this head set; `gamma`, Bessel, `erf` and non-integer powers still decline, and `evalf` is unchanged. | `enclosure::` 34 passed, 2 doctests; clippy exit 0; hygiene PASS in the lane |
| 2026-09-05 | **Item 5 landed, first slice** (lane `cas-permgroup`, merged `399f294c9`): `permgroup.rs`, deterministic Schreier–Sims over the existing `Permutation` type with order, membership, orbits, stabilizers, cosets, Cayley tables, centre and derived subgroup, every result carrying a certificate that re-derives the claim; S₈ handled without enumeration. One of five guards was measured redundant and is documented as such rather than claimed load-bearing. Sylow, presentations and isomorphism testing remain open. | `permgroup::` 25 passed; clippy exit 0; 4 guards each kill exactly one test |

## How to re-measure

```sh
# size and surface
find crates/axeyum-cas/src -name '*.rs' | xargs cat | wc -l
ls crates/axeyum-cas/src/*.rs | wc -l; ls -d crates/axeyum-cas/src/*/ | wc -l
grep -rhE '^\s*pub fn ' crates/axeyum-cas/src --include=*.rs | wc -l
grep -rh '#\[test\]' crates/axeyum-cas/src crates/axeyum-cas/tests | wc -l

# the trust split (the number file 11 and the roadmap also quote)
python3 scripts/check-cas-internal-residue.py --report

# the core arithmetic and evalf claims
grep -n 'i128' crates/axeyum-cas/src/lib.rs | head -3
grep -n 'pub fn evalf' crates/axeyum-cas/src/lib.rs

# absence probes -- file counts, case-insensitive; a hit must be READ, not
# counted (two of the baseline hits were false), and every negative needs a
# positive control of the same query shape:
for p in 'number_field|class_group|dedekind' 'cornacchia|two_squares' \
         'elliptic' 'factor_multivariate|multivariate_factor' 'galois' \
         'schreier|sylow|coset' 'pub struct.*(PowerSeries|FormalSeries)' \
         'generating_function' 'holonomic|guess_recurrence' \
         'struct [A-Za-z]*Distribution' 'fourier_transform' \
         'pub fn .*conic|struct Point3' 'quantifier_elim|cylindrical_alg' \
         'simplicial|homology' 'entropy'; do
  printf '%-60s %s\n' "$p" "$(grep -rliE "$p" crates/axeyum-cas/src | wc -l)"
done
grep -rlE 'pub fn (smith_normal_form|laplace_transform|gosper_sum|count_real_roots)' \
  crates/axeyum-cas/src   # positive controls: four files
```

## Related

- [11-applied-and-computational.md](11-applied-and-computational.md) — the
  trust axis of the same crate: residue, producers, reconstruction
- [`docs/research/10-cas/README.md`](../research/10-cas/README.md) — the
  capability table and the July roadmap this file supersedes as a
  priority list
- [`docs/plan/cas-parity-handoff-2026-07-22.md`](../plan/cas-parity-handoff-2026-07-22.md)
  — the paused wave-24 checkpoint and the gap-probing method
- [ADR-0301](../research/09-decisions/adr-0301-cas-layer-reduce-to-decide.md),
  [ADR-0601](../research/09-decisions/adr-0601-three-producers-one-trust-anchor.md),
  [ADR-1400](../research/09-decisions/adr-1400-a-certificate-must-record-every-distinction-its-acceptance-depends-on.md)

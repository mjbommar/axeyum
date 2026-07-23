# CAS Parity Push — Handoff & Resume Guide (2026-07-22)

Working state and pick-up instructions for the **proof-carrying CAS**
(`crates/axeyum-cas`) parity effort against SymPy / Mathematica. This is the
"CAS half" of axeyum (the other half being the SMT/Lean lanes documented
elsewhere in `docs/plan/`). Read this file first when resuming.

---

## 1. TL;DR state

- **Branch/worktree discipline:** follow the current
  [multi-agent operations guide](../contributor-guide/multi-agent-operations.md):
  work only in the dedicated CAS worktree on an `agent/cas/*` branch, push that
  branch, and leave `main` to the integration owner. The current increment is
  `agent/cas/gap-probe-wave-thirteen`, based on integration parent `4682a486`,
  with implementation commit `3a361b0a` (integrated by `44e08f0b`); do not
  rebase it onto `main` ahead of the integration owner.
- **Tests:** `554` unit + `147` doctests, **all green**, warning-denied workspace
  all-target/all-feature Clippy-clean, strict stable/nightly rustdoc-green,
  wasm-green, links-green, and whitespace-clean.
- **Source of truth for capabilities:** `docs/research/10-cas/README.md`
  (capability table) and `docs/research/10-cas/diary.md` (chronological entries;
  latest is **Entry 37afb**). Keep both in sync when landing features.
- **Method that works:** empirical **gap-probing** (below). It found every recent
  feature *and* a serious infinite-hang regression.

---

## 2. How to build / test / iterate (READ THIS — there are gotchas)

Everything runs in the axeyum worktree:
`/nas4/data/workspace-infosec/claude-axeyum-cas-work`.

```bash
# The full gate before any commit:
: "${AXEYUM_CAS_TMP:?create AXEYUM_CAS_TMP with the guarded setup below}"
CARGO_BUILD_JOBS=1 TMPDIR="$AXEYUM_CAS_TMP" cargo test -p axeyum-cas --jobs 1
CARGO_BUILD_JOBS=1 cargo clippy --workspace --all-targets --all-features --jobs 1 -- -D warnings
CARGO_BUILD_JOBS=1 cargo build -p axeyum-cas --target wasm32-unknown-unknown --jobs 1
RUSTDOCFLAGS="-D warnings" CARGO_BUILD_JOBS=1 cargo +stable doc -p axeyum-cas --no-deps --jobs 1
RUSTDOCFLAGS="-D warnings" CARGO_BUILD_JOBS=1 cargo doc -p axeyum-cas --no-deps --jobs 1
./scripts/check-links.sh
git diff --check
```

### Critical gotcha: `TMPDIR`
The tmpfs `/tmp` hits **"Disk quota exceeded"** when the ~147 doctests link
concurrently. **Always** point `TMPDIR` at a roomy disk:

```bash
AXEYUM_CAS_TMP="$(mktemp -d /nas4/data/tmp/axeyum-cas-full.XXXXXX)"
case "$AXEYUM_CAS_TMP" in
  /nas4/data/tmp/axeyum-cas-full.*) ;;
  *) exit 2 ;;
esac
export AXEYUM_CAS_TMP
trap 'find "$AXEYUM_CAS_TMP" -depth -delete' EXIT
```
Without this, doctests fail with a spurious linker `LLVM ERROR: IO failure`.

### Commit / push cadence
Commit after each feature with the full gate green, using pathspec-only staging
and commits. Push the owned topic branch for the integration owner:
```bash
git add crates/axeyum-cas/src/... docs/research/10-cas/...
git commit -- <same owned paths>
git push -u origin HEAD
```

### Doc sync on every feature
- bump the test count in `docs/research/10-cas/README.md` (the
  `NNN unit + 147 doctests` line),
- append a diary entry to `docs/research/10-cas/diary.md`.

---

## 3. The gap-probing method (the productive loop)

This is how essentially all recent progress was made. Repeat:

1. Write a throwaway `crates/axeyum-cas/examples/probe_*.rs` exercising a batch of
   operations SymPy/Mathematica handle (integrals, limits, sums, series, solve,
   simplify, transforms). Cover a spread; you're hunting for `DECLINE` or a
   *degenerate/wrong/ugly* result.
2. Run it under a **timeout** (some finders can hang — see §5):
   ```bash
   timeout 60 bash -c 'TMPDIR="$CLAUDE_JOB_DIR/tmp/doctmp" \
       cargo run -q -p axeyum-cas --example probe_x 2>/dev/null' || echo HANG
   ```
   If a batch hangs, bisect by testing integrands one at a time with a short
   timeout to find the culprit.
3. For each real gap, find the responsible finder/function, add a targeted,
   **certified**, value-preserving fix (new integration finder, simplify
   candidate, zero-test canonicalization, etc.).
4. TDD it, run the full gate, sync docs, commit, push. **Delete the probe file.**

Gotchas when probing:
- Output can be swallowed on panic / block-buffering — write to a file and
  `grep -a`, or add `std::io::Write::flush(&mut std::io::stdout()).ok();`.
- `grep` reports "binary file matches" on the `\0`-prefixed atom keys — use `grep -a`.
- **Applying `simplify` to an `apart`/partial-fraction result re-combines it** —
  don't wrap `apart` output in `simplify` and conclude it "didn't decompose".
- Probe *targets* are sometimes wrong (a limit that genuinely diverges *should*
  DECLINE). Verify the math before "fixing" a correct decline.

---

## 4. What landed this session (chronological highlights)

The marquee arc, roughly in order. Vandermonde is on `main`; the adjacent,
fixed-shift, and moment extensions are on the current CAS topic stack pending
green integration by the `main` owner:

**Foundations / gammasimp**
- **`gammasimp`/`combsimp`**: the Γ functional equation `Γ(z+1)=z·Γ(z)` now lives
  in the zero-test (`combine_gamma_ratios` lowers every Γ to an integer-stripped
  base; wired into `simplify` + `equal`'s `canonicalize_for_equality`). This
  unlocked most of what follows.
- **Zero-test completeness fix**: `atom_name` now falls back to
  `normalize_rational` so `ln(ln x+1) = ln(1+ln x)` (transcendental-atom argument
  ordering) decides.

**Special functions / integrals / sums**
- Beta integral for fractional exponents; Γ reflection `Γ(z)Γ(1−z)=π/sin πz` +
  special-angle trig in the zero-test; modified Bessel `Iₙ`.
- Gosper for **factorial/binomial** hypergeometric terms; telescoping rational
  products `∏(1−1/k²)=(n+1)/(2n)`.
- Many integration finders (each certified by differentiate-and-check):
  `∫tanⁿx`, `∫p(x)√(ax+b)`, `∫eˣsin²x` (power reduction), `∫sinh²x` (expand
  fallback), `∫cos(ln x)`, `∫F(root_q x)` (√x/∛x), `∫√(a²∓x²)` general `a`,
  `∫₀^∞ ln x/(1+x²)=0`, `∫1/(1+tan x)`.
- `cancel` constant-denominator absorption (`(3/8·π)/2→3π/16`);
  `fold_power_quotient` (`(s−3)/(s−3)⁴→1/(s−3)³`, keeps Laplace denominators
  factored); double-angle contraction (`2 sin x cos x → sin 2x`).
- `solve_polynomial_system` surd solutions; algebraic limit of a product-with-
  radical (`x(√(x²+1)−x)=½`); fractional binomial series `(1+x)^{1/q}`.
- **Correctness bug fixed**: `∑k·cᵏ` was returning `-(0/0)` (route to
  `geometric_gosper` before `rational_gosper`).
- **Hang bug fixed**: `∫sin^odd·cos^even` looped forever in
  `integrate_power_reduced_trig`; guarded with `has_odd_trig_power`.

**★ Zeilberger / Wilf–Zeilberger (the marquee)** — `prove_wz_sum(...)`
Proves definite hypergeometric identities *soundly*. Currently proven:
`∑ₖ C(n,k)=2ⁿ`, `∑ₖ k·C(n,k)=n·2ⁿ⁻¹`, `∑ₖ k²·C(n,k)=n(n+1)2ⁿ⁻²`,
Vandermonde, a checked fixed-shift binomial-convolution family (regressed for
`r=0..7`), a direct squared-binomial falling-factorial family (regressed for
orders `0..=255`), and Stirling-composed raw moments (regressed for orders
`0..=35`). False near-misses correctly decline.

**Bounded polynomial-geometric Z transforms**
- A cross-area, timeout-bounded probe found that Fourier series (`|x|`, `e^x`),
  representative inhomogeneous ODEs, positive-assumption radical refinement,
  and polynomial-times-exponential Laplace pairs already succeeded. The concrete
  standard declines were `Z{n·2ⁿ}`, `Z{n²·2ⁿ}`, and double/triple inverse-Z
  poles, so this increment closes that measured gap rather than widening an
  already-green family.
- `z_transform` accepts linear combinations of `P(n)aⁿ`, where `P` has rational
  coefficients and degree at most 32 and `a` is a positive rational. It converts
  `P(n)=Σqᵣ(n)ᵣ` exactly and composes
  `Z{(n)ᵣaⁿ}=r!aʳz/(z−a)ʳ⁺¹` over one known denominator with private
  `BigRational` intermediates. Every final coefficient must still fit the public
  checked-`i128` `Rational` domain.
- `inverse_z_transform` accepts `X(z)/z` only when it is strictly proper and its
  denominator factors completely into positive-rational poles of multiplicity
  at most 32. For a pole `a` of multiplicity `m`, derivatives of
  `H(z)=(z−a)^mX(z)/z` recover each principal-part coefficient; the corresponding
  sequence is `Cⱼ binomial(n,j−1)a^(n−j+1)`. The result is returned only when the
  exact forward transform certifies the original `X(z)`.
- Regressions use independent reciprocal-power-series coefficients across four
  bases and three polynomial shapes, an independently generated Eulerian row at
  degree 32, every unit-pole multiplicity 1 through 32, mixed poles, and explicit
  negative controls. Degree 33, multiplicity 33, nonlinear exponents,
  non-positive/irrational poles, improper inputs, and overflow decline. The
  foundational DAG and research-question register require no ADR: no public
  operator, backend, evidence format, or logic fragment changed.

**Symmetric-period rational-trig Fourier boundary**
- The next bounded probe confirmed that polynomial/exponential Fourier series,
  representative ODEs, assumptions, and repeated-root recurrences already
  succeed. Repeated irreducible-quadratic inverse-Laplace poles consistently
  decline and remain the next measured transform family; the elliptic integral
  prototype also declines but needs a deliberate new head/semantics boundary.
- The same probe found a correctness-priority representation seam before those
  missing features: rational-trig Fourier coefficients on `[-π,π]` reached the
  generic FTC path, whose certified Weierstrass antiderivative is discontinuous
  at the endpoints. It returned expressions containing `tan(±π/2)`. Their
  floating evaluations happened to approach the right numbers, but the exact
  zero-test rejected equality with the known coefficients.
- `definite_full_period_rational_trig` now treats both `[0,2π]` and `[-π,π]` as
  canonical full periods. For the symmetric spelling, `t=tan(x/2)` maps the
  open interval monotonically to `(-∞,∞)`; for the zero-based spelling its two
  branches concatenate to the same whole-real-line integral. Both retain the
  existing certified improper rational integration route, while `[0,π]`
  retains its half-line route.
- The focused regression independently freezes the exact base integral, first
  cosine coefficient, and two-harmonic expansion of `1/(2+cos x)`; existing
  full/half-period and non-rational-trig Fourier controls remain green. This is
  a proof-boundary correction with no public operator, evidence format,
  backend, or logic change, so the foundational DAG and research-question
  register require no ADR.

**Repeated irreducible-quadratic inverse Laplace**
- The next measured transform family is now closed for rational damped
  frequency through multiplicity 7. Exact `apart` terms `(A(s))/q(s)^m` are
  reconstructed in the `2m`-member basis
  `tʳe^{αt}{cos,sin}(βt)`, `0≤r<m`. Each basis column comes from the existing
  forward Laplace transform; one exact rational solve finds the coefficients,
  and the pre-existing whole-expression forward zero-test round trip remains
  mandatory before a result is returned.
- Explicit controls freeze `1/(s²+1)²`, `s/(s²+1)²`, `1/(s²+1)³`, a shifted
  damped double pole, and `1/((s−2)(s²+1)²)`. The mixed result was independently
  checked against SymPy's partial fractions and inverse transform. Every unit-
  quadratic multiplicity 1 through 7 additionally round-trips.
- Multiplicity 8 is the first explicit resource decline: it needs the
  `t⁷cos(βt)` basis member, whose forward expression exists but whose rational
  normalization exceeds the public checked-`i128` coefficient path. Irrational
  frequencies still decline because the forward transform cannot certify them.
  This is a bounded reconstruction extension, not permission to bypass either
  exact normalization or the round trip.
- No public operator, backend, evidence format, or logic fragment changed, so
  the foundational DAG and research-question register require no ADR.

**Rational-scale/shift Bessel-`J₀` Laplace pairs**
- A third timeout-bounded cross-area probe found five standard declines around
  the already-public `BesselJ(0)` head: forward `J₀(t)`, `J₀(2t)`, and
  `e^tJ₀(2t)`, plus inverse `1/√(s²+1)` and
  `1/√((s−1)²+4)`. Adjacent two-quadratic rational inversion, full-period
  rational-sine integration/Fourier, and a nonzero exact IVP control remained
  green. The elliptic new-head control still declines.
- `laplace_base` now implements NIST DLMF 3.5.40,
  `J₀(bt) ↦ 1/√(s²+b²)`, for rational `b`. The pre-existing exponential shift
  and transform-derivative machinery then supplies `e^{at}J₀(bt)` and
  `t^kJ₀(bt)` without a second formula path. `J₀(0)` is handled as `1` rather
  than emitting branch-dependent `1/√(s²)`.
- The inverse route accepts a rational-scaled square root of a quadratic only
  when completing the square yields rational shift/frequency and the leading
  coefficient has a rational square root. It constructs
  `(c/√lead)e^{at}J₀(bt)` but still requires the public forward transform plus
  exact zero-test to reproduce the whole input before returning it.
- NIST fixes the base formula; an independent SymPy check agrees on the unit,
  scaled, and shifted forward transforms. Regressions additionally freeze a
  polynomial `t` weight and rational half-frequency inverse, then require
  `J₁`, irrational frequency, and nonquadratic radicals to decline. The `J₁`
  result was the measured next gap at this historical checkpoint and is closed
  by the arbitrary-order extension below.
- No new expression head, public operator, backend, evidence format, or logic
  fragment was introduced, so the foundational DAG and research-question
  register require no ADR.

**Exact-expression initial-condition data**
- The wave-three declines `y(0)=√2, y′(0)=1` and `y(0)=A, y′(0)=B` now
  specialize the oscillator to `√2 cos x+sin x` and `A cos x+B sin x`.
  SymPy independently agrees on both forms and on the retained rational
  `x=π/2` control `−3 cos x+2 sin x`.
- The evaluated baseline and every integration-constant coefficient remain in
  the exact rational fragment. When the condition right-hand sides are not
  rational, the implementation obtains each inverse-matrix column from the
  existing checked-`i128`/bounded-bignum rational solver, then forms exact
  `CasExpr` linear combinations. It does not introduce symbolic pivoting or
  assume a denominator nonzero.
- After substituting every solved constant, the public path differentiates and
  evaluates the complete result for every original condition. A result is
  returned only when the zero-test certifies each equality. This adds the
  missing checker boundary to the older rational-only specialization too.
- Expression-valued systems are capped at 16 constants. Reserved integration-
  constant-shaped data, data depending on the ODE variable, nonrational basis
  coefficients, singular systems, and dimension 17 decline. A 17-constant
  rational system succeeds, proving the existing rational path was not
  narrowed by the symbolic cap.
- No expression head, operator, backend, evidence format, or logic fragment
  changed; this is a bounded extension and certification strengthening of the
  existing public IVP operation, so no ADR is required.

**Generic first-order inhomogeneous routing**
- The next measured gap was dispatch, not mathematics:
  `dsolve_inhomogeneous([1,1], e^x)` and the sine analogue declined while the
  direct `dsolve_first_order_linear` calls succeeded. Scaled-leading and
  resonant controls exposed the same disconnect. Polynomial forcing and the
  existing second-order variation-of-parameters route were already green.
- For a trimmed operator of exact degree one, the non-polynomial path now
  rewrites `c₁y′+c₀y=f` as `y′+(c₀/c₁)y=f/c₁` with checked exact rationals and
  calls the existing integrating-factor solver. That solver keeps its own
  normalized-equation differentiate-and-check certificate; the wrapper then
  independently evaluates `c₁y′+c₀y` and requires the zero-test to certify the
  original forcing before returning.
- Regressions cover exponential and sine forcing, nonunit positive and negative
  leading coefficients, resonance, a derivative-only operator, and trailing
  zero coefficients. Degree-zero/cubic operators and `1/(x²+1)` forcing retain
  honest declines. A polynomial control proves undetermined coefficients is
  unchanged, and the pre-existing second-order suite remains green.
- Independent SymPy checks agree on `y′+y=e^x`, `y′+y=sin x`,
  `2y′+4y=e^x`, and resonant `2y′−2y=e^x`. No public operator, expression head,
  backend, evidence format, or logic fragment changed, so the foundational DAG
  and research-question register require no ADR.

**Arbitrary-order rational-scale/shift Bessel-`Jₙ` Laplace transforms**
- A fourth timeout-bounded cross-area probe retained exact Fourier controls for
  `|sin x|` and `sign(sin x)`, while `J₁(t)`, `J₂(2t)`, shifted/weighted `J₁`,
  modified Bessel `I₀/I₁`, Bessel integrals/asymptotics, inverse `J₁`/`I₀`
  forms, and a quadratic inverse-Z form declined. This selected the existing-
  head Bessel-`Jₙ` forward family without narrowing the wider backlog.
- `laplace_base` now implements the nonnegative-integer specialization of NIST
  DLMF 10.22.49,
  `L{Jₙ(bt)}=((√(s²+b²)−s)/b)ⁿ/√(s²+b²)` for exact nonzero rational `b`.
  The `b=0` boundary returns `1/s` at order zero and zero at positive orders.
  The expression uses one symbolic power rather than an order-sized loop, so
  the full public `u32` order domain, including `u32::MAX`, remains bounded.
- Existing exponential shift and transform differentiation compose unchanged,
  covering `e^{at}Jₙ(bt)` and `t^kJₙ(bt)`. Regressions freeze orders 1--4,
  positive/negative half and integer scales, shift, polynomial weight, zero
  argument, and the extreme order. An independent exact scenario replays
  `sF₀+bF₁=1` and `sFₙ=(b/2)(Fₙ₋₁−Fₙ₊₁)` through order 17 at scales
  `1`, `−2`, and `1/2`; SymPy independently agrees for orders 0--3.
- Modified Bessel `I₀`, irrational Bessel scale, and affine Bessel argument
  retained explicit declines at that historical checkpoint. The modified-
  Bessel gap is closed by the next increment; irrational and affine arguments
  still decline. No public expression head, operator, backend, evidence format,
  or logic fragment changed, so no ADR is required.

**Arbitrary-order rational-scale/shift modified-Bessel-`Iₙ` Laplace and inverse `I₀`**
- The handoff-ranked follow-up probe confirmed forward `I₀`, `I₁`, scaled
  `I₂`, shifted `I₀`, polynomial-weighted `I₁`, and unit/shifted inverse `I₀`
  all declined, while the arbitrary-order Bessel-J control remained green.
- Laplace-transforming the integer-order NIST DLMF 10.32.3 integral
  representation gives
  `L{Iₙ(bt)}=((s−√(s²−b²))/b)ⁿ/√(s²−b²)` for nonzero exact rational `b` in
  `Re(s)>|b|`. `laplace_base` now implements that form for every public order;
  `b=0` returns `1/s` at order zero and zero at positive orders. One symbolic
  power represents the order, so the full `u32` domain remains bounded.
- Existing exponential shift and transform differentiation cover
  `e^{at}Iₙ(bt)` and `t^kIₙ(bt)`. Independent exact replay checks
  `sF₀−bF₁=1` and `sFₙ=(b/2)(Fₙ₋₁+Fₙ₊₁)` through order 17 at scales `1`,
  `−2`, and `1/2`. SymPy independently agrees on representative orders 0--4.
- `inverse_laplace` now recognizes exact rational square-root quadratics of
  the form `c/√((s−a)²−b²)`, constructs `c·e^{at}I₀(bt)`, and retains the
  existing mandatory public-forward-transform plus zero-test round trip.
  Unit, signed-scale, shifted integer-frequency, and shifted half-frequency
  pairs pass. Irrational forward scales, affine arguments, irrational inverse
  frequencies, non-square leading scale, and zero-frequency branch-degenerate
  radicals decline. No public expression head, operator, backend, evidence
  format, or logic fragment changed, so no ADR is required.

**Exact rational-scale/shift order-one Bessel inverse Laplace pairs**
- A fifth timeout-bounded broad probe compared the handoff-ranked inverse
  family against adjacent surfaces. Unit/scaled/shifted `J₁` and `I₁`, plus
  order-two controls, all declined. Bessel Maclaurin series and zero limits
  also declined at that checkpoint and are closed by the increment below;
  the measured elementary Bessel antiderivatives are likewise closed below.
  In contrast, two rational-trigonometric Fourier families and exact
  Gaussian/rational integrating-factor ODE controls were already green.
- `inverse_laplace_bessel_order_one` finds exactly one distinct square-root
  atom, normalizes its quadratic radicand to recover the rational shift and
  positive rational frequency, and constructs the matching `J₁` or `I₁`
  candidate. The complete input must reduce to a rational multiple of that
  candidate's public `laplace_transform`; the outer `inverse_laplace` gate then
  independently repeats the whole forward transform and exact zero-test before
  returning. Discovery is therefore not acceptance.
- Regressions cover both families over positive/negative integer and half
  frequencies, three shifts, expanded unit spellings, and an independent outer
  scale. Negative frequencies canonicalize to a positive frequency plus the
  odd-parity outer sign. Order two, irrational frequency, a malformed linear
  numerator, two distinct radicals, and zero frequency decline. SymPy
  independently agrees on unit, integer/half-frequency, and shifted formulas.
  No new expression head, public operator, backend, evidence format, or logic
  fragment changed, so no ADR is required.

**Exact arbitrary-order Bessel Maclaurin series and zero limits**
- `series` now expands every existing nonnegative integer-order `Jₙ` and `Iₙ`
  head when its argument vanishes at the origin. It uses the exact recurrence
  `c₀=1/(2ⁿn!)`, `cₖ=cₖ₋₁/(4k(n+k))`, alternating signs only for `Jₙ`, then
  composes those coefficients with the ordinary inner power series.
- The valuation check precedes any order-dependent loop, so an order larger
  than the requested truncation—including `u32::MAX`—returns the exact zero
  truncation promptly. Checked public `i128` rational arithmetic remains the
  representation boundary: `J₀/I₀` succeed through degree 32 and decline at
  degree 34; `J₁` succeeds through degree 33 and declines at degree 35.
- DLMF 10.2.E2 and 10.25.E2 fix the formulas. Explicit `J₀/J₁/J₂` and
  `I₀/I₁/I₂` fixtures, SymPy composition checks, and both defining Bessel ODEs
  through order 16 / degree 24 independently exercise the implementation.
  The public limit path now computes the removable values
  `Jₙ(x)/xⁿ=Iₙ(x)/xⁿ→1/(2ⁿn!)` at zero for the tested orders 0 through 8.
  Series remains a compute operation without a proof artifact; no expression
  head, public operator, backend, evidence format, or logic fragment changed,
  so no ADR is required.

**Certified direct and weighted Bessel antiderivatives**
- The direct rational-affine pairs `∫J₁(u)dx=−J₀(u)/slope` and
  `∫I₁(u)dx=I₀(u)/slope` first closed through the public derivative
  rules and ordinary differentiate-and-zero-test certificate. They retain
  arbitrary variable-free outer factors and explicit nonlinear, symbolic-slope,
  overflow, and other-order declines.
- The weighted follow-up now accepts `c·u·J₀(u)` and `c·u·I₀(u)` for
  rational-affine `u` and variable-free `c`, including rationally rescaled
  weights such as `xJ₀(2x)`. Its candidates are `(c/slope)uJ₁(u)` and
  `(c/slope)uI₁(u)` and still return only after the unchanged public
  differentiate-and-check gate succeeds.
- The zero-test closes the product derivative using only the division-free
  DLMF 10.6.1 / 10.29.1 recurrences `uJ₂=2J₁−uJ₀` and
  `uI₂=uI₀−2I₁`. It rewrites an order-two atom only when its full
  polynomial coefficient divides exactly by the same normalized argument; the
  replacement strictly lowers that atom's exponent. This is value-preserving,
  terminating, and valid at `u=0`, unlike a `J₂=2J₁/u−J₀` spelling.
- Unit, rational-scale, shift, reflection, symbolic-factor, exact recurrence,
  near-miss, and FTC controls pass. Unweighted/mismatched weights, nonlinear
  arguments, symbolic slopes, other orders, and reciprocal overflow decline.
  No public operator, head, backend, evidence format, or logic fragment changed,
  so no ADR is required.

**Exact rational-scale/shift order-two Bessel inverse Laplace pairs**
- A sixth timeout-bounded probe measured unit/shifted `J₂` and `I₂` inverse
  transforms as the best bounded existing-head decline. Order three, weighted
  order-one transforms, elliptic integration, and quadratic-pole inverse Z
  remained honest declines; Fourier-exponential and second-order ODE controls
  stayed green.
- The private indexed recognizer shares one parameter-discovery route for
  orders one and two, but public dispatch enumerates only those exact orders.
  It reconstructs a rational shift and positive rational frequency from one
  quadratic radical and requires the complete input to be a rational multiple
  of the selected public forward transform.
- The outer inverse route still independently applies the complete public
  forward transform and exact zero-test before returning. Recognition alone is
  never evidence. Independent explicit unit formulas supplement the generated
  round-trip matrix.
- Positive/negative integer and half frequencies, three shifts, both families,
  and an outer scale pass. Odd order-one and even order-two parity are frozen;
  order three and the malformed/irrational/zero-frequency boundaries decline.
  No public head, operator, backend, evidence format, or logic fragment changed,
  so no ADR is required.

**Certified additive radical-bearing inverse Laplace closure**
- Wave seven measured same-radical, distinct-radical, and rational-plus-Bessel
  inverse sums as clean declines. Nonzero-center Bessel series and the Fourier/
  ODE controls were already green; weighted Bessel transforms/integrals,
  asymptotics, improper `J₀`, and quadratic inverse Z remain larger gaps.
- The additive inverse route activates only for expressions containing a square
  root, recursively processes strict children, requires every summand to pass
  its existing inverse certificate, and independently forward-transforms plus
  zero-tests the complete sum. Ordinary rational sums retain their established
  whole-expression path.
- Same/distinct Bessel families and frequencies, nested sums, a shifted/scaled
  order-two term plus rational pole, and `1/s+J₀` pass. A supported term plus
  order three or irrational frequency makes the whole sum decline. The mixed
  case exposed and fixed the zero-pole basis `exp(0t)→1`; a rational-cancellation
  control freezes the old whole-expression route.
- DLMF 1.14.17 supplies the integral definition from which linearity follows.
  No public head, operator, backend, evidence format, or logic fragment changed,
  so no ADR is required.

**Certified weighted order-one Bessel antiderivatives**
- The next bounded integration gap now accepts `c·u²·J₁(u)` and
  `c·u²·I₁(u)` for nonconstant rational-affine `u` and variable-free `c`,
  including exact rational multiples of `u²`. The candidates are
  `(c/slope)u²J₂(u)` and `(c/slope)u²I₂(u)` and still return only after the
  unchanged public differentiate-and-zero-test gate succeeds.
- DLMF 10.6.6 and 10.29.4 supply the derivative identities. The zero-test now
  closes their product derivatives with division-free recurrences for target
  orders two and three, processed in descending order. A target is rewritten
  only when its complete coefficient divides exactly by the normalized
  argument; the replacement lowers that target and introduces only lower
  orders, so no `1/u` seam or unbounded recurrence search is added.
- Unit, rational-scale, shifted, reflected, symbolic-factor, exact recurrence,
  derivative-replay, and definite-FTC controls pass. Lower/higher or mismatched
  weights, order-two integrands, nonlinear arguments, symbolic slopes, and
  reciprocal overflow decline. Recurrence collection remains explicitly
  bounded to orders two and three; no arbitrary-order integral claim is made.
  No public head, operator, backend, evidence format, or logic fragment changed,
  so no ADR is required.

**Certified weighted integer-order Bessel antiderivative family**
- Wave nine measured weighted order-two/three antiderivatives against already-
  green polynomial-weighted Bessel Laplace controls and continuing declines for
  order-three inverse Laplace, improper/limit `J₀`, and quadratic inverse Z.
- The order-generic DLMF 10.6.6 / 10.29.4 identities now drive
  `∫c·uⁿ⁺¹Jₙ(u)=(c/slope)uⁿ⁺¹Jₙ₊₁(u)` and the corresponding `I` family for
  rational-affine `u`, variable-free `c`, and the explicit discovery cap
  `0≤n≤32`. Every candidate still passes the complete public derivative and
  exact zero-test certificate; order 33 and wrong powers decline.
- Division-free recurrence equality is safe for every public `u32` order: each
  finite descriptor rewrites only an exact argument multiple, lowers the target
  atom, and introduces only lower orders. The recurrence coefficient is widened
  to checked `i128` before doubling, and regressions reach `u32::MAX`.
- J/I orders 2, 3, 8, 16, and 32, shifts, reflection, nested symbolic factors,
  derivative replay, and definite FTC pass. The nested symbolic/reflected case
  also hardened variable-free-factor extraction to flatten multiplication
  recursively rather than depend on tree association. No public head, operator,
  backend, evidence format, or logic fragment changed, so no ADR is required.

**Certified bounded integer-order Bessel inverse-Laplace family**
- Wave ten audited the existing positive-order inverse recognizer after order
  three remained the nearest measured transform gap. The same DLMF-backed
  indexed forms used by the arbitrary-order forward transformer now drive
  bounded inverse discovery for `Jₙ` and `Iₙ` through order 32; the established
  order-zero routes complete the family `0≤n≤32`.
- Recognition remains subordinate to two exact gates: the complete input must
  be a rational multiple of the selected public forward basis, and the outer
  inverse route independently forward-transforms and zero-tests the reconstructed
  result. Additive radical-bearing inputs retain their all-summands-or-none rule.
- J/I orders 3, 8, 16, and 32, a shifted/scaled order-seven case, complete
  forward roundtrips, and `J₀+J₃` pass. Order 33 and `u32::MAX`, irrational or
  zero frequency, malformed numerators, and supported-plus-order-33 sums
  decline. No public head, operator, backend, evidence format, or logic fragment
  changed, so no ADR is required.

**Certified rational-scale integer-order Bessel-J improper integrals**
- Wave eleven ranked the existing-head DLMF integral ahead of quadratic-pole
  inverse Z, which requires a new oscillatory sequence fragment and exact angle
  representation. DLMF 10.22.41 gives `∫₀^∞Jₙ(t)dt=1` for every public
  nonnegative integer order.
- `improper_integrate` applies the exact change of scale to `c·Jₙ(ax)` for any
  nonzero rational `a` and `x`-free factor `c`. Negative scales use integer-order
  parity. The rule is constant-time in `n`; orders through `u32::MAX`, half and
  reflected scales, and symbolic factors pass.
- Modified Bessel `I`, shifted/nonlinear/irrational/zero scales, checked-negation
  overflow, and a nonzero lower bound decline. The value is theorem-backed; no
  elementary-antiderivative claim is made. No public head, operator, backend,
  evidence format, or logic fragment changed, so no ADR is required.

**Certified affine integer-order Bessel-J limits at both infinities**
- Wave twelve's bounded probe confirmed that standalone/rational-affine `Jₙ`
  limits still declined alongside the deliberately unsupported modified,
  irrational, nonlinear, reciprocal, and polynomial-weighted neighbors. NIST
  DLMF 10.17.3 gives the fixed-order oscillatory `O(|z|^{-1/2})` envelope, and
  10.11.1 transfers it across the negative real direction for integer order.
- `limit` now returns zero for `c·Jₙ(ax+b)` at `+∞` or `−∞` for every public
  nonnegative integer order, nonzero rational `a`, rational `b`, and `x`-free
  `c`. The rule is constant-time in `n`; orders through `u32::MAX`, both scale
  signs and infinities, rational shifts, symbolic factors, and additive
  linearity pass. SymPy independently agrees for orders 0 through 3 across
  half, shifted positive, and shifted negative scales.
- Modified Bessel `I`, irrational/nonlinear arguments, symbolic shifts,
  reciprocals, and polynomial weights decline. Constant and finite-point
  `J₀(0)=1` behavior remains unchanged. No public head, operator, backend,
  evidence format, or logic fragment changed, so no ADR is required.

**Certified rational-polynomial integer-order Bessel-J limits**
- Wave thirteen compared the adjacent nonlinear `Jₙ` limit gap with
  quadratic-pole inverse Z. The latter still needs a new oscillatory-sequence
  transform fragment, while every nonconstant real polynomial has unbounded
  magnitude at both infinities and therefore remains under DLMF 10.17.3's
  fixed-order envelope plus 10.11.1's integer-order continuation.
- `limit` now returns zero for `c·Jₙ(p(x))` at either real infinity for every
  public order, nonconstant rational-coefficient polynomial `p`, and `x`-free
  `c`. Orders through `u32::MAX`, degrees two through four, both leading signs
  and infinities, a half coefficient, shifts, and symbolic factors pass. SymPy
  independently agrees for orders 0 through 3 on all four polynomial shapes.
- Rational-function arguments such as `x+1/x`, irrational or symbolic
  polynomial coefficients, modified Bessel `I`, and variable-dependent outer
  weights decline. No public head, operator, backend, evidence format, or logic
  fragment changed, so no ADR is required.

---

## 5. Zeilberger / WZ — how it works and where to extend

`prove_wz_sum(summand, n, k, rhs, base, k_lo, k_hi) -> Option<CasExpr>`
(returns the certificate `R(n,k)` iff proven). File: `crates/axeyum-cas/src/lib.rs`.

Pipeline:
1. `f = F/rhs`. The WZ pair: a rational certificate `R(n,k)` gives
   `f(n+1,k) − f(n,k) = G(n,k+1) − G(n,k)` with `G = R·f`; summing over `k`
   collapses the RHS to 0, so `S(n)=∑ₖ f` is constant, pinned to 1 by the base.
2. **Discovery (heuristic):** run the factorial-capable `gosper_sum`, or its
   exact structured-ratio fallback, on the WZ term at up to sixteen concrete
   `n`. The small rational ratios are derived while `n` is still symbolic and
   then specialized, avoiding equivalent concrete gamma towers whose factorial
   constants overflow. Extract `R(nᵢ,k)`, monic-normalize the denominator, and
   interpolate each coefficient over `n` with
   `rational_interpolate` (lowest-total-degree `P(n)/Q(n)` with a monic
   denominator, balanced-degree tie-breaking, and validation against every
   available sample — subsumes Lagrange and admits poles such as `1/(2n)`).
3. **Soundness gate (symbolic):** verify `equal(G(n,k+1)−G(n,k),
   f(n+1,k)−f(n,k))` with `n,k` both symbolic. A wrong/under-fit interpolation
   fails here and the prover declines. This leans on gammasimp + the atom-ordering
   fix.

Enabling Gosper fixes: `reduce_fraction` divides out common scalar content before
the GCD and normalizes every Euclidean remainder to its primitive part (large
gamma-lowered ratios otherwise overflow despite a small reduced quotient);
`nonneg_integer_dispersion` scans `j=0..64` by direct shifted polynomial GCD
instead of materializing an overflow-prone symbolic resultant; and
consecutive-ratio extraction cancels exact common monomial content before
requiring a univariate ratio. A structured-difference fallback uses
`a=f(n,k+1)/f(n,k)` and `d=f(n+1,k)/f(n,k)` to represent the difference as
`f(n,k)(d−1)` and its consecutive ratio as
`a(d(n,k+1)−1)/(d(n,k)−1)`, avoiding an expanded additive gamma tower.
Polynomial gamma arguments are canonicalized before integer-shift lowering, so
equivalent zero-shift bases cancel. Fraction reduction peels shared small
integer-linear factors, cancels a residual denominator cofactor only after exact
division succeeds on both sides, and can prove a remaining pair coprime over a
good finite field; inconclusive modular reductions still fall back to exact
rational GCD. Small interpolation systems first use `i128`, then a dimension-16
exact `BigRational` fallback; only solutions whose final coefficients fit the
public `i128` rational type are accepted.
The preferred Gosper certificate is the full
telescoping identity; if expanding a concrete gamma tower overflows, the exact
reduced polynomial Gosper equation certifies the same antidifference. The final
symbolic WZ check remains mandatory and unchanged.

Base-case gotcha: avoid `n` where a binomial hits the `Γ(0)` pole (e.g. `C(0,1)`)
— use `base ≥ 1` with a clean `k` range.

### Vandermonde is closed: `∑ₖ C(n,k)² = C(2n,n)`

`prove_wz_sum` now returns
`R(n,k)=k²(2k−3n−3)/(2(2n+1)(k−n−1)²)` and symbolically rechecks the WZ
telescoping identity. The earlier decline had three completeness causes: the
common `Γ(−k)^6Γ(k)^6k^m` monomial was not cancelled before the univariate gate,
the symbolic dispersion resultant overflowed even when its required shifted GCD
was small, and substituting into the already-formed normalized quotient expanded
large exact intermediates. Exact monomial-content cancellation, direct bounded
shifted-GCD scanning, and separately specializing/folding the summand and RHS
close those seams. The final WZ equality checker is unchanged; a false
`C(2n,n)+1` near-miss still declines.

### Adjacent convolution and squared moments are closed

The same public `prove_wz_sum` route now certifies:

- `∑ₖ C(n,k)C(n,k+1)=C(2n,n−1)`, with
  `R=k(k+1)(2k−3n−2)/(2(2n+1)(k−n)(k−n−1))`;
- `∑ₖ kC(n,k)²=(n/2)C(2n,n)`, with
  `R=k(k−1)((2n+1)k−(3n+1)(n+1))/(2n(2n+1)(k−n−1)²)`;
- `∑ₖ k²C(n,k)²=n³C(2n,n)/(2(2n−1))`, with
  `R=(k−1)²(2k−3n−2)/(2(2n−1)(k−n−1)²)`.

The first-moment coefficient `1/(2n)` exposed the old `Q(0)=1` interpolation
restriction; monic-denominator interpolation closes it. Its `n=5` concrete
Gosper sample also exposed coefficient growth in a degree-35 ratio with a
degree-31 common factor; pre-GCD content reduction, primitive-part Euclid, and
the exact reduced-equation certificate close that path. Every returned WZ
certificate still passes the fully symbolic identity, while `rhs+1` controls for
the new families decline.

### Fixed shift two and the third squared moment are closed

The next tier through the same public route is now:

- `∑ₖ C(n,k)C(n,k+2)=C(2n,n−2)`, with
  `R=k(k+2)(2k−3n−1)/(2(2n+1)(k−n−1)(k−n+1))`;
- `∑ₖ k³C(n,k)²=n³(n+1)C(2n,n)/(4(2n−1))`, with
  `R=(k−1)²(k²(2n²+3n−2)−k(3n³+8n²+3n−2)+3n(n+1)²)/(2k(n−1)(n+2)(2n−1)(k−n−1)²)`.

The third-moment `n=6` sample is the structured-difference regression: direct
Gosper expansion overflows, while the exact quotient identity recovers the
small consecutive ratio. Its degree-six coefficient fit also motivates the
eight-sample soft target. Returned certificates still receive the unchanged
fully symbolic WZ check, and both `rhs+1` controls decline.

### Fixed shift three and the fourth squared moment are closed

The next tier through the same public route is now:

- `∑ₖ C(n,k)C(n,k+3)=C(2n,n−3)`, with
  `R=k(k+3)(2k−3n)/(2(2n+1)(k−n−1)(k−n+2))`;
- `∑ₖ k⁴C(n,k)²=n³(n³+n²−3n−1)C(2n,n)/(4(2n−3)(2n−1))`.

The fourth moment is the regression for the strengthened exact-discovery path.
Symbolic ratio specialization avoids concrete factorial overflow after the
small samples; exact residual-cofactor cancellation reduces the `n=5` and
`n=7` quotients; and the bounded bignum linear solve permits the needed 5/5
rational coefficient fit without widening the public rational representation.
The then-current soft sample target was twelve. The recovered certificate still
passes the unchanged fully symbolic WZ equality, and both new `rhs+1` controls
decline.

### Fixed shift four and the fifth squared moment are closed

The next tier through the same public route is now:

- `∑ₖ C(n,k)C(n,k+4)=C(2n,n−4)`, with
  `R=k(k+4)(2k−3n+1)/(2(2n+1)(k−n−1)(k−n+3))`;
- `∑ₖ k⁵C(n,k)²=n⁴(n+1)(n²+2n−5)C(2n,n)/(8(2n−3)(2n−1))`.

The fifth moment exposed a remaining asymmetry in symbolic WZ preprocessing:
common canonical gamma atoms were cancelled from the RHS ratio, but not from
the inner `k` ratio or the summand's outer `n` ratio. Those two ratios were
therefore compact only through `n=12`; at `n=13`, concrete `Γ(n)` constants
reappeared and exact normalization declined. All three ratios now use the same
symbolic gamma-monomial cancellation before specialization. Sixteen samples are
needed to reject lower-degree rational interpolants and recover the fifth-moment
certificate, so the target and scan bounds are now 16 and 32. The existing
dimension-16 bignum cap is unchanged. The exact returned certificates and fully
symbolic WZ equality pass, while both `rhs+1` controls decline.

### The fixed-shift convolution is a checked family route

`prove_fixed_shift_binomial_convolution(shift)` now constructs

`R=k(k+r)(2k−3n+r−3)/(2(2n+1)(k−n−1)(k−n+r−1))`

for the requested concrete nonnegative `r`, then accepts it only after the same
fully symbolic WZ equality checker used by `prove_wz_sum` and the exact base
case at `n=r`. It does no interpolation and trusts no table. The shared checker
was extracted so discovery and direct-family candidates cannot drift. Regressions
cover `r=0..7` and reject a zero certificate; larger shifts may still decline on
exact coefficient growth. The public API therefore preserves `Option` semantics
rather than claiming an unbounded completeness result.

### Squared-binomial moments compose a directly checked falling-factorial family

`prove_squared_binomial_moment(moment)` generates the candidate identity

`∑ₖ k^m C(n,k)² = C(2n,n) ∑ⱼ S(m,j) (n)ⱼ²/(2n)ⱼ`

from the Stirling expansion `k^m=∑ⱼS(m,j)(k)ⱼ` and the falling-factorial
Vandermonde moment. `prove_squared_binomial_falling_moment(order)` constructs
the parameterized WZ candidate

`R=k(j−k)(jk−2j(n+1)−2k(n+1)+3(n+1)²)/((j−2n−2)(j−2n−1)(k−n−1)²)`

for `∑ₖ(k)ⱼC(n,k)²=(n)ⱼC(2n−j,n−j)` and accepts it only through the shared
fully symbolic WZ and exact base-case checker. The raw-moment prover composes
the nonzero certified falling-factorial members, checks
`k^m=∑ⱼS(m,j)(k)ⱼ` exactly, and checks their closed forms against the compact
factored result. `CertifiedSquaredBinomialMoment::is_certified()` independently
replays all three obligations; it does not trust the Stirling expansion or
component list.

`certifies_wz_sum` first checks the direct symbolic telescoping equation. If that
exact expansion returns `Unknown`, it now checks the algebraically equivalent
quotient equation
`R(n,k+1)f(n,k+1)/f(n,k)−R(n,k)=f(n+1,k)/f(n,k)−1`; consecutive gamma factors
cancel before polynomial expansion. A certified-false direct equation never
falls back. This exact product-aware route extends
`MAX_PROVED_SQUARED_BINOMIAL_FALLING_MOMENT` to 33. The order-15 outer ratio
initially remained too large because both sides simplified their exact
falling-factorial products before division. Product factors are now
polynomial-canonicalized and identical factors cancelled before gamma/rational
normalization. Order 16 then exposed a separate concrete-base artifact:
normalizing the whole `(16)₁₆(16!/16!)²` term overflowed before the quotient
cancelled. Fully substituted terms and RHSs now use the existing exact rational
evaluator first, retaining the older normalizer as a fail-closed fallback.
Orders 16 through 18 pass. Order 19 then exposed equal Gamma atoms and
polynomial factors buried inside nested divisions after Gamma lowering. The
old preprocessor inspected only the top-level numerator and denominator, so the
remaining exact products expanded into degree-36 polynomials. It now recursively
collects factors across multiplication and division, reverses sides through a
divisor, canonicalizes each polynomial factor and Gamma argument, and cancels
only structurally equal pairs. The resulting quadratic quotient first carried
the unchanged symbolic equality gate through order 33.

The exact finite-base checker now retains that checked-`i128` route first and
falls back only from `Unknown` to a private `BigRational` evaluator for the
fully concrete rational/positive-integer-Gamma fragment. It has explicit caps
at Gamma argument 256 and power 1024; variables, other unary heads, poles, and
larger operations decline. A certified-false symbolic or base result never
falls back. Product leading scalars also accumulate in `BigRational` before one
mandatory conversion of the final scalar to public `Rational`, and the bounded
Gamma-shift span is 256. These exact changes remove the former `34!`, `2^127`,
and 129-shift representation limits. The direct family certifies every order
through 255. Order 256 still passes the compact symbolic quotient identity,
then declines exactly because its base needs `Γ(257)`, outside the declared
resource fragment.

The raw compositor no longer expands every Stirling term over the full known
common denominator `(2n)ₘ`. Before expansion, it removes every even factor
`2n−2r`: either the matching complement factor is present, or one copy of
`n−r` is removed from `(n)ⱼ²` and its scalar `2` is recorded. Each reduced term
therefore retains only the odd common-denominator factors. Dense polynomial
products and accumulation use exact `BigRational` intermediates, but the
candidate declines unless every final coefficient converts back to the public
checked-`i128` `Rational` representation. The prior exact odd-factor division,
monic normalization, and compact residual factorization remain mandatory.

The composite checker still replays every component WZ proof and independently
certifies `k^m=ΣⱼS(m,j)(k)ⱼ`, now with exact bignum polynomial intermediates.
Before expanding a central-binomial quotient, it lowers Gamma shifts, expands
only bounded positive product powers, extracts exact polynomial leading
scalars, makes factors monic, cancels structurally identical factors, and sorts
the remaining factor lists deterministically. Structural equality closes the
large but already factored cases; otherwise the prior exact monic
numerator/denominator comparison remains the fail-closed fallback. Monic
coefficient division now likewise uses bignum intermediates but accepts only
final checked-`i128` values. This route extends
`MAX_PROVED_SQUARED_BINOMIAL_MOMENT` to 35. Regressions cover raw orders
`0..=35`, exact direct-sum samples, the explicit compact order-11 form,
pre-cancelled-term reconstruction, factor canonicalization, and tampered
results, certificates, missing components, and the ceiling. Raw order 36 is the
first measured decline: its exact monic numerator has coefficients beyond the
public `i128` rational domain. The independent concrete-sum control evaluates
every high raw order at `n=8` with `BigInt` direct arithmetic and the bounded
exact concrete evaluator, avoiding the small equality checker's intermediate
domain without weakening the sample.
The foundational DAG and research-question register require no new ADR here:
this adds no IR operator or backend semantics and keeps evidence explicit and
checker-backed.

### Strict rustdoc is green again

`RUSTDOCFLAGS="-D warnings" cargo doc -p axeyum-cas --no-deps` now passes on
both stable and the local nightly. The failures were pre-existing documentation
links outside the moment code: an unescaped `𝔽ₚ[x]`, public docs linking private
helpers, one unqualified crate-level link, and redundant explicit link targets.
The cleanup changes documentation markup only; no API or implementation
semantics changed.

---

## 6. Known-open items / candidate next work

Ordered roughly by value:

1. **Resume broad, timeout-bounded gap probing.** Direct order-one and weighted
   Bessel antiderivatives through order 32 are closed through the normal
   certificate path; order 33 is the explicit discovery boundary. Rational-scale
   integer-order Bessel-J improper integrals on `[0,∞)` and nonconstant
   rational-polynomial integer-order Bessel-J limits at both real infinities
   are also closed. The moment families retain separate explicit resource
   boundaries:
   direct order 256 needs `Γ(257)`, raw order 36 needs public coefficients beyond
   `i128`, and repeated-quadratic inverse Laplace multiplicity 8 exceeds
   checked-`i128` normalization at `t⁷cos(βt)`. Extending these requires a
   deliberate resource/data-model decision rather than another local
   cancellation. Fixed-shift `r=8` remains a focused exact-growth candidate if
   a concrete use needs it.
2. **Higher-order inverse Bessel boundary.** Forward `Jₙ` and `Iₙ` are exact
   for every public order, while inverse recognition is explicitly bounded to
   `0≤n≤32`. Order 33 and `u32::MAX` decline promptly. Raising that boundary
   requires an explicit resource justification and must retain the mandatory
   complete forward round trip; do not infer unbounded inverse support from the
   forward tables alone.
3. **Alternating series** `∑(−1)ᵏ/k = −ln2`, `∑(−1)ᵏ/(2k+1)=π/4−…`, Dirichlet
   eta `η(s)`. **Blocked by the data model**: `(−1)ᵏ` has no clean real
   representation (`geometric_power(−1)` = `exp(k·ln(−1))`, complex `ln`). Would
   need a dedicated alternating-sign representation or a complex extension.
4. **Continue gap-probing** — still productive. Areas not yet swept much:
   Fourier and additional inverse-transform families, 2nd-order variable-coeff
   ODEs, PDE separation, richer assumptions/piecewise behavior, elliptic
   integrals, and `bessely`/`besselk` (second-kind / modified-second-kind, via
   the proven indexed Bessel-head pattern but requiring log-singular numerics).
5. **Minor display nits** (value-correct, cosmetic): denominator rationalization
   `1/√3→√3/3` (doesn't fit the size-gated simplify cleanly); `L{t·eᵗ}` shows
   `−(−1/(s−1)²)` for some internal structures (the manually-built structure folds
   fine — a subtle structural mismatch worth 20 min if it bugs you).
6. **One-sided limits** (`lim_{x→0⁺} √x·ln x = 0`) — the limit API is two-sided;
   `√x` isn't defined for `x<0` so the two-sided limit legitimately declines.

---

## 7. Architecture pointers (where things live)

All in `crates/axeyum-cas/src/`:
- `lib.rs` — the bulk: `CasExpr`/`UnaryFunc` enums, `equal` (zero-test) +
  `canonicalize_for_equality`, `simplify` (a size-gated candidate search —
  **add value-preserving transforms as candidates**), `integrate` (a flat list of
  ~40 certified finders — add new integration methods here), `limit`, `solve`,
  `dsolve_*`, transforms, `prove_wz_sum`, `combine_gamma_ratios`/`fold_gamma`.
- `gosper.rs` — Gosper's algorithm (rational + geometric + factorial-via-gammasimp).
- `series.rs` — Taylor/Laurent/Puiseux; `unary_series` per-head dispatch.
- `orthopoly.rs`, `ntheory*.rs`, `combinatorics.rs`, `matrix.rs`, `mvpoly.rs`,
  `approx.rs`, `ratint.rs`, `special.rs`, `boolean.rs`, `sets.rs`, `interval_arith.rs`.

Design invariants (hold the line):
- **Proof-carrying / sound.** Every result is certified (differentiate-and-check
  for integrals; the decidable zero-test with witness for equalities; symbolic WZ
  verification for sums). Out-of-fragment cases **DECLINE (`None`)**, never return
  a wrong answer. Never trade soundness for a numeric-only "answer".
- `simplify` candidates must be **value-preserving** and are **size-gated** (only
  chosen when strictly smaller) — so adding one can't break a caller's form.
- New integration finders that recurse into `integrate` need a **termination
  guard** (see `has_odd_trig_power`, the `√u`/`ln u` guards) — this class of bug
  hangs the whole engine and can pass the test suite undetected. Always
  timeout-stress new recursive finders on adjacent inputs.
- Rust: `Result<T,E>`+`?` over `.unwrap()`; `///`/`//!` docs on public items;
  keep it `wasm32-unknown-unknown`-safe (no `std::time`, no filesystem in the
  core); `Date.now()`/`Math.random()` equivalents are unavailable.

---

## 8. Resume checklist

```bash
cd /nas4/data/workspace-infosec/claude-axeyum-cas-work
AXEYUM_CAS_TMP="$(mktemp -d /nas4/data/tmp/axeyum-cas-full.XXXXXX)"
case "$AXEYUM_CAS_TMP" in
  /nas4/data/tmp/axeyum-cas-full.*) ;;
  *) exit 2 ;;
esac
export AXEYUM_CAS_TMP
trap 'find "$AXEYUM_CAS_TMP" -depth -delete' EXIT
git rev-parse --abbrev-ref HEAD        # → agent/cas/...
git merge-base --is-ancestor 3a361b0a HEAD
CARGO_BUILD_JOBS=1 TMPDIR="$AXEYUM_CAS_TMP" cargo test -p axeyum-cas --jobs 1
# → 554 unit + 147 doctests green
```
Then: read `docs/research/10-cas/diary.md` tail for the latest context, and pick
up from §6 or resume the gap-probing loop. Push the green owned topic branch;
sync README count + diary each time.

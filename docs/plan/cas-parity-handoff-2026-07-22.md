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
  branch, and leave `main` to the integration owner.
- **Tests:** `520` unit + `147` doctests, **all green**, clippy-clean, wasm-green.
- **Source of truth for capabilities:** `docs/research/10-cas/README.md`
  (capability table) and `docs/research/10-cas/diary.md` (chronological entries;
  latest is **Entry 37adn**). Keep both in sync when landing features.
- **Method that works:** empirical **gap-probing** (below). It found every recent
  feature *and* a serious infinite-hang regression.

---

## 2. How to build / test / iterate (READ THIS — there are gotchas)

Everything runs in the axeyum worktree:
`/nas4/data/workspace-infosec/claude-axeyum-cas-work`.

```bash
# The full gate before any commit:
cargo test  -p axeyum-cas          # unit + doctests
cargo clippy -p axeyum-cas --all-targets
cargo build -p axeyum-cas --target wasm32-unknown-unknown   # must stay wasm-safe
```

### Critical gotcha: `TMPDIR`
The tmpfs `/tmp` hits **"Disk quota exceeded"** when the ~147 doctests link
concurrently. **Always** point `TMPDIR` at a roomy disk:

```bash
AXEYUM_CAS_TMP="$(mktemp -d /nas4/data/workspace-infosec/axeyum-cas-doctmp.XXXXXX)"
export AXEYUM_CAS_TMP
TMPDIR="$AXEYUM_CAS_TMP" cargo test -p axeyum-cas          # etc.
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
`r=0..7`), and a generated squared-binomial raw-moment family (regressed for
orders `0..=5`). False near-misses correctly decline.

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

### Squared-binomial moments are now a generated checked family

`prove_squared_binomial_moment(moment)` generates the candidate identity

`∑ₖ k^m C(n,k)² = C(2n,n) ∑ⱼ S(m,j) (n)ⱼ²/(2n)ⱼ`

from the Stirling expansion `k^m=∑ⱼS(m,j)(k)ⱼ` and the falling-factorial
Vandermonde moment. It reduces the rational factor exactly, makes its numerator
and denominator monic before factoring to keep coefficients bounded, and then
passes the resulting candidate through `prove_wz_sum`. A returned
`CertifiedSquaredBinomialMoment` carries the order, closed form, and rational WZ
certificate; `is_certified()` independently reruns the fully symbolic WZ and
exact base-case checks over that payload.

`MAX_PROVED_SQUARED_BINOMIAL_MOMENT=5` makes that resource boundary explicit
and rejects larger requests before candidate generation. Regressions cover
orders `0..=5`, compare every generated member with a direct
finite sum, recover the known compact fifth-moment identity, and reject both a
tampered closed form and a zero certificate. An exploratory order-six request
did not pass bounded WZ discovery, so the public contract remains fail-closed
rather than claiming completeness for every `u32` order.
The foundational DAG and research-question register require no new ADR here:
this adds no IR operator or backend semantics and keeps evidence explicit and
checker-backed.

---

## 6. Known-open items / candidate next work

Ordered roughly by value:

1. **Broaden certified creative telescoping beyond the two checked families.**
   Investigate why order six exceeds the bounded WZ discovery path and whether
   a direct falling-factorial certificate composition can avoid interpolation;
   keep the fully symbolic checker boundary unchanged. For fixed shifts,
   investigate the `r=8` exact-growth decline only if a concrete use needs it.
2. **Alternating series** `∑(−1)ᵏ/k = −ln2`, `∑(−1)ᵏ/(2k+1)=π/4−…`, Dirichlet
   eta `η(s)`. **Blocked by the data model**: `(−1)ᵏ` has no clean real
   representation (`geometric_power(−1)` = `exp(k·ln(−1))`, complex `ln`). Would
   need a dedicated alternating-sign representation or a complex extension.
3. **Continue gap-probing** — still productive. Areas not yet swept much:
   more transforms (Z-transform edge cases, Fourier), 2nd-order variable-coeff
   ODEs, PDE separation, vector calculus (grad/div/curl), assumptions/`refine`,
   piecewise, elliptic integrals, `bessely`/`besselk` (second-kind / modified-2nd,
   via the proven `UnaryFunc::BesselI(u32)` parameterize-the-variant technique
   but they need log-singular numerics).
4. **Minor display nits** (value-correct, cosmetic): denominator rationalization
   `1/√3→√3/3` (doesn't fit the size-gated simplify cleanly); `L{t·eᵗ}` shows
   `−(−1/(s−1)²)` for some internal structures (the manually-built structure folds
   fine — a subtle structural mismatch worth 20 min if it bugs you).
5. **One-sided limits** (`lim_{x→0⁺} √x·ln x = 0`) — the limit API is two-sided;
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
AXEYUM_CAS_TMP="$(mktemp -d /nas4/data/workspace-infosec/axeyum-cas-doctmp.XXXXXX)"
export AXEYUM_CAS_TMP
git rev-parse --abbrev-ref HEAD        # → agent/cas/...
git merge-base --is-ancestor origin/main HEAD
TMPDIR="$AXEYUM_CAS_TMP" cargo test -p axeyum-cas   # → 520 + 147 green
```
Then: read `docs/research/10-cas/diary.md` tail for the latest context, and pick
up from §6 or resume the gap-probing loop. Push the green owned topic branch;
sync README count + diary each time.

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
- **Tests:** `504` unit + `147` doctests, **all green**, clippy-clean, wasm-green.
- **Source of truth for capabilities:** `docs/research/10-cas/README.md`
  (capability table) and `docs/research/10-cas/diary.md` (chronological entries;
  latest is **Entry 37adh**). Keep both in sync when landing features.
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
export AXEYUM_CAS_TMP="$PWD/.tmp/cas-doctmp"
mkdir -p "$AXEYUM_CAS_TMP"
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

The marquee arc, roughly in order (all on `main`):

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
`∑ₖ C(n,k)=2ⁿ`, `∑ₖ k·C(n,k)=n·2ⁿ⁻¹`, `∑ₖ k²·C(n,k)=n(n+1)2ⁿ⁻²`. A false
identity (`∑C(n,k)=3ⁿ`) correctly declines.

---

## 5. Zeilberger / WZ — how it works and where to extend

`prove_wz_sum(summand, n, k, rhs, base, k_lo, k_hi) -> Option<CasExpr>`
(returns the certificate `R(n,k)` iff proven). File: `crates/axeyum-cas/src/lib.rs`.

Pipeline:
1. `f = F/rhs`. The WZ pair: a rational certificate `R(n,k)` gives
   `f(n+1,k) − f(n,k) = G(n,k+1) − G(n,k)` with `G = R·f`; summing over `k`
   collapses the RHS to 0, so `S(n)=∑ₖ f` is constant, pinned to 1 by the base.
2. **Discovery (heuristic):** run the factorial-capable `gosper_sum` on the WZ
   term at several *small* concrete `n` (sample from `n=1,2,3,…` — larger `n`
   overflow the rising factorials), extract `R(nᵢ,k)`, monic-normalize the
   denominator, and interpolate each coefficient over `n` with
   `rational_interpolate` (lowest-degree `P(n)/Q(n)`, validated — subsumes
   Lagrange, needed because e.g. `k²·C(n,k)` certificates have `(n+1)/(n+2)`-type
   coefficients).
3. **Soundness gate (symbolic):** verify `equal(G(n,k+1)−G(n,k),
   f(n+1,k)−f(n,k))` with `n,k` both symbolic. A wrong/under-fit interpolation
   fails here and the prover declines. This leans on gammasimp + the atom-ordering
   fix.

Enabling Gosper fixes: `reduce_fraction` divides out the common
integer **content** (binomial ratios carry a huge content that overflowed the
dispersion machinery); `nonneg_integer_dispersion` now scans `j=0..64` by direct
shifted polynomial GCD instead of materializing an overflow-prone symbolic
resultant; and consecutive-ratio extraction cancels exact common monomial content
before requiring a univariate ratio.

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

---

## 6. Known-open items / candidate next work

Ordered roughly by value:

1. **Broaden certified creative telescoping beyond Vandermonde.** Probe the
   adjacent-binomial convolution `∑C(n,k)C(n,k+1)=C(2n,n−1)` and weighted
   squared-binomial moments; retain only identities whose concrete discovery and
   fully symbolic WZ check both close.
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
export AXEYUM_CAS_TMP="$PWD/.tmp/cas-doctmp"; mkdir -p "$AXEYUM_CAS_TMP"
git rev-parse --abbrev-ref HEAD        # → agent/cas/...
git merge-base --is-ancestor origin/main HEAD
TMPDIR="$AXEYUM_CAS_TMP" cargo test -p axeyum-cas   # → 504 + 147 green
```
Then: read `docs/research/10-cas/diary.md` tail for the latest context, and pick
up from §6 or resume the gap-probing loop. Push the green owned topic branch;
sync README count + diary each time.

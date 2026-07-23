# CAS initiative — research & build diary

A running, append-only log of research, decisions, prototypes, and references for
the [CAS initiative](README.md). Newest entries at the bottom of each day.

---

## 2026-07-20 — Entry 1: kickoff, framing, substrate survey

### Goal (as set)
Build the compute-side functionality of SymPy / Mathematica in axeyum — carefully,
comprehensively, patiently: research → design → prototype → document, keeping this
diary as we go.

### Orientation (docs read)
- `docs/research/README.md`, `00-orientation/*` (north star: general reasoning /
  logic / proving; untrusted search / trusted checking).
- `08-planning/`: `roadmap.md` (foundation phases 0–7 landed; parity plan in
  PLAN.md), `capability-matrix.md` (certified DRAT/Alethe/Lean procedures across
  BV/UF/LIA/LRA/NRA/NIA/FP/arrays/datatypes/quantifiers),
  `formal-mathematics-tour.md` (backward-derived math DAG + per-node decidable
  fragment; already contemplates "symbolic-derivative-rule checks"),
  `foundational-example-suites.md` (decidability lens; `unknown` first-class;
  double-duty artifacts; oracle-free ground truth per ADR-0008),
  `foundational-dag.md` (every layer needs semantics + checker + replay before it
  is public).

### Framing settled
The Pareto-dominant, honest target is a **proof-carrying CAS**: compute
`transform(expr)` and, wherever the fragment is decidable, return a checkable
witness that the transform is denotation-preserving; label everything else
`computed-uncertified`. This is axeyum's identity applied to algebra and the
compute-side realization of the destinations `formal-mathematics-tour.md` already
maps (number theory, linear algebra, calculus). Not "reimplement Mathematica" —
"be the CAS that certifies which of its answers are proven." Written up in
[README.md](README.md).

### Substrate survey (sub-agent, read-only) → [substrate-map.md](substrate-map.md)
**Already built (the hard half):** hash-consed typed term DAG = the `head[args]`
model; exact univariate rational polynomial algebra (`poly.rs`: derivative, rem,
GCD, exact div, squarefree, resultants/Sylvester, Sturm chains, exact real-root
counting); real-algebraic numbers with field arithmetic (`real_algebraic.rs`,
deg ≤ 24); ground evaluator over all sorts (`eval.rs`); a fixed ~60-rule
denotation-preserving canonicalizer (`axeyum-rewrite/canonical.rs`);
congruence-closure e-graph with e-matching + proof explanations (`axeyum-egraph`).

**Missing (the compute side to build):** symbolic differentiation *over terms*;
symbolic simplification *returning a term* (expand/collect/factor/normal form);
multivariate polynomials + Gröbner; univariate factorization (Berlekamp/
Zassenhaus/LLL) + partial fractions; a general rewrite/equality-saturation engine
(the e-graph matches but never applies rules or extracts); **transcendental
function operators** (exp/log/sin/cos/sqrt as heads — the IR has none);
integration/summation/limits/series/equation-solving; public symbolic linear
algebra; a substitution/match-and-rewrite API.

### Key architectural finding
The solver IR deliberately has **no transcendental heads** and is confined to
decidable theories. So the CAS should be a **new `axeyum-cas` layer** carrying the
broad (partly-undecidable) surface, which **lowers to the decidable IR core**
(poly/RCF/SMT/`real_algebraic`) exactly where certification happens — *broad
algebra, narrow certifier*. Proposed as option (B) in
[substrate-map.md](substrate-map.md#architectural-implication); to be ratified in
the initiative's first ADR. This keeps the solver core clean and makes the
decidability boundary an explicit lowering boundary.

### The first thin vertical slice (proposed)
Per ADR-0001 (thin slice first) and the decidable-first rule: the **certified
polynomial kernel** — `canonicalize`, `differentiate`, and **decidable
`equal?`** (polynomial zero-testing) over the rational-function fragment, lowered
to the IR and certified via `poly.rs` + NRA. This directly answers the user's own
exemplar "check `D[x²+c] = 2x`": compute `D[x²+c] = 2x + 0`, then *decide*
`2x + 0 ≡ 2x` by zero-testing `(2x+0) − 2x = 0`. It is simultaneously compute-side
(returns a new expression) and fully certifiable (polynomial zero-testing is
decidable; exact rational arithmetic and RCF are already in-tree). Design to
follow in [build-plan.md](build-plan.md) after the architecture + decidability
docs land.

### Pending (sub-agents in flight)
- Oracle/harness survey (`axeyum-scenarios` `self_check` mechanism; curriculum
  DAG; is the corpus a non-circular oracle?) → feeds the "test harness for a CAS"
  claim with exact mechanism.
- CAS architecture web research (SymPy/Mathematica/Symbolica internals; capability
  taxonomy; the decidability boundary incl. Richardson's theorem & Risch) → feeds
  [cas-architecture-survey.md](cas-architecture-survey.md) and
  [decidability-map.md](decidability-map.md).

### Next actions
1. On oracle survey: write the harness/oracle section of the vision + confirm the
   self-check mechanism.
2. On web research: write `cas-architecture-survey.md` + `decidability-map.md`.
3. Then `gap-analysis.md`, `vision.md`, `build-plan.md`, and the first-slice ADR.
4. Then prototype the certified polynomial kernel, TDD, decidable-first.

### References gathered so far
- Existing in-tree docs linked above.
- (Web references to be added by the architecture-research sub-agent.)

---

## 2026-07-20 — Entry 2: design set + first slice shipped & verified

### Recon complete (3 sub-agents)
- **Substrate** → [substrate-map.md](substrate-map.md). Confirmed: `head[args]`
  DAG, exact univariate poly algebra, real-algebraic numbers, canonicalizer,
  e-graph. Missing: differentiation-over-terms, transcendental heads,
  multivariate polys, factorization, integration, general rewrite/saturation.
- **Oracle/harness** → [oracle-as-test-harness.md](oracle-as-test-harness.md).
  Confirmed the corpus is a **non-circular** oracle: `Scenario::self_check`
  (`lib.rs:349`) trusts only `eval`; exhaustive enumeration ≤20 bits is a real
  finite-domain UNSAT proof; ~165 instances / 83 generators / 23 families /
  23-node decidability-tagged curriculum DAG; **zero compute-shaped functions** —
  a pure test harness for a CAS, exactly as claimed.
- **CAS architecture (web)** → [cas-architecture-survey.md](cas-architecture-survey.md).
  SymPy (`args` invariant, `polys` domain tower, portfolio `integrate`), Wolfram
  (uniform `head[args]` rewriting + `Flat`/`Orderless`), Symbolica (proprietary;
  MIT `numerica`/`graphica` spin-outs), the algorithm/decidability taxonomy, and
  Richardson/Risch as the load-bearing bounds. **Opening confirmed:** no
  permissively-licensed Rust CAS, and *no CAS in any language* makes per-answer
  trust machine-checkable — axeyum's differentiator.

### Design docs written
`vision.md`, `decidability-map.md`, `gap-analysis.md` (16 build units G0–G16),
`build-plan.md` (phases C0–C7, decidable-first, evidence-gated), and
**ADR-0301** (ratifies the `axeyum-cas` layer + reduce-to-decide certifier;
rejects extending the IR with transcendental heads and rejects external-CAS
oracle laundering).

### Phase C0 shipped — the certified polynomial kernel (TDD, verified)
New crate **`crates/axeyum-cas`** (leaf; depends only on `axeyum-ir`; no solver
dep; pure Rust). Implements over the polynomial fragment:
- `CasExpr` + `differentiate` (sum/product/power rules on the tree);
- `MultiPoly` — canonical multivariate sparse-polynomial normal form (this is
  also a head start on **G3**, the polynomial tower);
- `normalize` (expand to `MultiPoly`), `equal` (decidable zero-test returning a
  trust-tagged `ZeroTest` whose `witness` is the re-checkable difference poly),
  `prove_derivative`.

**Certification is oracle-free**: the canonical form *is* the certificate; exact
`Rational` arithmetic throughout; overflow → honest `ZeroTest::Unknown`, never a
wrong answer.

**Verification (all green):**
- 11 unit tests + 1 doctest pass. Includes the exemplar **`D[x²+c] = 2x`
  certified**; product/power/multivariate partial derivatives; rational
  coefficients exact.
- **Independent cross-check**: symbolic `differentiate` agrees exactly with the
  trusted numeric `poly::rat_derivative` on univariate polynomials.
- **Self-check in the `axeyum-scenarios` spirit**: `normalize` preserves value at
  sample points under the trusted evaluator; certified-equal agrees with
  evaluation; overflow declines to `Unknown`.
- `cargo clippy -p axeyum-cas --all-targets` — **clean** (pedantic).
- `cargo build -p axeyum-cas --target wasm32-unknown-unknown` — **succeeds**
  (WASM-green).

### Honest status of the C0 exit gate
Met: differentiate/equal correct + certified; exemplar certified; `poly.rs`
cross-check; clippy + wasm green. **Not yet done (deliberately deferred, not
faked):** the *formal* double-duty self-checking scenario in `axeyum-scenarios`.
That corpus is verification-shaped (asserts a `Query`, self-checks via `eval`
over BV); turning a *compute-transform* certificate into that shape is a real
design question (how a computed transform becomes a self-checking scenario),
worth its own careful slice — tracked as the next step, not claimed complete.

### Next actions
1. **C0.1** — design how a certified compute-transform lands as a double-duty
   self-checking scenario (bridge the poly-normal-form certificate into the
   `Scenario`/`Family` machinery), closing the last C0 gate.
2. **C1 start** — extend the kernel to **rational functions**: `Div` + quotient
   rule; zero-test of `p/q` via numerator (still fully decidable/certified);
   then subresultant multivariate GCD to reduce `MultiPoly` fractions.
3. Add a QF_NRA test-only differential cross-check (via `axeyum-solver` as a
   dev-dependency) as a second independent certifier for the rational fragment.

---

## 2026-07-20 — Entry 3: C1 rational functions green; `expand` added

### C1 — rational-function fragment (verified)
Extended `axeyum-cas` with `CasExpr::Div`, the **quotient rule**, a `RatFunc`
(num/den) normal form, and rational-function `equal` by **cross-multiplication**
(`a/b = c/d` iff `a·d − c·b ≡ 0`; denominators non-zero by construction, so no
GCD reduction is needed to *decide* equality). Division by an identically-zero
denominator → honest `Unknown`.

**Verified:** `cargo test -p axeyum-cas` → **15 passed / 0 failed** (+ doctest),
`cargo clippy --all-targets` clean, `wasm32` build green. New tests: quotient
rule `d/dx(1/x)=-1/x²` and `d/dx(x/(x+1))=1/(x+1)²` (the latter also confirmed by
the trusted evaluator at sample points), cancellation equality
**`(x²−1)/(x−1)=x+1` certified without a GCD**, and division-by-zero→`Unknown`.

### `expand` — return the canonical expression, not just a yes/no
Added `MultiPoly::to_expr` and `expand(expr) -> Option<CasExpr>`: the compute
transform now hands back the actual expanded/canonical expression (core CAS
ergonomics — "give me the simplified form"), certified value-equal to the input
by round-trip (`equal(expand(e), e)` is proven). Tests: `expand((x+1)³) =
x³+3x²+3x+1` (and certified equal to the original); rational `expand`
value-preserving. **Verified:** `cargo test -p axeyum-cas` → **17 passed / 0
failed** (+ doctest), clippy clean.

### Interaction note
The developer is concurrently running `cargo test --workspace --all-features`,
which now also compiles/tests the new `axeyum-cas` crate — the initiative is
integrated into the workspace test from the first commit.

### `cancel` — reduce to lowest terms (univariate GCD), verified
Added `RatFunc::reduced` (univariate case) reusing the in-tree exact
`poly::rat_gcd` + `poly::rat_exact_div`, with denominator-sign canonicalization,
and the public `cancel(expr) -> Option<CasExpr>`. Multivariate functions are left
expanded-but-unreduced (still value-equal) pending multivariate GCD (G4).

**Verified:** `cargo test -p axeyum-cas` → **20 passed / 0 failed** (+ doctest),
clippy `--all-targets` clean, `wasm32` build green. Tests: `(x²−1)/(x−1) → x+1`
(fully cancels to a polynomial), `(2x²+2x)/(x+1) → 2x`, and value-preservation
`(x²−4)/(x−2) = x+2` confirmed by the trusted evaluator at four points.

### Kernel state after this session
`axeyum-cas` now offers, over polynomials **and** rational functions, all
certified / oracle-free / WASM-safe: **`differentiate`** (sum/product/quotient/
power), **`normalize`** (canonical multivariate polynomial), **`equal`**
(decidable zero-test with re-checkable witness), **`expand`**, **`cancel`**
(univariate lowest-terms). 20 tests + doctest, clippy-clean. This realizes the
Phase C0 slice and most of C1; it is the working seed of the certified core.

### Next
- **Multivariate GCD** (G4, subresultant PRS / content-primitive) → full
  `cancel`/canonical reduced form for the multivariate case; gateway to `factor`
  (G5) and partial fractions → **certified rational integration** (G11, the
  flagship differentiate-and-check demo).
- **C0.1** scenario bridge (double-duty artifact in `axeyum-scenarios`).
- **QF_NRA** second, independent certifier (test-only, via `axeyum-solver`
  dev-dependency).
- A `Display` for `CasExpr` for human-readable output.

---

## 2026-07-20 — Entry 4: curriculum coverage correction (+ parallel-build setup)

### Prompt
"Did you plan/envision the *entire* curriculum — number theory, real & complex
analysis, geometry, differential & integral calculus, linear algebra,
differential equations?"

### Honest finding: the first plan was incomplete
I planned the certified polynomial/analysis/linear-algebra/number-theory core
well and tied the vision to `formal-mathematics-tour.md`, but I did **not** map
the build units node-by-node onto the actual 23-node curriculum, and I omitted:
- **complex analysis** — the `complex` node (lean-horizon, "NRA over pairs") had
  **no** CAS unit;
- **differential equations** — not a curriculum node, and absent from my plan
  entirely (a core SymPy capability);
- **geometry** — only implicit via NRA; never called out.

### Fix → [curriculum-coverage.md](curriculum-coverage.md)
Read the authoritative `docs/curriculum/curriculum.toml` (23 nodes, 4 layers) and
wrote a full node-by-node map: each node → the CAS capability that makes it
computational + its trust ceiling, under the unifying frame **"each node's
`decidability` tag is the CAS's trust ceiling for that node."** Added build units
**G17 (complex numbers/ℚ(i)/complex-algebraic)** and **G18 (differential
equations)** to `gap-analysis.md`, plus **C4b/C6b** phases and a geometry-suite
note to `build-plan.md`. The lean-horizon nodes (cardinality, complex-*analysis*,
sequences-and-limits, calculus-foundations) are honestly the decidable-fragment +
Lean-reconstruction split, never false claims.

Key reframe recorded: **ODE solving is proof-carrying exactly like integration** —
substitute the candidate solution into the ODE and zero-test the residual; linear
constant-coefficient ODEs are decidable via the characteristic polynomial (reuses
factorization G5).

### Parallel-build setup (with the other agent)
Confirmed clean isolation: all CAS work is a new crate + new docs (only 2 shared
one-line diffs), on shared branch `main`. To avoid cargo build-lock contention
with the other agent's `cargo test --workspace`, my builds now use a **separate
`CARGO_TARGET_DIR=/nas4/data/workspace-infosec/claude-axeyum-cas-target`**
(verified: 5.4s cold, contention-free thereafter; 20 tests pass there).

---

## 2026-07-20 — Entry 5: certified integration flagship (polynomial slice)

Goal refined to: follow the `10-cas/` docs, always reasoning backwards from
**axeyum = (Lean/Z3/cvc5 decide+prove) + (Mathematica/SymPy compute)**.

### The flagship, in its first fully-decidable slice
Brought the C6 flagship forward in its polynomial slice — the clearest embodiment
of the thesis: **`integrate` computes an antiderivative and returns it bundled
with a proof of its own correctness** (`CertifiedIntegral { antiderivative,
certificate }`). The certificate is produced by *differentiating the answer and
zero-testing it against the integrand* — reusing C0's `differentiate` + `equal`.
So the compute step is SymPy-shaped and the certify step is Lean/Z3-shaped, in one
call. Justified as decidable-first: polynomial integration is fully decidable and
always certifiable.

`integrate_in` on `MultiPoly` (∫ term-by-term, exact rational coeffs, drops `+C`),
`CertifiedIntegral` + `is_certified()`, public `integrate(expr,var)`.

**Verified** (isolated target dir, no contention): `cargo test -p axeyum-cas` →
**25 passed / 0 failed** (+ doctests), clippy `--all-targets` clean, wasm green.
Tests: `∫(3x²+2x)=x³+x²` certified; `∫x⁴=(1/5)x⁵` (exact rational); multivariate
`∫(xy+y²)dx=(1/2)x²y+y²x` (other vars as constants); fundamental-theorem roundtrip
`d/dx ∫f dx = f` over a batch; **honest decline** (`None`) on non-polynomial input
(rational integration is the next slice). A doctest shows the proof-carrying loop.

### In flight (parallel research)
Launched a research sub-agent (sonnet) on **univariate rational-function
integration** (Hermite reduction rational part + Rothstein–Trager log part) mapped
onto the in-tree `poly` primitives, focused on the certification angle (Hermite
part → pure rational zero-test; log part → the minimal zero-test extension). Feeds
the next slice: extend `integrate` to `Div` inputs, still certified by
differentiate-and-check.

### Display + runnable demo (shipped, +1 test → 26)
Added a precedence-aware `Display` for `CasExpr` (SymPy-like infix output) and a
runnable example `examples/certified_calculus.rs`
(`cargo run -p axeyum-cas --example certified_calculus`). Output:
```
d/dx (x^2 + c) = 2*x   [= 2*x, CERTIFIED]
∫ (3*x^2 + 2*x) dx = x^2 + x^3   [CERTIFIED by differentiate-and-check]
expand((x + 1)^3) = 1 + 3*x + 3*x^2 + x^3
cancel((x^2 - 1)/(x - 1)) = 1 + x
```
26 tests + 2 doctests, clippy `--all-targets` clean (incl. example), wasm green.
(Monomial print order is ascending-degree from the `BTreeMap`; a descending/
SymPy-style order is a cosmetic follow-up.)

### Also shipped this session: `substitute` (G0 foundational)
Added `CasExpr::substitute(var, replacement)` (composition / change-of-variables /
solution-checking) — the substitution API the gap analysis flagged missing in G0.
Structural, denotation-preserving. Tests: `x²[x:=(y+1)] = y²+2y+1`; root check
`(x²−2x+1)[x:=1] = 0`. **28 tests + 2 doctests, clippy `--all-targets` clean,
wasm green**, canonical descending-degree output, runnable demo.

### Next
- Implement rational-function integration (Hermite reduction first — the rational
  part is certified by a rational-function zero-test I already have); **awaiting
  the research sub-agent's algorithm design note** (it maps Hermite/Rothstein–
  Trager onto the in-tree `poly` primitives and flags the new primitives needed:
  extended-Euclid cofactors, full squarefree factorization). Holding on this
  rather than rushing a subtle algorithm from memory.
- Then univariate factorization (C2/G5) and multivariate GCD (G4) for breadth.

### Session tally (public API of `axeyum-cas` so far)
`CasExpr` (+ `Display`, arithmetic ops), `differentiate`, `substitute`,
`normalize`/`MultiPoly` (canonical form + `to_expr`/`to_univariate`), `equal`
(decidable zero-test, `ZeroTest` witness), `expand`, `cancel`, `integrate`
(`CertifiedIntegral`), `prove_derivative`. All certified/oracle-free/WASM-safe.

---

## 2026-07-20 — Entry 6: certified rational-function integration (Horowitz)

Research sub-agent returned a precise, sourced design note (Bronstein Ch. 2 +
SymPy `ratint`) mapping Hermite/Rothstein–Trager onto the in-tree `poly`
primitives. Distilled it into [rational-integration.md](rational-integration.md).

### Implemented — Slice 1 (rational part), verified
New module `crates/axeyum-cas/src/ratint.rs` (operates only on `poly.rs` public
functions — **no `axeyum-ir` edits**, parallelism preserved):
- `divrem` (quotient+remainder), `solve_linear` (exact-rational Gauss–Jordan —
  also the seed of C3 linear algebra), `horowitz` (Horowitz–Ostrogradsky rational
  part via one linear system).
`integrate` now handles the **univariate rational fragment**: proper/improper
split → gcd-reduce → Horowitz → certify. **Deviation from the research note:**
used Horowitz (like SymPy) not Hermite — simpler primitives, no
squarefree-factorization list / extended-Euclid; correct on the same class.

**Certification = correctness backstop.** Every antiderivative is differentiated
and zero-tested against the integrand; `integrate` returns `Some` only when the
certificate confirms. So a buggy finder or a log-part case declines to `None`,
never a wrong answer.

**Verified:** `cargo test` → **31 passed / 0 failed** (+ 2 doctests), clippy
`--all-targets` clean, wasm green. `∫1/x² = −1/x` certified; improper
`∫(x²+1)/x² = x − 1/x`; self-certifying roundtrip over `{1/x, 1/(x²+1),
x/(x+1)}` (differentiate R → integrate back → certificate confirms); honest
decline on `∫1/x`, `∫2x/(x²+1)` (need logs). Demo updated:
`∫ (1/x^2) dx = (-1)/x [CERTIFIED]`.

### Next: the logarithmic part (Slice 2a)
Rational-root Rothstein–Trager: resultant `Res_x(P̄−tQ̄',Q̄)` via the **existing**
`sylvester_*` (no new resultant code), `CasExpr::Ln` + `d/dx ln v = v'/v`,
rational root finder; certifies through the existing zero-test once `Ln`
differentiates away. Then 2b (irrational roots, needs `RealAlgebraic::inv`),
2c (`atan` folding). Details in [rational-integration.md](rational-integration.md).

---

## 2026-07-20 — Entry 7: `∫1/x = ln(x)` certified (log part, Slice 2a-i)

Added the transcendental head **`CasExpr::Ln`** (arms in differentiate — `d/dx ln
v = v'/v` — eval → None, substitute, `Display` → `ln(v)`, normalize → None) and
the **linear-denominator logarithmic integration** case: after Horowitz, a log
part `C/D₁` with `D₁ = a·x + b` linear → `(C/a)·ln(a·x+b)`. Higher-degree log
denominators decline (Rothstein–Trager, Slice 2a-ii).

**The key soundness idea** (this is what makes it certify): the certificate must
zero-test the derivative of a *log-containing* antiderivative, but the product
rule leaves a spurious `c'·ln(v)` term. Fix: `normalize_rational` now treats each
`ln(v)` as an **opaque atom** — a fresh variable keyed by `v`'s canonical
rendering. This is *sound*: a zero normal form proves equality (atoms are
independent), while genuine log identities conservatively fail to reduce (→ not
certified, never a false certification). So `d/dx(1·ln x) = 0·ln x + 1/x` reduces
to `1/x` (the `0·ln x` drops), matching the integrand → certified.

**Verified:** `cargo test` → **32 passed / 0 failed** (+ 2 doctests), clippy
`--all-targets` clean, wasm green. `∫1/x = ln(x)` and `∫1/(2x+1) = ½ln(2x+1)`
certified (differentiate back → integrand); `∫2x/(x²+1)` correctly declines
(deg-2 log, needs Slice 2a-ii). Demo: `∫ (1/x) dx = ln(x)  [CERTIFIED]`.

### Next
- **Slice 2a-ii:** Rothstein–Trager for deg ≥ 2 squarefree log denominators with
  rational resultant roots (∫1/(x²−1), ∫2x/(x²+1)=ln(x²+1)). Resultant via the
  existing `sylvester_matrix`/`sylvester_determinant` (convention confirmed:
  coefficients indexed by eliminated-var exponent, entries polys in `t`); add a
  rational root finder over `R(t)`. Then 2b/2c.
- Breadth: univariate factorization (C2/G5), multivariate GCD (G4).

---

## 2026-07-20 — Entry 8: Rothstein–Trager log part (Slice 2a-ii); first commit

### General rational-function integration, certified
Implemented the degree-≥2 logarithmic part in `ratint.rs`:
`rothstein_trager_resultant` (`R(t)=Res_x(P̄−t·Q̄',Q̄)` via the **existing**
`sylvester_matrix`/`sylvester_determinant` — `t` the surviving variable, **no new
resultant code**), `rational_roots` (rational-root theorem + bounded divisor
search), and `log_terms` (per rational root `cᵢ`: `vᵢ = gcd(P̄−cᵢQ̄', Q̄)` monic;
the identically-zero-shift case gives `vᵢ = Q̄`). `integrate_log_part` now assembles
`Σ cᵢ·ln(vᵢ)`.

**Verified:** `cargo test` → **33 passed / 0 failed** (+ 2 doctests), clippy
`--all-targets` clean, wasm green. `∫2x/(x²+1)=ln(x²+1)` (root t=1, v=x²+1);
`∫1/(x²−1)=½ln(x−1)−½ln(x+1)` (roots ±½); `∫1/(x²+1)` **declines** (arctan; roots
±i/2 are complex → honest None, `atan` folding is Slice 2c). All certified by
differentiate-and-check. This covers a large part of SymPy's `ratint`: polynomial +
rational (Horowitz) + logarithmic (Rothstein–Trager, rational roots), every answer
proof-carrying.

### Committing
Per instruction, committing regularly. Isolated to my files (new crate + new docs,
2 one-line shared diffs); shared branch `main`, so I stage only my paths (never the
other agent's in-progress work) and verified the `Cargo.toml`/README diffs are
exactly my additions.

### Next
- **Slice 2c:** complex-conjugate-root folding → real `atan` closed forms
  (`∫1/(x²+1)=arctan(x)`), via `CasExpr::Atan` + `d/dx atan u = u'/(1+u²)`. Then
  **2b** (irrational real roots, needs `RealAlgebraic::inv`).
- Breadth: univariate factorization (C2/G5), multivariate GCD (G4).

## 2026-07-20 — Entry 9: `atan` (Slice 2c) + ongoing sweep to parity

`CasExpr::Atan` + `d/dx atan u = u'/(1+u²)` (opaque atom in the zero-test, like
`ln`). Irreducible-quadratic integration: `∫(c₁x+c₀)/(ax²+bx+d) = (c₁/2a)ln(ax²+bx+d)
+ ((2ac₀−bc₁)/(a·s))atan((2ax+b)/s)`, `s=√(4ad−b²)` (rational-square case; irrational
→ decline, needs algebraic numbers). `∫1/(x²+1)=atan(x)`, `∫1/(x²+4)=½atan(x/2)`,
mixed ln+atan certified; `∫1/(x²+2)` declines (√2). **34 tests, clippy-clean.**
Elementary rational-function integration is now essentially complete (rational +
log + atan). Working continuously toward SymPy/Mathematica parity — next:
elementary function heads (exp/sin/cos/sqrt) with certified differentiation, then
factorization, linear algebra (sub-agent building `matrix.rs`), series, summation.

## 2026-07-20 — Entry 10: breadth sweep toward parity (committing continuously)

Grinding through the CAS surface, committing + pushing each capability. New since
entry 9 (all certified/oracle-free/WASM-safe unless noted; `main` is shared with
the other agent, I stage only my paths):

- **Elementary functions** — refactored `Ln`/`Atan` into an extensible
  `Unary(UnaryFunc,..)` head; added exp/sin/cos/tan/sqrt. Certified chain-rule
  differentiation of any elementary expression; transcendental heads are opaque
  atoms in the zero-test. Elementary **integration** table `∫k·f(ax+b)` for
  exp/sin/cos + `∫ln` by parts.
- **`factor`** (rational linear factors, certified by re-multiplication),
  **`solve`** (rational roots + quadratic formula), **`limit`** (rational: continuous,
  0/0-cancellation, ±∞), **`apart`** (partial fractions via residues, certified),
  **`simplify`** (smallest value-equal form), **`sum_polynomial`** (discrete
  antiderivative, certified by the telescoping identity).
- **Symbolic linear algebra** (`matrix.rs`, sub-agent, reviewed + integrated):
  `Matrix` with transpose/add/sub/mul, cofactor determinant over symbolic entries,
  exact rational RREF / solve / inverse; `det(AB)=det(A)det(B)` certified.
- **In flight (sub-agents):** number theory (`ntheory.rs`), power series
  (`series.rs`).

**Public `axeyum-cas` surface now:** differentiate, substitute, normalize, equal,
expand, cancel, factor, solve, apart, simplify, limit, sum_polynomial, integrate
(poly/rational/log/atan/elementary), + `Matrix`; heads exp/sin/cos/tan/ln/atan/sqrt.
**67 tests + 2 doctests + 23 matrix tests, clippy-clean, WASM-green.**

## 2026-07-20 — Entry 11: comprehensive-core checkpoint (117 tests)

The proof-carrying CAS now covers most of SymPy's core, all committed/pushed to
`main` and validated against SymPy where checked. **117 unit tests + 18 doctests,
clippy-clean, WASM-green.** Two runnable demos (`certified_calculus`, `cas_tour`).

**Public surface (`crates/axeyum-cas`):**
- *Core algebra:* `CasExpr` (+ `Display`, ops, 7 transcendental heads via `Unary`),
  `differentiate` (full chain rule), `substitute`, `normalize`/`equal` (decidable
  polynomial zero-test with witness; transcendental heads as sound opaque atoms),
  `expand`, `cancel` (**uni- and multivariate** via `mvpoly` GCD), `factor`,
  `solve` (rational + real-quadratic + **complex** roots), `apart`, `simplify`,
  `poly_gcd`, `poly_div`.
- *Calculus:* `integrate` → `CertifiedIntegral` (polynomials; full univariate
  rational via Horowitz + Rothstein–Trager + `atan`; `∫k·f(ax+b)`, `∫p·eˣ`,
  `∫p·sin|cos`); `limit`; `series`; `sum_polynomial` (telescoping-certified);
  `dsolve_homogeneous` (constant-coeff ODEs, operator-certified).
- *Modules:* `Matrix` (symbolic linear algebra), `ntheory` (primality/factor/CRT/…),
  `mvpoly` (multivariate polynomials + GCD + square-free), `series`, `ratint`.

**Certification everywhere it's decidable:** integration & derivative claims by
differentiate-and-check; factor/apart/summation/ODE by their respective exact
zero-tests; the certificate doubles as a correctness backstop (out-of-fragment →
`None`, never wrong). Sub-agents (sonnet/opus) built `matrix`, `series`, `ntheory`,
`mvpoly`; each reviewed before integration.

**Plan status:** G0–G4, C0–C6 (incl. log/atan), G17 (complex roots), G18 (const-coeff
ODEs) done or substantially done. **Remaining long tail:** Gröbner (G6), assumptions
engine, trig/log identity simplification, special functions, first-order/
inhomogeneous ODEs, integration by parts/substitution beyond the current tables,
irrational-root integration logs (needs `RealAlgebraic::inv`). When these are
exhausted, extend the roadmap via web research per the goal.

## 2026-07-20 — Entry 12: gap-analysis essentially complete (129 tests)

Since entry 11: **complex numbers completed** (`I²=−1` in the zero-test →
certified complex arithmetic; `conjugate`/`real_part`/`imaginary_part`);
**Pythagorean identity** in the zero-test (`cos²→1−sin²`, per argument) → trig
identities like `sin²+cos²=1`, `cos⁴−sin⁴=cos²−sin²` now **decidable/certified**;
**trig-square integrals** `∫sin²/cos²(ax)` (certified via that identity); **Gröbner
bases** (`groebner.rs`, sub-agent: Buchberger → reduced basis, `reduce` normal
form, `ideal_contains` membership over `MvPoly`); `factor` groups repeated roots
into powers; `differentiate_n`, `degree`/`coeff`/`leading_coeff`, `poly_gcd`/
`poly_div`. **129 tests + 18 doctests, clippy-clean, WASM-green.**

This completes essentially the whole gap-analysis (G0–G18, C0–C6) plus the
Pythagorean/complex zero-test extensions. Next: a research pass (per the goal) to
map the *remaining* SymPy/Mathematica surface (assumptions, special functions,
Risch transcendental integration, more ODE classes, exact eigen/Smith–Hermite,
double-angle/sum trig, polynomial factorization over ℚ via Zassenhaus) and extend
`gap-analysis.md`/`build-plan.md` with the next wave.

## 2026-07-20 — Entry 13: curriculum synthesis + Tier A next-wave build (152 tests)

Ran seven sub-agents, one per `docs/curriculum/` branch (00-foundations …
reconstruction-targets), each cross-checking the roadmap **and the actual code**
for MISSING capabilities, plus a SymPy/Mathematica capability-survey agent. Folded
the union into two roadmap notes — [next-wave-roadmap.md](next-wave-roadmap.md)
(prioritized top-15) and [curriculum-gaps.md](curriculum-gaps.md) (Tier A–D by
value × certifiability × buildability) — and reconciled the doc-hygiene defects the
reviews found (stale build-plan snapshot; Maclaurin-vs-Taylor over-claim; coverage
target stated: **≥ SymPy, → Mathematica**).

Then built the whole **Tier A** wave, each certified and TDD'd:
- **Linear algebra:** `null_space` (RREF free-columns, `A·v=0`), `eigenvectors`
  (rational spectrum via `ker(A−λI)`, `A·v=λv`; dedups; skips irrational/complex
  eigenvalues honestly), `minimal_polynomial` (exact power-dependence search,
  `m(A)=0` by construction).
- **Calculus:** `definite_integrate` (FTC on the certified antiderivative),
  `series_at` (arbitrary-center Taylor via the shift identity — fixes the prior
  Maclaurin-only limitation), `gradient`/`jacobian`/`divergence`/`curl` (certified
  partials).
- **K-12 / reals:** `simplify_radicals` (`√12→2√3`, rationalize denominators; exact
  integer identity `k²·m=c`), `stats` module (exact mean/median/mode/variance),
  `standard_deviation` (surd-simplified).
- **Number theory (sub-agent `ntheory_advanced`):** `permutations` (nPr),
  Legendre/Jacobi symbols, quadratic residues, `multiplicative_order`,
  `primitive_root`, `discrete_log` (BSGS), continued fractions + convergents,
  Pell fundamental solution — all re-check-certified.

**152 unit + 31 doctests, clippy-pedantic clean, WASM-green.** In flight: univariate
factorization over ℤ/ℚ (Berlekamp–Zassenhaus, sub-agent). Next (Tier B): first-order
ODE methods, linear-recurrence closed forms, public resultant/discriminant, the
`Abs` head, exact trig-value table.

## 2026-07-20 — Entry 14: Tier B progress + a new sound fold (166 tests)

Continued the next-wave build past Tier A into Tier B, all certified/TDD:
- **`resultant` / `discriminant`** (public) — exposing the existing Sylvester
  machinery. `resultant = 0` iff common root/factor; `disc(x²+bx+c) = b²−4c`;
  `disc = 0` detects repeated roots (incl. a cubic with a double root). Fixed the
  trimmed-empty-determinant (vanishing resultant) case to return `Const(0)`.
- **Univariate factorization over ℤ/ℚ** (`factor_int`, sub-agent, verified):
  Berlekamp–Zassenhaus (Yun squarefree → Berlekamp mod p → Hensel lift → complete
  recombination). `x⁴−10x²+1` correctly irreducible; `factor_expr` returns only
  `Certified`-equal results.
- **`solve` via factorization** — degree-≥3 leftovers are now factored over ℚ and
  each quadratic factor solved, so products of irreducible quadratics fully solve
  (`x⁴+5x²+4 → ±I,±2I`; `x⁴−5x²+6 → ±√2,±√3`; `x³−x²+x−1 → 1,±I`).
- **`fold_radical`** — a new **sound** zero-test reduction `sqrt(c)² → c` for
  `c ≥ 0` (rational radicand parsed from the atom key), the same shape as the
  imaginary/Pythagorean folds. It certifies radical arithmetic (`√2·√2 = 2`,
  `(1+√2)² = 3+2√2`, `(√3−1)(√3+1) = 2`) **and** the irrational-root substitutions
  above — turning `simplify_radicals`' output and irrational quadratic roots into
  certified results.

**166 unit + 33 doctests, clippy-pedantic clean, WASM-green.**

**Identified blocker (recorded, not yet built).** First-order linear ODEs and
linear-recurrence closed forms both need the zero-test to know
`e^A·e^B = e^{A+B}` (the integrating-factor / `rⁿ`-as-`e^{n ln r}` cancellations).
The opaque-atom representation keys `exp` by the *render* of its argument, so
combining two exp atoms requires summing their argument *expressions*, which the
current MultiPoly (string-keyed atoms) can't do. The fix is an atom-representation
refactor: carry the argument `CasExpr` alongside the atom key and add a
`fold_exponential` that sums exp arguments within a monomial (mirroring
`fold_radical`). This is the next real substrate step — it unlocks first-order
ODEs, recurrences, and general `exp`/`log` simplification at once. Sequenced ahead
of the assumptions engine.

## 2026-07-20 — Entry 15: more Tier B/C breadth (171 tests)

Kept building certifiable breadth without waiting on the exp-tower substrate:
- **Inhomogeneous linear ODEs with polynomial forcing** (`dsolve_inhomogeneous`):
  undetermined coefficients (with the `xˢ` resonance factor), particular solution
  from an exact linear solve, plus the homogeneous part; **certified** by
  substituting the full solution into the operator and zero-testing against the
  forcing. Fully certifiable *without* the exp refactor — the particular part is
  polynomial and the homogeneous exp terms are single atoms.
- **Cyclotomic polynomials** (`cyclotomic_polynomial`): from `∏_{d∣n} Φ_d = xⁿ−1`
  by exact recursive division; certified by the product identity.
- **Exact trig values** (`evaluate_trig`): full unit-circle table at every multiple
  of `π/12` (`sin(π/6)=1/2`, `tan(π/3)=√3`, `sin(π/12)=(√6−√2)/4`), keyed on the
  reserved constant `pi`; compute op whose values interoperate with the certified
  zero-test (`sin²+cos²=1` on the exact values certifies).
- **`evalf`** (exact→decimal), **LU decomposition** (`P·A=L·U`, certified by
  reconstruction), **`resultant`/`discriminant`**, and the **`sqrt(c)²→c` fold**
  (all recorded earlier this day).

**171 unit + 37 doctests, clippy-pedantic clean, WASM-green.** Gosper indefinite
hypergeometric summation is in flight (sub-agent, telescoping-certified). The
exp-combination/differential-tower refactor remains the sequenced next substrate
step (unlocks first-order ODEs, recurrences, general exp/log simplification).

## 2026-07-20 — Entry 16: log rules, absolute value, vector ops (174 tests)

Further breadth toward K-12 + linear-algebra parity:
- **`expand_log`** — product/quotient/power log rules (`ln(a·b)→ln a+ln b`, etc.),
  honestly labelled compute (valid for positive reals; the certifying assumptions
  engine is future work).
- **`Abs` head** — a new `UnaryFunc::Abs` with a constant-folding constructor
  (`|−3|=3`), `d/dx|x|=x/|x|`, `evalf`, and the sound `√(b^{2k})→|bᵏ|` rewrite in
  `simplify_radicals` (so `√(x²)=|x|`).
- **Vector ops** — `dot`, `cross`, `norm` (√(v·v), surd-simplified); dot/cross
  certified by the zero-test, norm exact via the `sqrt(c)²→c` fold.

**174 unit + 38 doctests, clippy-pedantic clean, WASM-green.** Gosper hypergeometric
summation still in flight. The exp-tower substrate refactor remains the sequenced
next step (first-order ODEs / recurrences / general exp-log simplification).

## 2026-07-21 — Entry 17: Gosper summation shipped (185 tests)

**Gosper's algorithm** (`gosper.rs`, sub-agent) — indefinite hypergeometric
summation, roadmap next-wave #1. Full pipeline on exact poly primitives (reduced
ratio → Gosper–Petkovšek normal form via dispersion resultant → degree-bounded
Gosper-equation solve → antidifference). Rational-function terms fully certified by
the decidable telescoping zero-test (`∑k`, `∑1/(k(k+1))→−1/k`); geometric×poly
(`∑k·2ᵏ→(k−2)2ᵏ`) certified via the reduced Gosper identity (polynomial in `k`)
plus exact telescoping spot-checks; non-summable (`∑1/k`) and factorial heads
declined honestly.

**Second independent confirmation of the exp-tower blocker.** The Gosper agent
measured that `equal(Δ[(k−2)2ᵏ], k·2ᵏ)` returns `Certified{equal:false}` — because
`exp((k+1)ln c)` and `exp(k ln c)` are independent opaque atoms and the exponent
law `eᴬ·eᴮ=eᴬ⁺ᴮ` is never applied. This is exactly the substrate gap identified for
first-order ODEs and recurrences, now confirmed from a second angle. Design note:
[exp-tower.md](exp-tower.md). It is the single highest-leverage next substrate step.

**185 unit + 38 doctests, clippy-pedantic clean, WASM-green.**

## 2026-07-21 — Entry 18: real-root isolation + numeric roots (191 tests)

**Sturm real-root isolation** (`sturm.rs`, roadmap next-wave #8): `real_root_intervals`
isolates each real root of a univariate polynomial into a disjoint half-open interval
Sturm-certified to hold exactly one root (multiplicity collapsed via the square-free
part); `count_real_roots` counts roots in any interval. The Sturm sign-count *is* the
certificate — exact, theorem-backed, in exact rational arithmetic (Cauchy bound +
bisection worklist with a resource cap). **`approximate_real_roots`** refines those
intervals by sign-bisection to any width, giving decimalizable roots for irrational
or degree-≥5 polynomials beyond closed-form radicals.

This is the gateway to RootOf / algebraic-number machinery — the prerequisite for
next-wave #15 (Lazard–Rioboo–Trager algebraic-number integration). Hermite/Smith
normal form (#9) delegated to a sub-agent. **191 unit + 39 doctests, clippy-clean,
WASM-green.**

## 2026-07-21 — Entry 19: normal forms, permutations, exp reciprocals (206 tests)

- **Hermite & Smith normal forms** (`normalforms.rs`, sub-agent, next-wave #9):
  `U·A=H` and `U·A·V=D` for integer matrices; certified by the re-multiply identity
  (via `Matrix::mul`+`equal`) **and** `det(U)=det(V)=±1` (unimodularity). Unblocks
  integer linear systems / Diophantine, module theory, f.g. abelian group structure.
- **Permutations** (`permutation.rs`): symmetric-group objects — compose, inverse,
  cycles, order, sign; group laws verified by direct computation.
- **Polynomial inequalities** (`solve_polynomial_inequality`, k12 #2): sign chart →
  interval unions, Sturm-guarded against irrational endpoints.
- **exp reciprocal canonicalization** — `exp(0)=1`, `exp(−A)=1/exp(A)`, so
  `exp(−P)·exp(P)=1` now decides (first partial step of the [exp tower](exp-tower.md);
  zero regressions).

**206 unit + 40 doctests, clippy-pedantic clean, WASM-green.** This session took the
crate from 129 → 206 tests: full curriculum synthesis + ~23 new capabilities across
Tier A–C (Gosper, Sturm, factorization, normal forms, ODE methods, exact trig,
statistics, vector calculus, number theory, radicals, …). Remaining headline gaps:
the full exp tower (unlocks first-order ODEs / recurrences / general exp-log), RootOf
(unblocked by Sturm — next), Zeilberger, assumptions engine, Risch.

## 2026-07-21 — Entry 20: the exp tower + its payoffs (209 tests)

Built the **exp-tower substrate** — the highest-leverage remaining item — via a
lower-risk per-term decomposition in `normalize_exp` (no Monomial redesign needed):
addition (`exp(A+B)=exp(A)exp(B)`), integer scaling (`exp(2x)=exp(x)²`,
`exp(x)·exp(2x)=exp(3x)`), the exp/ln inverse (`exp(k·ln v)=vᵏ`, v>0 rational), and
reciprocals (`exp(0)=1`, `exp(−A)=1/exp(A)`). All sound; **zero regressions** across
integration/series/ODE tests. Then shipped the two capabilities it unlocks:
- **`dsolve_first_order_linear`** — integrating-factor method, certified by the
  `e^{−P}·e^P=1` cancellation the tower now provides.
- **`solve_recurrence`** — rational-root linear recurrence closed forms
  (`aₙ=5aₙ₋₁−6aₙ₋₂ → 3ⁿ−2ⁿ`, `rⁿ=exp(n·ln r)`), certified by the recurrence residual;
  Fibonacci (irrational roots) declines honestly.

Also this stretch: **partial fractions with repeated linear factors** (`apart` via
undetermined coefficients), **Hermite/Smith normal forms**, **permutations**,
**polynomial inequalities**. **209 unit + 43 doctests, clippy-clean, WASM-green.**
Remaining exp-tower tail (rational-coefficient scaling, non-constant `exp/ln`) is
documented in [exp-tower.md](exp-tower.md); it needs the RootOf/RealAlgebraic layer.

## 2026-07-21 — Entry 21: exp-tower payoffs + broad parity wave (258 tests)

The exp tower (entry 20) unlocked a cascade, and a parallel sub-agent wave added
breadth. Since entry 20 (209 → 258 tests):

- **Fibonacci / Binet** — `solve_recurrence` extended to quadratic-irrational roots
  including **negative** ones (`rⁿ = cos(πn)·exp(n·ln|r|)`), certified over ℚ(√D) by
  a roots-and-initials argument. `F(n) = (φⁿ − ψⁿ)/√5` reproduces 0,1,1,2,3,5,8,13;
  Lucas too.
- **RootOf** — `algebraic::AlgebraicReal` + `real_roots`: every real root of a
  univariate polynomial as (irreducible minimal polynomial + Sturm-certified
  isolating interval), any degree (∛2, the non-solvable quintic x⁵−x−1), with f64
  refinement.
- **Trig identities via Euler** — `rewrite_exp` + exp tower + `I²=−1` make **all
  polynomial trig identities decidable** (double-angle, sum, product-to-sum,
  power-reduction), non-identities correctly rejected.
- **Full partial fractions** — `apart` now handles irreducible factors of any degree
  (linear, quadratic, repeated) via undetermined coefficients.
- **Residues** (`residue`) of rational functions at a pole (order-m formula).
- **Linear algebra / calculus** — `wronskian`, `gram_schmidt`, `hessian`,
  `laplacian`.
- **Sub-agent modules** (each verified, throwaway-crate tested, clippy-clean):
  `orthopoly` (Chebyshev/Legendre/Hermite/Laguerre), `combinatorics` (Bernoulli/
  Euler/Stirling/Bell/partitions/Catalan/Fibonacci/Lucas), `approx` (Padé +
  Lagrange/Newton interpolation), `ntheory_more` (Möbius/Mertens/σ_k/Carmichael/
  primorial/π(n)/nth_prime/…).

**258 unit + 70 doctests, clippy-pedantic clean, WASM-green.** Work is on a dedicated
`main` worktree (`cas/parity-push`) to keep clear of the concurrent solver-side
branch sharing the repo. Next: definite integrals via residues, Laurent/Puiseux
series, Jordan form, Gruntz limits, special functions with derivative rules, Risch.

## 2026-07-21 — Entry 22: broad SymPy-parity wave (283 tests)

Continued the parity push with core work + a second sub-agent wave (each module
verified in a throwaway crate with its own target dir, clippy-clean). Since entry 21
(258 → 283 tests):

- **Transcendental limits via series** — `limit` now does `0/0` transcendental forms
  by comparing leading series terms (`sin x/x=1`, `(1−cos x)/x²=1/2`, `(eˣ−1)/x=1`);
  poles → `None`.
- **Laplace transform** (`laplace_transform`) over the elementary fragment via the
  `L{tᵏg} = (−1)ᵏ dᵏ/dsᵏ L{g}` rule + the standard table.
- **Matrix** `adjugate`/`cofactor`/`pow`/`is_symmetric`; **finite calculus**
  (`falling`/`rising_factorial`, `forward`/`backward_difference`); `poly_lcm`,
  `is_irreducible`.
- **Sub-agent modules**: `boolean` (BoolExpr, truth tables, tautology/SAT, DNF/CNF,
  Quine–McCluskey), `geometry` (Point/Line/Circle over exact rationals).

Total this session's parity push added ~50 capabilities across recurrences (incl.
Fibonacci/Binet), RootOf, residues, Gram–Schmidt, Wronskian, Hessian/Laplacian, full
partial fractions, trig-identities-via-Euler, orthogonal polynomials, combinatorial
numbers, Padé/interpolation, extended number theory, Boolean algebra, geometry,
Laplace, and the **exp tower** substrate that unlocked much of it. **283 unit + 71
doctests, clippy-pedantic clean, WASM-green.** All on the `cas/parity-push` → `main`
worktree. Next: Laurent/Puiseux series, definite integrals via residues, Jordan form,
special functions with derivative rules, Zeilberger, Risch.

## 2026-07-21 — Entry 23: deep parity — the CAS at 355 tests

Sustained the parity push with core work + a third/fourth sub-agent wave (each module
verified in an isolated throwaway crate, clippy-clean). Since entry 22 (283 → 355):

**Core (in-lib):** RootOf `AlgebraicReal`; full `apart`; `residue`; `laurent_series`;
`series_reversion`; transcendental `limit` via series (`sin x/x=1`); `laplace_transform`
+ `inverse_laplace`; `definite_sum`; `diagonalize` (P·D·P⁻¹); `wronskian`,
`gram_schmidt`, `hessian`/`laplacian`; Matrix `adjugate`/`cofactor`/`pow`/`bareiss_
determinant`/`hadamard`/`kronecker` + predicates; `solve_linear_system`;
`least_squares_polynomial`; `rewrite_exp` (Euler → all polynomial trig identities);
`logcombine`; `modulus`/`roots_of_unity`; `content`/`primitive_part`, `poly_lcm`,
`is_irreducible`; `∫atan`, `∫p·ln`; finite calculus; `rationalize`; covariance/correlation.

**Sub-agent modules (10 total this session):** `orthopoly`, `combinatorics`, `approx`
(Padé/interpolation), `ntheory_more`, `boolean` (Quine–McCluskey), `geometry`,
`hyperbolic`, `gfp` (𝔽ₚ[x] + Berlekamp), `sets` (RealSet algebra), `interval_arith`
(rigorous enclosures), plus `special` (Gamma/Beta).

The **exp tower** substrate remains the load-bearing unlock (first-order ODEs,
recurrences incl. Fibonacci/Binet, hyperbolic + trig identities all certify through
it). **355 unit + 98 doctests, clippy-pedantic clean, WASM-green.** All on the
`cas/parity-push` → `main` worktree, kept clear of the concurrent solver-side branch.
Remaining frontier: assumptions engine, full Risch, Zeilberger, Jordan form for
defective matrices, Gruntz limits, multivariate factorization, PDEs.

## 2026-07-21 — Entry 24: assumptions, a zero-test soundness fix, clean display (365 tests)

Consolidation + correctness pass, all in-lib. Since entry 23 (355 → 365):

**Assumptions engine** (`assumptions.rs`): a `Sign` lattice (positive/negative/zero/
nonneg/nonpos/unknown) with sound product/sum/negate combinators and an `Assumptions`
set whose `sign_of` decides an expression's sign structurally (`exp>0`, even power ≥0,
`|·|≥0`, `√·≥0`, product/sum of signs). Gates `simplify_under_assumptions`:
`|u|→u`/`√(x²)→x` when `x≥0`, `|u|→−u` when `x≤0`.

**Zero-test soundness fix (important).** The core cross-multiplication test treats each
transcendental head as an *independent* atom — sound for asserting *equality*, but it
was emitting `Certified{equal:false}` for **true** identities whose atoms are secretly
related: `equal(tan x, sin x/cos x)` and `equal(cos 2x, 2cos²x−1)` were *false proofs of
inequality*. Fix: `equal` now re-checks any non-equal core result on the `rewrite_exp`
(Euler) canonical form — where sin/cos/tan become complex exponentials and the exp-tower
makes distinct atoms genuinely independent (ℚ-linearly-independent exponents ⇒
algebraically independent), so a nonzero witness is *sound*. Denotation-preserving and
identity on trig-free input; an undecidable re-check downgrades to `Unknown`, never a
false cert. Unlocks tan/double-angle/product identities in the zero-test.

**Display fix (pervasive).** `expand`/`cancel`/`simplify` were leaking the internal
`\0head:…` atom keys: `expand(sin(2x+1))` returned the literal `\0sin:2*x + 1`,
`simplify(sin x)` returned ` sin:x`. Added `collect_atom_dictionary` + `deatomize`
(reconstructing exp-tower per-term / integer-scaled / sign-canonical / conjugate-trig
keys) as a post-pass. All transcendental output now renders cleanly.

**New capability.** `trigsimp` (Pythagorean `sin²+cos²=1`, both reduction directions,
equality-gated smallest form) — now also wired into `simplify`. Integration finders for
`∫p·eˣ·sin|cos` (exp×trig, one coupled linear system), `∫sinᵐcosⁿ` (odd-power
substitution), and `∫tan` (via the now-sound Euler equal).

**365 unit + 99 doctests, clippy-pedantic clean, WASM-green.** Frontier unchanged:
full Risch, Zeilberger, Jordan form, Gruntz limits, multivariate factorization, PDEs.

## 2026-07-21 — Entry 25: numerics polish + matrix exp / ODE systems / ζ (371 tests)

Continued the in-lib parity + polish push. Since entry 24 (365 → 371):

**New capability.** `matrix_exp` (e^{A·t} for ℚ-diagonalizable A, certified by the
defining IVP d/dt M = A·M ∧ M(0)=I); `linear_ode_system` (x′=Ax ⇒ x=e^{At}x0, cert
inherited); `special::zeta` (exact ζ(2k)=(−1)^{k+1}B_{2k}(2π)^{2k}/(2(2k)!) = c·π^{2k},
ζ(0)=−1/2, ζ(−m)=−B_{m+1}/(m+1) via the existing Bernoulli; honest None at the s=1
pole and positive-odd s≥3); `series` of `tan` (sin/cos quotient) → unblocks
`lim tan x/x`.

**Polish (display/correctness).** `differentiate_n` now folds each step (`d³ sin =
−cos`, not a giant tree); `fold_trivial` gained `−(−x)→x`, `x¹→x`, `x⁰→1`, nested-Mul
+ constant combining. `simplify_radicals` cancels constant denominators (√8/2→√2).
Quadratic solver extracts/reduces surds (`solve(x²−12)=±2√3`, `solve(x²+4)=±2I`) via a
new `simplify_surd`. `definite_integrate` folds elementary constants (∫₀^π sin x=2,
∫₁² 1/x=ln 2). `apart` folds factor^1→factor.

**Numerics note.** `evalf` remains f64 (~15 digits) — there is no arbitrary-precision
`N[expr,d]` yet; that is a deliberate architectural fork (a pure-Rust WASM-safe bignum
float + Euler-Maclaurin/AGM kernels), kept separate from the dependency-free core.
Integer factorization is already fast (Brent Pollard-rho + Miller-Rabin, u128,
overflow-safe) — adequate for all in-fragment inputs.

**371 unit + 102 doctests, clippy-pedantic clean, WASM-green.** Frontier: Jordan form
(defective), Zeilberger, Gruntz, multivariate factorization, arbitrary-precision N[].

## 2026-07-21 — Entry 26: Jordan form, systems, transcendental solve (379 tests)

Frontier linear-algebra + solving wave, all in-lib. Since entry 25 (371 → 379):

**Jordan canonical form** (`jordan_form`, `jordan_decomposition`): P·J·P⁻¹ for any
rational-spectrum matrix, **including defective** ones — generalized-eigenvector
chains from the nullities of (A−λI)^k (new chain tops = ker(B^ℓ) vectors independent
of ker(B^{ℓ−1}) + descending images, rank-tested). Certified A·P=P·J. This
**generalized `matrix_exp`** to defective matrices: exp(A·t)=P·exp(J·t)·P⁻¹ with the
per-block e^{λt}·t^d/d! super-diagonals (so exp([[2,1],[0,2]]t)=e^{2t}[[1,t],[0,1]]).

**`solve_polynomial_system`**: two bivariate polynomials via the Sylvester resultant
(a CasExpr-entry determinant, retaining x-coefficients), solve R(x)=0, back-substitute,
return pairs satisfying both (certified). Circle∩hyperbola⇒(±4,±3). Irrational-coordinate
solutions honestly dropped.

**Transcendental `solve`**: A·exp(ax+b)+C=0 ⇒ ln-root, certified by a two-part check
(head reduces `exp(ln v)=v`; root links back — sidesteps the tower's rational-arg gap).
**Exponential-dominance limits** at ±∞ (x²/eˣ→0). **`series(tan)`** (sin/cos quotient).

**Exact special values/polynomials**: `zeta` (ζ(2k)=c·π^{2k}, ζ(−m) via Bernoulli),
`bernoulli_polynomial`/`euler_polynomial`, `harmonic`/`generalized_harmonic`,
`finite_product` (∏ over concrete bounds). **Numerics note**: `evalf` is still f64 —
arbitrary-precision `N[expr,d]` remains a deliberate (bignum-dependency) fork.

**Infra**: a home-dir disk-quota exhaustion mid-session broke rustdoc linking + the shell's
output capture; fixed by pruning stale dated nightly toolchains and routing rustdoc temp to
the `/nas4` volume via `TMPDIR` (see `axeyum-cas-worktree` memory).

**379 unit + 109 doctests, clippy-pedantic clean, WASM-green.** Frontier: Zeilberger,
Gruntz (general), multivariate factorization, Puiseux, arbitrary-precision N[].

## 2026-07-21 — Entry 27: ODE suite, Z-transform, trig/improper (386 tests)

Solving + transforms + ODE breadth wave. Since entry 26 (379 → 386):

**First-order ODE suite completed**: `dsolve_separable` (y′=f(x)g(y) ⇒ implicit
G(y)−F(x)−C0, certified by ∂S/∂y=1/g ∧ ∂S/∂x=−f), `dsolve_exact` (M dx+N dy=0 with
∂M/∂y=∂N/∂x ⇒ potential F, certified ∂F/∂x=M ∧ ∂F/∂y=N), `dsolve_bernoulli` (y′+py=qy²
via v=1/y → the linear solver, certified by substitute-back). Joins the existing
homogeneous/inhomogeneous/integrating-factor solvers.

**Z-transform pair** (`z_transform`/`inverse_z_transform`): discrete Laplace over the
geometric fragment (z/(z−a) ↔ aⁿ), inverse via partial fractions of X(z)/z, round-trip
certified. **Trig equation solving** in `solve` (2sin x−1⇒π/6,5π/6, principal in [0,2π)).
**Improper integrals** (`improper_integrate`, ±∞ bounds via the exp-dominance limit —
∫₀^∞ x²e^{−x}=2, divergence declined). **Combinatorics**: derangements, double
factorial, multinomial.

**386 unit + 117 doctests, clippy-pedantic clean, WASM-green.** (Infra: a mid-session
home-quota exhaustion is worked around via `TMPDIR=/nas4/...` for rustdoc; see the
`axeyum-cas-worktree` memory.) Frontier: Zeilberger, general Gruntz, multivariate
factorization, Puiseux, new special-function heads (erf/Si/Ci/Ei), arbitrary-precision N[].

## 2026-07-21 — Entry 28: integration completeness + number theory (391 tests)

Integration-engine completion + number-theory/special-function fills. Since entry 27
(386 → 391):

**`integrate` structural rules**: additive linearity `∫(f+g)=∫f+∫g` (was missing — so
`eˣ+e^{−x}` had declined) and the constant-multiple rule `∫c·f=c·∫f` (`split_constant_
factor` peels a Div-by-const / Neg / Mul-with-const). Together these compose with the
finders to integrate **hyperbolics** (sinh/cosh via their exp form), `−sin x`, mixed
sums (`x+eˣ+1/(x²+1)`), etc. **Both-even trig** (`∫cos⁴x`, `∫sin²cos²`) via Euler
power-reduction to a `cos(k·u)` sum — completing trig-monomial integration. **Log
substitutions** `∫ln x/x=½(ln x)²`, `∫1/(x ln x)=ln(ln x)`.

**Number theory / special**: `sqrt_mod` (Tonelli–Shanks modular square root, cert by
squaring); `gamma` extended to **negative half-integers** (Γ(−1/2)=−2√π via the
recurrence).

**391 unit + 118 doctests, clippy-pedantic clean, WASM-green.** The integration engine
now covers: polynomials, full rational (Rothstein–Trager), elementary tables, poly×{exp,
log,sin,cos}, exp×trig, trig monomials (odd+even), ∫tan, log-substitution, additive/
constant linearity, definite (FTC + constant folding), improper (±∞). Frontier: general
substitution/by-parts, Risch; Zeilberger; Gruntz; multivariate factorization; Puiseux;
erf/Si/Ci/Ei heads; arbitrary-precision N[].

## 2026-07-21 — Entry 29: the special-function heads frontier (415 tests)

Broke into the special-function frontier — the first genuinely "hard" roadmap tier.
Since entry 28 (391 → 415, plus the calculus/number-theory fills at 391–411):

**Nine new integral-defined special-function heads** (`UnaryFunc::Erf/Si/Ci/Ei/Li/Shi/Chi/
FresnelS/FresnelC`), each carrying its **defining integral as a certified antiderivative**
(differentiate-and-check): ∫e^{−x²}=(√π/2)erf(x) (perfect-square a), ∫sin x/x=Si, ∫cos x/x=Ci,
∫eˣ/x=Ei, ∫1/ln x=li, ∫sinh x/x=Shi, ∫cosh x/x=Chi, ∫sin(πx²/2)=FresnelS, ∫cos(πx²/2)=FresnelC.
Each has a chain-rule derivative, `.erf()/.si()/…` builders, a numeric `evalf` (their series /
Abramowitz–Stegun), and `series`/`fold_elementary_constants` handling. **Key finding: adding a
head is cheap** — only 4 match sites are exhaustive over `UnaryFunc` (`name`, `differentiate`,
`series::unary_series`, `evalf`); all else (`normalize_rational`, `rewrite_exp`, `evaluate_trig`,
`simplify_radicals`, `assumptions::sign_of`) has a catch-all.

Supporting integration machinery: `integrate_gaussian`, `integrate_special_integral` (f(ax)/x),
`integrate_fresnel`, and `integrate_split_fraction` (∫(f+g)/h=∫f/h+∫g/h via a `flatten_fraction`
that collapses nested divisions) + denominator-constant and negated-numerator pulls in
`split_constant_factor` — so Shi/Chi fall out of sinh/cosh-over-x by linearity.

Also (391→411, the pre-frontier fills): ∫ additive/constant linearity, both-even trig, log-sub;
improper integrals; `function_parity` + odd-over-symmetric definite shortcut; `average_value`,
`root_mean_square`; `companion_matrix`; Tonelli–Shanks, Kronecker, Jordan totient, perfect-power,
amicable/abundant/deficient, Pythagorean triples, linear congruences; ζ/η/λ/polygamma, Γ at
negative half-integers; Pell/Jacobsthal/Tribonacci/Motzkin/Eulerian/Narayana/Lah numbers.

**415 unit + 143 doctests, clippy-pedantic clean (incl. examples), WASM-green.** Frontier
remaining: Gamma/digamma **heads** (derivative tower), Bessel, multivariate factorization,
Puiseux, Zeilberger, general Gruntz/Risch, arbitrary-precision N[expr,d].

## 2026-07-21 — Entry 30: substitution/power-rule integration + a radical soundness fix (421 tests)

Two more integral-defined heads (`BesselJ0/J1`, closed derivative pair J₀′=−J₁, J₁′=J₀−J₁/u)
and the inverse pair `asin/acos/asinh/acosh` (415→419) with `∫1/√(1−x²)=asin`, `∫1/√(x²+1)=asinh`,
`∫1/√(x²−1)=acosh`. Then a **substitution/power-rule wave** on the integrator, each certified by
the usual differentiate-and-check:

- **`atom_name` canonicalization** — sqrt/atom keys now key on the *normalized* argument, so
  `√(1+x²)` and `√(x²+1)` share one atom and relate under `equal` (general zero-test robustness).
- **`integrate_radical_usub`**: `∫k·f′/√f = 2k·√f` (`∫x/√(1−x²)=−√(1−x²)`, `∫(2x+1)/√(x²+x)`).
- **`integrate_sqrt_power`**: the half-integer power rule the `Pow(_,u32)` representation can't
  hold — `∫√x=(2/3)x√x`, `∫xᵐ√x`, `∫√(ax+b)`.
- **`integrate_exp_quadratic_usub`**: `u=x²` reversal for an odd polynomial times `{exp,sin,cos}`
  of a pure-quadratic argument — `∫x·e^{x²}=½e^{x²}`, `∫x·sin(x²)=−½cos x²`, `∫x³·cos(x²)`.
- **`integrate_power_of_inner`**: the general reverse power rule `∫k·g′·gⁿ = k·gⁿ⁺¹/(n+1)` for a
  factor `gⁿ` whose cofactor is a constant multiple of `g′` — `∫(ln x)²/x=(ln x)³/3`,
  `∫eˣ(eˣ+1)²`, `∫atan²/(x²+1)`; handles both `Mul` and `Div` shapes. New `multipoly_proportion`
  decides `rest = k·g′` over the atom-polynomial ring.

**Soundness fix (important):** the zero-test's `fold_radical` only reduced `(√c)²=c` for rational
*constant* radicands, so `equal(x/√x, √x)` and `equal((√x)², x)` certified **FALSE** — a
relation-blind inequality on a true identity. Generalized it to symbolic radicands: `equal_core`
resolves each sqrt atom's radicand from the compared expressions and passes the dictionary into
`fold_radical`, which now reduces `sqrt(u)^{2k} → u^k` for any `u`. Sound wherever `√u` is real
(`u≥0`). This is what makes the half-integer power rule certify (the derivative check folds
`u/√u=√u`), and fixes radical arithmetic generally.

**421 unit + 142 doctests, clippy-pedantic clean, WASM-green.**

## 2026-07-21 — Entry 31: rational-integration completeness + by-parts family (425 tests)

Pushed the integrator to **complete univariate rational integration over ℚ** and rounded out the
by-parts family. All certified by differentiate-and-check.

- **Mixed ℚ-factor denominators** (`integrate_log_part_by_factoring`): the Rothstein–Trager
  rational-root scan returns only *rational-residue* logs, so a squarefree denominator mixing a
  linear and an irreducible-quadratic factor got an incomplete (cert-failing) result. Now factor
  the squarefree denominator over ℚ (via `apart`) and integrate each partial fraction directly —
  linear→log, quadratic→ln+atan — tried *before* `log_terms` since it is complete-or-declines.
  Closes `∫1/(x³±1)`, `∫x/(x³+1)`, `∫1/((x+1)(x²+1))`, `∫(3x+2)/((x−1)(x²+4))`.
- **Surd atan** for irreducible quadratics whose `√(4ad−b²)` isn't a perfect square:
  `∫1/(x²+x+1) = (2/√3)atan((2x+1)/√3)` — built with a symbolic surd (squares away in the
  cert). Previously declined.
- **Real-irrational-root quadratics** (`integrate_real_irrational_quadratic`, disc>0 non-square):
  algebraic surd-logs `∫1/(x²−2) = (1/2√2)ln((x−√2)/(x+√2))`. The disc<0/disc>0 pair now covers
  every ℚ-irreducible quadratic factor.
- **By-parts**: `∫P·(ln x)ᵐ` (`integrate_log_power`, repeated by-parts), and `∫P·f` for inverse
  `f ∈ {atan,asin,acos,asinh,acosh}` (`integrate_poly_times_inverse`, residual `∫Q·f′` run
  through `cancel` then re-integrated) — `∫x·atan x`, `∫asin x`, `∫ln²x`.
- **Substitution/power-rule** (from earlier in the wave): reverse power rule `∫k·g′·gⁿ`,
  log-derivative `∫k·g′/g`, radical u-sub `∫k·f′/√f`, half-integer `∫√(ax+b)`, `u=x²` for
  odd·{exp,sin,cos}(x²).

What still declines (honestly): trig substitution (`∫x²/√(1−x²)`, hence `∫x·asin`), Weierstrass
(`∫1/(1+cos x)`), degree-≥3 irreducible-over-ℚ denominators (`∫1/(x⁴+1)`), and genuinely
non-elementary integrands (`∫e^{x²}`).

**425 unit + 142 doctests, clippy-pedantic clean, WASM-green.**

## 2026-07-21 — Entry 32: trig-sub radicals, solve (ln/√/eˣ-poly), limit log-at-0 (427 tests)

Rounded out three surfaces beyond integration:

- **Trig-substitution radicals** (`integrate_sqrt_quadratic`, a=1 forms): `∫√(1−x²)=½(x√(1−x²)+asin x)`,
  `∫√(1+x²)`, `∫√(x²−1)`, and `∫(c·x²)/√(1±x²|x²−1)`. Allowing a constant-multiple numerator makes the
  by-parts residual `∫(x²/2)/√(1−x²)` resolve — so **`∫x·asin x`, `∫x·acos`, `∫x·asinh`, `∫x·acosh`
  now cascade** through `integrate_poly_times_inverse`.
- **`solve` transcendentals**: `ln x = c ⇒ eᶜ` and `√x = c ⇒ c²` (new `Sqrt` arm; the `head_reduces`
  certificate runs `simplify_radicals` so `√9→3`). Enabled by a new **`ln(exp u)=u` zero-test fold**
  (`rewrite_log_exp`, the exp→ln left inverse, sound for real `u`) wired into `equal`'s
  canonicalization. Plus **polynomials in eˣ** (`solve_exp_polynomial`/`exp_to_power`): rewrite
  `P(eˣ)=0` to a polynomial in `u=eˣ`, solve, map positive rational roots back via `x=ln u` —
  `e^{2x}−5e^x+6⇒{ln2,ln3}`, dropping non-positive/complex `u`.
- **`limit` log-vs-power at 0** (`limit_log_at_zero`): a positive power of `x` beats any power of
  `ln x`, resolving the `0·∞` form the series fallback can't (`x·ln x=0`, `1/ln x=0`); genuinely
  divergent forms decline.

**427 unit + 142 doctests, clippy-pedantic clean, WASM-green.**

## 2026-07-21 — Entry 33: breadth wave — transforms, sums, factoring, asymptotes (433 tests)

A broad parity sweep across many surfaces (each certified):

- **Transforms.** Laplace **s-shift** `L{e^{at}f}=F(s−a)` (`L{e^t sin t}`, `L{t·e^t·sin t}` — flatten
  the nested `Mul` and extract the exp as a shift); **inverse Laplace of irreducible quadratics** →
  (damped) sinusoids `L⁻¹{1/((s−1)²+4)}=½e^t sin2t` (rational frequency, distributed sum so the
  forward round-trip certifies).
- **Summation.** `definite_sum` now routes geometric/hypergeometric via Gosper (`Σ_{0}^{3}2^k=15`,
  symbolic `Σ_{0}^{n}2^k=2^{n+1}−1`). New **`infinite_sum`**: convergent `Σ_{k}^{∞}` = `lim_{k→∞}S(k)
  − S(lower)` — geometric (`Σ2^{−k}=2`, via new `limit_geometric_decay`/`numeric_exp_rate` deciding a
  transcendental rate's sign numerically) and **p-series `Σ1/kˢ=ζ(s)`** (`Σ1/k²=π²/6`, `Σ1/k⁴=π⁴/90`).
- **Algebra.** `collect` (group terms by powers of a var); `expand_trig` (angle-addition/multiple-angle
  → trig form, `sin(2x)`, identity-certified); **multivariate quadratic factorization** `x²−y²=(x−y)(x+y)`,
  `x²±2xy+y²=(x±y)²` (new `rational_poly_sqrt` for the discriminant; certified by re-multiplication) —
  the first slice of the multivariate-factorization frontier.
- **Solve/limit/series.** `solve` `ln x=c⇒eᶜ`, `√x=c⇒c²`, polynomials in `eˣ`; the **`ln(exp u)=u`**
  zero-test fold; `limit` `x·ln x→0`; `series` for `asin`/`asinh`.
- **Special values & asymptotes.** Exact inverse-trig values (`atan(1)=π/4`, `asin(½)=π/6`, …);
  **erf/atan horizontal asymptotes at ±∞** (`limit_asymptotic_head`) — closes the **Gaussian**
  `∫_{−∞}^∞ e^{−x²}=√π` and `∫₀^∞1/(1+x²)=π/2`.

**433 unit + 143 doctests, clippy-pedantic clean, WASM-green.**

## 2026-07-21 — Entry 34: applied-math surface — Fourier, IVPs, numerics (439 tests)

Rounding out the *applied* mathematics surface a working analyst reaches for:

- **`∫sin(ax)sin(bx)`** via product-to-sum → the Fourier-orthogonality integrals `∫₀^{2π}sin2x·sin3x=0`,
  `∫₀^{2π}sin²3x=π`.
- **`fourier_series`** — Euler coefficients by exact `definite_integrate` over `[−L,L]`: `f(x)=x` on
  `[−π,π]` → `2sin x − sin2x + (2/3)sin3x`, `f(x)=x²` → `π²/3 − 4cos x + cos2x − …`.
- **`apply_initial_conditions`** — specialize a general ODE solution (constants `C0,C1,…`) to an IVP by
  solving the exact linear system in the constants (`collect_constant_names` + `ratint::solve_linear`):
  `y″+y=0, y(0)=1, y′(0)=0 ⇒ cos x`; `y′−y=0, y(0)=3 ⇒ 3eˣ`.
- **`numeric_integrate`** — composite Simpson for integrands with no elementary antiderivative
  (`∫₀¹e^{−x²}≈0.7468`, `∫₀¹sin(x²)≈0.3103`); **`nsimplify`** — recognize an f64 as a closed form
  (`1.5708→π/2`, `1.4142→√2`, `2.718→e`), the numeric→symbolic bridge.
- **`argument`** (complex phase, `arg(1+i)=π/4` across all quadrants); exact **inverse-trig** values
  incl. surds (`atan(√3)=π/3`, `asin(√2/2)=π/4`) in `evaluate_trig`; p-series `infinite_sum` at an
  arbitrary lower bound (`Σ_{2}^{∞}1/k²=π²/6−1`).

**439 unit + 143 doctests, clippy-pedantic clean, WASM-green.** Frontier remaining: Gamma/digamma
heads, general multivariate factorization, Puiseux, Zeilberger, Weierstrass/general Risch,
arbitrary-precision N[expr,d]. Known limitation: `normalize` (public poly normalizer) doesn't atomize
transcendentals, so `real_part`/`imaginary_part` decline surd complex coefficients.

## 2026-07-21 — Entry 35: integration & limit completeness wave (445 tests)

A sustained push closing the long tail of standard first/second-year integrals and limits, each
certified by differentiate-and-check:

- **Substitution family filled out.** `u=eˣ` for `∫R(eˣ)` (`∫1/(eˣ+1)=x−ln(eˣ+1)`, via
  `exp_to_power` + the `ln(eˣ)→x` fold); `u=x²` for odd-numerator/even-denominator rationals
  (`∫x/(x⁴+1)=½atan(x²)` — the ℚ-irreducible case the factoring path can't reach); the reverse
  power rule extended to the **n=1** bare-base case `∫g′·g=g²/2` (`∫atan x/(1+x²)=½atan²x`,
  `∫sin·cos`).
- **By-parts generalized.** `∫ln x·R(x)` for a rational cofactor (`∫ln x/x²=−ln x/x−1/x`) — with a
  recursion guard declining the `∫ln x/x` case (whose `V=ln x` reproduces the integrand; that's the
  reverse-power-rule `ln²x/2`). **Distributed products** `∫x·sinh x`, `∫(x+1)(eˣ+e^{−x})` — a
  `Mul`-with-`Add`-factor is distributed (folding a constant divisor into `1/c`), and
  `split_constant_factor` now pulls `−1` from a `Neg` factor.
- **Limits.** Linearity `lim(f+g)=lim f+lim g` (finite terms) — closes improper integrals of repeated
  irreducible quadratics `∫_{−∞}^∞1/(x²+1)ⁿ` (rational→0 + atan→π/2); the squeeze theorem
  (`sin x/x→0`); `lim exp(g)=exp(lim g)` + reciprocal substitution `x→1/t` (with `deep_normalize`) →
  the compound-interest limit `(1+1/x)^x→e`.
- Plus (Entry 34 surface): Fourier series, IVPs, `numeric_integrate`, `nsimplify`, complex `argument`,
  Gaussian `∫_{−∞}^∞e^{−x²}=√π`, sinusoid-product Fourier orthogonality, surd inverse-trig values.

**445 unit + 143 doctests, clippy-pedantic clean, WASM-green.** Frontier remaining (all large
subsystems): residue-based contour integration (complex poles), Gamma/digamma heads, general
multivariate factorization, Puiseux, Zeilberger, Weierstrass/general Risch, arbitrary-precision
N[expr,d], symbolic-coefficient series.

## 2026-07-22 — Entry 36: Weierstrass substitution + an exp-tower soundness fix (452 tests)

Took on a **substantial subsystem** rather than another edge case: the **Weierstrass substitution**
`t = tan(x/2)`, which closes the *entire class* of rational-trigonometric integrals `∫R(sin x, cos x)`
— `∫1/(1+cos x)=tan(x/2)`, `∫1/(a+b·cos x)`, `∫sec x`, `∫csc x`, `∫1/(sin x+cos x)`, … Every such
integrand becomes a rational function of `t` (via `sin x=2t/(1+t²)`, `cos x=(1−t²)/(1+t²)`,
`dx=2/(1+t²)dt`), integrated by the now-complete rational integrator and mapped back.

Getting there required two prerequisites:

- **A genuine soundness fix.** `exp(x/2)·exp(−x/2)` certified **FALSE** (it is `exp(0)=1`).
  `normalize_exp` bailed to distinct opaque atoms whenever the exp argument's rational normal form had
  denominator ≠ 1 — but `x/2` normalizes to `num x / den 2` (a *constant* denominator). Fix: absorb a
  constant denominator into the coefficients, so `exp(x/2)` keys on the primitive `exp((1/2)x)` and
  `exp(−x/2)=1/exp((1/2)x)`. Now half-angle identities like `1+tan²(x/2)=sec²(x/2)` decide too.
- **A half-angle certificate.** The cross-level relation `exp(x/2)²=exp(x)` still can't be captured by
  the `u32`-power atom representation, so the Weierstrass antiderivative (in `x/2` trig) can't be
  directly zero-tested against the integrand (in `x` trig). Added a `rewrite_double_angle` fallback in
  `prove_derivative`: rewrite full-angle `sin x→2sin(x/2)cos(x/2)`, `cos x→2cos²(x/2)−1` so both sides
  live at the `x/2` level, which the (now-fixed) zero-test decides.

**452 unit + 143 doctests, clippy-pedantic clean, WASM-green.** Rational-trig integration is now
complete. Frontier remaining (large subsystems): residue-based contour integration, Gamma/digamma
heads, general multivariate factorization, Puiseux, Zeilberger, general Risch, arbitrary-precision
N[expr,d], symbolic-coefficient series, and the whole Lean/Mathlib theorem-proving axis.

---

## 2026-07-21 — Entry 37: integration & series breadth wave (454 tests)

Five self-contained, certified additions across the calculus surface — each closing a class SymPy
covers that we declined on:

1. **Half-period rational-trig definite integrals** `∫₀^π R(sin,cos)`. `t=tan(x/2)` maps `[0,π]→[0,∞)`
   (vs. `[0,2π]→(−∞,∞)` for the full period), so the same Weierstrass→improper path handles both;
   `definite_full_period_rational_trig` now picks the `t`-bounds by which endpoint it sees. Closes
   `∫₀^π 1/(2+cos x)=π/√3`.
2. **Taylor about an arbitrary center with transcendental coefficients.** `series_at` about a nonzero
   center used to decline whenever a head's shifted argument left the rational-coefficient series ring
   (`exp(x)` about 1 needs coefficients `e/n!`). Added a `taylor_by_derivatives` fallback computing the
   Taylor definition `cₙ=f⁽ⁿ⁾(center)/n!` — coefficients are arbitrary closed-form constants (`e`,
   `sin(1)`, `√3/2`). Declines on a pole (non-finite coefficient). `exp` about 1 → `e·[1+(x−1)+…]`.
3. **Gaussian moments** `∫P(x)·e^{−ax²}` over `(−∞,∞)`/`[0,∞)` (non-elementary antiderivative). Reduce
   to `√π` multiples of the erf-certified base `I₀=∫e^{−ax²}` via `∫x^{2m}e^{−ax²}=(2m−1)!!/(2a)^m·I₀`
   (and the half-interval odd formula `m!/(2a^{m+1})`, elementary). `∫_{−∞}^∞ x²e^{−x²}=√π/2`,
   `x⁴e^{−x²}=3√π/4`. Perfect-square `a` only (the base needs rational `√a`); else declines honestly.
4. **Dirichlet/Fresnel improper integrals.** Added the horizontal asymptotes `Si(±∞)=±π/2`, `Ci(+∞)=0`,
   `FresnelS/C(±∞)=±½` to `substitute_asymptotic_heads` → `∫₀^∞ sin x/x=π/2`, `∫₀^∞ sin(πx²/2)=½`.
   Folded the odd integral-functions (Si/Shi/FresnelS/C/asin/asinh) to 0 at the origin (Ci/Ei/Chi
   excluded — they diverge there), and made that fold `simplify` its argument first so `Si(2·0)→Si(0)→0`
   (needed for `sin(2x)/x` to both fold *and* certify).
5. **Combining-log improper boundaries.** Rational-function antiderivatives routinely have log terms that
   individually diverge at ±∞ but combine to a finite limit (`∞−∞`). `limit_log_sum_at_infinity`
   flattens the sum and uses `ln Pᵢ ~ degᵢ·ln|x|+ln|leadᵢ|`, so the limit is finite iff `Σcᵢ·degᵢ=0`,
   value `Σcᵢ·ln|leadᵢ|` + the non-log terms' limits. Plus: run the definite/improper boundary value
   through `evaluate_trig` so special-angle inverse-trig endpoints fold (`atan(−1/√3)→−π/6`). Closes
   `∫₀^∞ 1/(1+x³)=2π/(3√3)`, `∫₀^∞ 1/((x+1)(x+2))=ln 2`, `∫₀^{√3} 1/(1+x²)=π/3`.

**454 unit + 143 doctests, clippy-pedantic clean, WASM-green.**

**Entry 37b — quartic denominators + the surd combining-log completion (same 454-test count; +3 features):**
- **`factor` now returns the full ℚ-irreducible factorization.** It peeled rational-root linear
  factors then dumped the degree-≥2 residual whole; now that residual is routed through the complete
  Berlekamp–Zassenhaus `factor_expr`, so `x⁴+x²+1=(x²+x+1)(x²−x+1)`, `x⁴+4=(x²+2x+2)(x²−2x+2)`.
- **`∫ k/(x⁴+px²+q)` via the real (surd) quadratic factorization** (`integrate_even_quartic_denominator`),
  which lies beyond the ℚ-partial-fraction path. Case A (`p²<4q`): `D=(x²+αx+β)(x²−αx+β)`, `β=√q`,
  `α=√(2β−p)`, decomposition `A=1/(2αβ), B=1/(2β)` → `ln`+`atan` (shared `√(2β+p)`). Case B (`p²>4q`,
  `p>0`): `D=(x²+β₁)(x²+β₂)` → `atan/√βᵢ`. Constant numerator, backed by `prove_derivative` (the surd
  zero-test verifies the `√`-atoms; a nested-surd `α=√(2√q−p)` case like `x⁴+2` declines honestly). The
  constructed antiderivative is `fold_elementary_constants`+`simplify_radicals`'d so `√(2·√1−0)` keys as
  the canonical `√2` atom (else the zero-test sees an opaque unrelated atom and rejects). Closes
  `∫1/(x⁴+1)`, `∫1/(x⁴+9)`, `∫1/(x⁴+16)`.
- **Surd-coefficient combining-logs** → the famous `∫_{−∞}^∞ 1/(x⁴+1)=π/√2`. Generalized
  `limit_log_sum_at_infinity` from rational to symbolic coefficients: the real factors give log terms
  whose polynomials (`x²±√2x+1`) have surd middle coefficients but *rational leading coeff* (=1). New
  `poly_leading_in_var` (degree+leading via `monomial_degree_coeff`, surd-tolerant) and
  `parse_log_polynomial_term` (CasExpr coefficient); the convergence test `Σcᵢ·degᵢ=0` is now the
  symbolic zero-test. `flatten_add_terms` gained `Neg`/constant-`Div` distribution and the handler
  `expand`s first, so `c·(lnP−lnQ)` and `(…)/c` split into per-log terms.

Known next gaps: general-`a` Gaussian (surd `√a` erf antiderivative), nested-surd quartics (`x⁴+2`).
Non-integration frontier unchanged: multivariate factorization, Puiseux, Zeilberger, ℚ(i) as a
first-class type, Gamma/digamma heads (polygamma tower), the Abs/sign assumptions layer, and the
Lean/Mathlib axis.

---

## 2026-07-21 — Entry 37c: even-numerator quartics, summation & limit polish (455 tests)

Continuing the breadth push across three branches:
- **Even-numerator quartics** — generalized `integrate_even_quartic_denominator` from constant to
  `n₂x²+n₀`: Case A gets `B=n₀/(2β)`, `A=(n₀/β−n₂)/(2α)`; Case B gets `P=(n₀−n₂β₁)/(β₂−β₁)`,
  `Q=(n₂β₂−n₀)/(β₂−β₁)`. Closes `∫x²/(x⁴+1)` and the improper `∫_{−∞}^∞ x²/(x⁴+1)=π/√2`. Odd
  numerators still decline (handled by `u=x²`).
- **Geometric base from any exponent spelling** (`gosper::geometric_base`) — it required the exponent
  to be literally `var·ln(Const)`, so `2^{−k}=exp(−k·ln2)` and other `Neg`/multiplier spellings were
  rejected. Now recovers the coefficient `a` of `var` by differentiation (**simplified** — the raw
  derivative carries `var·(…·0)` noise that structurally still mentions `var`) and sets `base=exp(a)`,
  accepting any equivalent exponent when `exp(a)` is a positive rational. Closes `Σ_{k≥0}2^{−k}=2`,
  `Σ 3^{−k}=3/2`, `Σ k·2^{−k}=2`.
- **Limit log-vs-power at +∞** (`limit_log_at_infinity`, dual of `limit_log_at_zero`) — a positive
  power of `x` beats any power of `ln x`, so `ln x/x→0`, `(ln x)²/x→0`, `1/ln x→0`, and
  `x^{1/x}=exp((ln x)/x)→1` via the exp-of-limit path. Divergent forms (`x/ln x`, `x·ln x`) decline.

**455 unit + 143 doctests, clippy-pedantic clean, WASM-green.**

**Entry 37d — conjugate limits at +∞ (456 tests).** Closed the item deferred above, but via
*conjugate rationalization* rather than a full Puiseux-at-∞ engine (which the reciprocal substitution
would have needed). `algebraic_leading_at_infinity` gives the `(order, coefficient)` of any
polynomial/`√`-polynomial expression (`√P → order deg/2, coeff √lead`), summing coefficients at the
top order and declining on cancellation. `limit_algebraic_at_infinity` tries that ratio directly
(`√(x²+1)/x=1`); when a `√`-sum's leading terms cancel (`√(x²+x)~x`, minus `x`), it rationalizes —
`S+R = (S²−R²)/(S−R)` — building the numerator polynomial `m²A−R²` **directly** (squaring `√A` does
not auto-fold in `simplify_radicals`), then re-runs the leading-term ratio. Handles `√A ± polynomial`
and `√A ± √B`. Closes `√(x²+x)−x=½`, `√(4x²+x)−2x=¼`, `√(x²+x)−√(x²−x)=1`, `√(x+1)−√x=0`.

---

## 2026-07-22 — Entry 37e: ODE gaps (still 456 tests; +2 features)

- **Constant-coefficient homogeneous ODEs with surd roots.** `dsolve_homogeneous`'s leftover-quadratic
  tail required a *rational* `β` (`rational_sqrt`), so a complex pair with a surd `β` (`x²+x+1 →
  −½±(√3/2)i`) declined — blocking degree-3 char polys like `x³−1`. Now the complex branch keeps `β`
  symbolic (`√(−disc)/2a`), and a new `disc>0` branch emits the two real-irrational-root exponentials
  `e^{(α±√·)x}`. The substitute-and-check certificate applies `simplify_radicals∘simplify` to the
  operator so the higher derivatives of a surd-trig basis fold and certify. Closes `y‴−y=0`, `y‴+y=0`,
  `y″−2y=0` (±√2), `y″+y′+y=0`. (Two irreducible quadratics — `x⁴+1` — still declines.)
- **First-order linear ODEs with variable/resonant coefficients.** (1) `p=k/x` gave `μ=exp(k·ln x)`
  which never folded — added `rewrite_exp_log` (`exp(c·ln u)→u^c` for integer `c`, the dual of
  `rewrite_log_exp`) applied to `μ` and `e^{−P}`. (2) Resonant forcing `y′−y=eˣ` left `eˣ·e⁻ˣ`
  unevaluated so `∫` failed — try the raw `μ·q` integrand first, fall back to its simplified form
  (which collapses `eˣ·e⁻ˣ=1` but also rewrites `exp(2x)→exp(x)²`, so raw must win when it works).
  Closes `y′+y/x=1` (`μ=x`), `y′+2y/x=x` (`μ=x²`), `y′−y=eˣ`.

---

## 2026-07-22 — Entry 37f: nsimplify surds/logs + inverse Laplace repeated poles (456 tests)

Two more parity fills:
- **`nsimplify` quadratic surds & ln(rational).** Added `(a+√b)/c` recognition (via `(c·value−a)²=b`
  over small `a,c` with `b` a non-square) — closing the golden ratio `(1+√5)/2` and `1+√2` — and
  `ln(r)` for a positive rational `r≠1` (via `r=exp(value)`) — closing `ln2`, `ln3`. Both verified by
  `evalf` reconstruction, so random values still decline.
- **`inverse_laplace` repeated real poles.** It handled only distinct simple poles or one irreducible
  quadratic, so `1/s²` declined. `inverse_laplace_repeated_poles` partial-fractions via `apart` and
  maps each `C/(s−a)^k → (C/lead)·t^{k−1}/(k−1)!·e^{at}` (checking `den = lead·(s−a)^k` by
  reconstruction). Closes `1/s²→t`, `1/s³→t²/2`, `1/(s−1)²→t·e^t`, and mixed `1/(s²(s−1))→e^t−1−t`.
  Round-trip certified.

---

## 2026-07-22 — Entry 37g: inhomogeneous ODEs via variation of parameters (457 tests)

`dsolve_inhomogeneous` handled only polynomial forcing. Added a 2nd-order **variation of parameters**
fallback for arbitrary integrable forcing: extract the homogeneous basis `y₁,y₂` (substitute `C0,C1`;
**`fold_trivial`, not `simplify`** — the latter rewrites `e^{−x}→1/eˣ`, which the integrator can't
invert), Wronskian `W`, then `y_p = y₁∫(−y₂g/aW) + y₂∫(y₁g/aW)`. A new **`merge_exp_products`** combines
exponential products/quotients into an integrable form (`eˣ·e^{−x}=1`, `e^{2x}/e^{3x}=e^{−x}`, and
crucially **not** `e^{2x}→exp(x)²` which `simplify` does and `integrate` rejects). Closes exponential
forcing including resonance (`y″−y=eˣ`, `y″−3y′+2y=eˣ`, `y″−2y′+y=eˣ`) and trig forcing over a complex
basis (`y″+y=sin x`, `y″+4y=sin 3x`). Known limitation: trig forcing over a **real-exponential** basis
(`y″−y=cos x`) still declines — `simplify` pushes the `e^{−x}` integrand into a denominator. Certified
by substitution.

---

## 2026-07-22 — Entry 37h: trig equation solving — surd RHS & polynomial-in-trig (457 tests)

- **Surd right-hand side.** `solve_trigonometric` accumulated the non-trig part as a `Rational` (via
  `constant_term`), so `2cos x − √3 = 0` declined. Now it accumulates a `CasExpr` (classifying terms by
  `expr_contains_var`), forms the target `f(var) = −C/A` symbolically, and matches the special-angle
  table via the zero-test. Closes `2cos x−√3⇒{π/6,11π/6}`, `2sin x−√2⇒{π/4,3π/4}`.
- **Polynomial in a trig head.** `solve_polynomial_in_trig`: substitute `sin(var)→u` (structural
  `replace_subexpr`), require a degree-≥2 polynomial with no residual `var`, solve `P(u)=0`, then invert
  `sin(var)=u₀` for each real root (out-of-range/complex roots yield no angles). Closes `sin²x=¼`,
  `2sin²x−3sin x+1=0`, `2cos²x−1=0`.

Also this entry: **surd tan** (`tan x=√3`) — the special-angle scan skipped any `Unary`-headed value to
dodge tan poles, but `√3` is `Unary(Sqrt)`, so surd targets landing on a bare `√` were wrongly skipped;
narrowed the skip to unevaluated *trig* heads. And **multiple-angle** `f(m·var)` (`sin 2x=0`,
`sin 3x=0`): extract the integer frequency `m`, scan `θ∈[0,2π)` for `f(θ)=target`, emit
`var=((θ_coeff+2j)/m)·π` for `j=0..m` as clean `r·π`.

**Gamma integrals** (Entry 37i): `improper_gamma_integral` decomposes `c·x^p·e^{−x}` (`extract_gamma_form`
handles `√x`, so `p` can be half-integral) and returns `c·Γ(p+1)` via `special::gamma`'s closed forms —
`∫₀^∞ e^{−x}/√x=Γ(1/2)=√π`, `∫₀^∞ √x·e^{−x}=Γ(3/2)=√π/2`, the half-integer cases with no elementary
antiderivative.

**Beta integrals** (Entry 37j): `definite_beta_integral` decomposes `c·x^p·(1−x)^q` (`extract_beta_form`
recognises `x`, `1−x`, `√x`, `√(1−x)`, and `√` of a product `√(x(1−x))=√x·√(1−x)`) and returns
`c·B(p+1,q+1)` via `special::beta` — `∫₀^1 1/√(x(1−x))=B(½,½)=π`, `∫₀^1 √x/√(1−x)=π/2`. Only fires for
fractional powers (integer powers stay on FTC). (Cosmetic: `simplify_radicals` doesn't fold
`Pow(Sqrt(Var),2)→Var`, so `B(½,½)` prints as `sqrt(pi)^2` though it certifies `= π`.)

**Bivariate power factorization** (Entry 37k): `factor_binomial_powers` — `xⁿ−yⁿ=(x−y)Σx^{n−1−k}yᵏ`, odd-`n` `xⁿ+yⁿ=(x+y)Σ(−1)ᵏx^{n−1−k}yᵏ`, certified by re-multiplication; `x³−y³`,`x⁵+y⁵`,`2x³−2y³`. Plus a `simplify_radicals` fix: fold `(√u)^{2k}→u^k` (was missing on the `Pow` case, so `√π²` didn't reduce).

---

## 2026-07-22 — Entry 37l: sign/floor/ceiling head family (458 tests)

Took on a **new head subsystem** (the assumptions/piecewise-constant axis). `Abs` already existed;
added `Sign`, `Floor`, `Ceiling` as first-class `UnaryFunc` heads — the memory's "adding a head = 4
exhaustive match sites" pattern held exactly (`name`, `UnaryFunc::differentiate` → `0` since they're
locally constant, `evalf` → `signum`/`floor`/`ceil` with `sign(0)=0` corrected from f64's `signum`, and
`series::unary_series` → decline). Builders `.sign()`/`.floor()`/`.ceiling()` fold a rational constant
(`⌊−7/2⌋=−4`, `⌈−7/2⌉=−3` via `div_euclid`; `sign(±c)=±1`, `sign(0)=0`). `fold_elementary_constants`
re-folds them after a substitution, and `simplify_under_assumptions` resolves `sign(x)→±1/0` once the
assumptions engine fixes the argument's sign (SymPy `refine`). NOTE: the natural next step in this axis —
a `Piecewise` data model, and symbolic `Gamma`/`digamma`/`polygamma` — both need a **data-model change**
(a new `CasExpr` variant / a 2-arg indexed head), touching every match site; deferred as a deliberate,
scoped effort rather than a risky mid-session refactor.

**Frullani integrals + a soundness fix** (Entry 37m): `∫₀^∞(cos x−cos 2x)/x` wrongly returned `0` — the antiderivative `Ci(x)−Ci(2x)` at the lower bound `0` unsoundly cancelled `Ci(0)−Ci(0)`, but `Ci(z)~γ+ln|z|` so the combination is `−ln2`. Added `limit_singular_integral_sum_at_zero` (`Σcᵢ·Hᵢ(aᵢx)`, `H∈{Ci,Ei,Chi}`, converges iff `Σcᵢ=0` → `Σcᵢ·ln|aᵢ|`) and routed the improper/definite finite boundary through `limit` when the antiderivative has a log-singular head (`contains_singular_integral_head`). Plus `Ei(−∞)=0`. Closes the Frullani family. **(This is the kind of ∞−∞ cancellation a proof-carrying CAS must get right — declining, not guessing 0.)**

**Limit polish** (Entry 37n): (1) `limit_via_series` now `cancel`s first so the `(1/g)·f` (Mul) spelling reduces like `f/g` (Div) — `(1/x²)ln(cos x)→−½`, hence `(cos x)^{1/x²}→e^{−½}`. (2) `limit_lhopital` — a 0/0 quotient with `f(a)=g(a)=0` returns `lim f′/g′` (up to depth 4), reaching forms the rational-coefficient series can't: `(aˣ−1)/x→ln a` (the numerator's derivative carries a transcendental `ln a`). Uses the *raw* quotient (cancel atomizes exp/ln). Non-0/0 and `g′(a)=0` poles decline.

**Log arithmetic in the zero-test** (Entry 37o): many integral results are sums of `ln(rational)` that didn't certify against a compact form (`∫₁² 1/(x(x+1)) = 2ln2−ln3` vs `ln(4/3)`, read as distinct atoms). `expand_log_over_primes` rewrites `ln(p/q)` into its prime basis `Σeᵢln(pᵢ)−Σfⱼln(qⱼ)` (`ntheory::factorize`), applied in `equal`'s canonicalization. So `ln6=ln2+ln3`, `3ln2=ln8`, `ln(1/2)=−ln2` decide — while distinct logs (`ln2` vs `ln3`) still don't certify (sound).

**Transcendental residues** (Entry 37p): `residue` handled only rational functions; `residue_meromorphic` computes `Res f(x)/(x−a)ⁿ = f^{(n−1)}(a)/(n−1)!` for an analytic (transcendental) numerator over a pure power — `Res₀ cos x/x=1`, `eˣ/x²=1`, `sin x/x⁴=−1/6`, `Res₁ eˣ/(x−1)²=e`.

**Fourier integrals via residues** (Entry 37q): `improper_fourier_quadratic` — `∫_{−∞}^∞ N(x)·{cos,sin}(ax)/(x²+q)` (`q>0`, `a>0`, `deg N≤1`) via the residue theorem (pole at `i√q`); by parity `∫(c₁x+c₀)cos(ax)/(x²+q)=c₀(π/√q)e^{−a√q}`, `·sin=c₁·π·e^{−a√q}`. `find_linear_trig` peels the oscillatory factor. Certified by construction (residue theorem exact; cross-checked numerically). `∫cos x/(x²+1)=π/e`, `∫x sin x/(x²+1)=π/e`, `∫cos2x/(x²+1)=π/e²`. **First genuine contour-integration capability.**

**QR decomposition** (Entry 37r): `qr_decomposition` reuses `gram_schmidt`+`norm` — orthogonalize A's columns, normalize to Q (surd entries), `R=QᵀA`; reconstruction `Q·R=A` and orthonormality `QᵀQ=I` certified by the zero-test (surds decided). Declines rank-deficient inputs.

**Cholesky** (Entry 37s): `cholesky_decomposition` — `A=L·Lᵀ` for symmetric positive-definite `A` (diagonal `√`, checked `>0` via `evalf`), certified `L·Lᵀ=A`. `[[4,2],[2,2]]→[[2,0],[1,1]]`; surds; non-PD/non-symmetric decline.

**Half-line Fourier integrals** (Entry 37t): extended `improper_fourier_quadratic` to the half-line `[0,∞)` when the integrand is **even** (`function_parity == Even`) — then `∫₀^∞ = ½∫_{−∞}^∞`. So `∫₀^∞ cos x/(x²+1)=π/(2e)`, `∫₀^∞ cos2x/(x²+1)=π/(2e²)`, and `∫₀^∞ x·sin x/(x²+1)=π/(2e)` (`x·sin x` is even). Parity is the exact soundness guard: an odd/asymmetric integrand still declines on `[0,∞)` (its half-line value is *not* half the symmetric one). Certified by construction (residue theorem) + the zero-test.

**Zero-test folds |u|²=u² → indefinite ∫|affine|** (Entry 37qq): taught the zero-test the abs relation `|u|² = u²` (real domain), mirroring the existing `(√u)² = u` `fold_radical`. New `MultiPoly::fold_abs(abs_args)` reduces even powers of an `abs` atom (`|u|^{2k}→u^{2k}`, `|u|^{2k+1}→u^{2k}·|u|`); the zero-test builds an `abs_args` dict (atom key → normalized argument) alongside `radicands` and chains it. Sound: `|x|²=x²`, `x²/|x|=|x|`, `|x|³=x²|x|` certify, while `|x|=x`, `|x|=−x`, `|x|²=x³` stay undecided (verified). This unlocks the **indefinite** `∫|ax+b| = (ax+b)|ax+b|/(2a)` — new `integrate_abs_affine` finder, verified by differentiate-and-check now that `d/dx(x|x|/2)=(|x|+x²/|x|)/2=|x|` certifies via `x²/|x|=|x|`. `∫|x|=x|x|/2`, `∫3|x|`, `∫|2x−4|`.

**min / max / Heaviside** (Entry 37pp): `minimum(a,b)=(a+b−|a−b|)/2`, `maximum(a,b)=(a+b+|a−b|)/2`, `heaviside(x)=(1+sign(x))/2` — all built from the existing `abs`/`sign` heads (no new data-model variant), folding to the concrete value on constants (`min(3,5)=3`, `H(−2)=0`, `H(0)=½`). Because they are `abs`-based, they **compose with the piecewise integrator**: `∫₀^2 min(x,1)=3/2`, `∫₀^2 max(x,1)=5/2` fall out for free (the `|x−1|` splits at `x=1`). SymPy `Min`/`Max`/`Heaviside` parity. (The zero-test still doesn't fold `abs(constant)`, so evaluating a symbolic min at a point needs `fold_elementary_constants` — the same `|·|`-atom limitation.)

**Definite integrals of |sin|/|cos|** (Entry 37oo): completed the abs-integration family with `abs(sin(affine))`/`abs(cos(affine))` — `definite_integrate_abs_periodic` splits at the periodic trig zeros (`sin(g)=0` at `g=kπ`, `cos(g)=0` at `g=(k+½)π`, solving `slope·x+intercept=mπ` for the exact `CasExpr` breakpoint), then on each piece replaces the `abs` by `±` the trig and integrates via FTC. `∫₀^π |sin x|=2`, `∫₀^{2π} |sin x|=4`, `∫₀^{2π} |cos x|=4`, `∫₀^{2π} |sin 2x|=4`, and polynomial × abs-trig `∫₀^π x·|sin x|=π`. (A runaway breakpoint range declines.)

**sign / Heaviside integrals** (Entry 37rr): `definite_integrate_sign` completes the step-function family — `sign(g)` with `g` affine (and thus `heaviside(g)=(1+sign(g))/2`) splits at `g`'s root and replaces `sign(g)` by `±1` on each side. `∫_{−1}^1 sign(x)=0`, `∫₀^3 sign(x−1)=1` (`−1` then `+1`), `∫₀^2 H(x−1)=1`, `∫₀^2 H(x−1)·x=3/2`. Together with the abs/floor/periodic handlers the whole `{abs, floor, ceiling, sign, heaviside, min, max}` piecewise-integration surface is now covered.

**Definite integrals of step functions** (Entry 37nn): extended the piecewise machinery to `floor(g)`/`ceiling(g)` with `g` affine — `definite_integrate_step_function` splits the interval at every point where `g` crosses an integer (`x_k=(k−intercept)/slope`), and on each piece replaces the step head by its constant integer value there, integrating exactly. `∫₀^3 floor(x)=3`, `∫₀^3 ceil(x)=6`, `∫_{−2}^2 floor(x)=−2`, `∫₀^4 floor(x/2)=2`, `∫₀^3 x·floor(x)=13/2`. Also added `univariate_affine` (extract `[intercept, slope]` via `normalize_rational` so a `Div`-by-constant like `x/2` is handled — `normalize` alone returns None on `Div`), which also fixed the abs path for scaled arguments (`∫₀^2 |x/2−1|=1`).

**Definite integrals of |affine|** (Entry 37mm): `∫|x|` and `∫sign(x)` have no zero-test-certifiable antiderivative (the zero-test doesn't know `|x|²=x²`), so the FTC path can't reach them. Added `definite_integrate_abs`: for an integrand containing `abs(g)` with `g` affine in the variable (`find_affine_abs`), split the interval at `g`'s root (its sign change) and on each piece replace `abs(g)` by `±g` (the definite sign there), integrating each piece exactly with `definite_integrate`. Each piece is certified, so the sum is exact. `∫_{−1}^1 |x|=1`, `∫₀^2 |x−1|=1`, `∫_{−1}^2 x·|x|=7/3`, `∫₀^3 |2x−4|=5`, `∫_{−1}^1 (|x|+x²)=5/3`. Nested/multiple `abs` handled by recursion (each piece re-enters for the next breakpoint); constant-sign intervals need no split.

**Multiple-angle cancellation in simplify** (Entry 37ll): added `cancel(expand_trig(·))` as a size-competing `simplify` candidate — it expands multiple-angle heads (`sin 2x → 2 sin x cos x`) then re-combines, so terms that cancel only *after* expansion collapse. This cleans variation-of-parameters output: the resonance ODE `y″+y=sin x` now returns `−½x·cos x + C₀cos x + C₁sin x` (was `−½cos²x·sinx + ¼cosx·sin2x − ½x·cosx + …`, correct but verbose — the residual `−½cos²x·sinx + ¼cosx·sin2x` is `0`). Chosen only when strictly smaller, so `sin(2x)`/`cos(2x)` themselves are left unexpanded (the expanded form is larger).

**Iterated (multiple) integrals** (Entry 37kk): `iterated_integral(f, &[(var, lower, upper), …])` — integrates inside-out over the bounds listed outer-to-inner, each stage via the certified `definite_integrate`. Because the bounds are arbitrary `CasExpr`, an inner bound may depend on an outer variable, so **non-rectangular regions** work: `∫₀^1 ∫₀^x (x+y) dy dx = 1/2`, triangle area `∫₀^1 ∫₀^x 1 = 1/2`, unit-cube triple `∫₀^1³ xyz = 1/8`, and plain rectangles `∫₀^1 ∫₀^2 xy = 1`. The multivariable `Integrate[f,{x,a,b},{y,c,d}]` parity capability.

**Repeated-root recurrences** (Entry 37jj): `solve_recurrence` handled distinct positive-rational roots (Vandermonde) and the order-2 quadratic-irrational (Fibonacci/Binet) but declined on **repeated roots** — because `ratint::rational_roots` returns distinct roots, so the count never reached `order`. Added `rational_root_multiplicity` (counts consecutive derivatives vanishing at the root) and `solve_recurrence_repeated_rational`: a root `r` of multiplicity `m` contributes the basis `rⁿ, n·rⁿ, …, n^{m−1}·rⁿ`, amplitudes fixed by the linear solve over columns `jᵖ·rʲ`, certified by substitution into the recurrence. So `aₙ=2aₙ₋₁−aₙ₋₂ (a₀=0,a₁=1) → n`, `aₙ=4aₙ₋₁−4aₙ₋₂ (a₀=0,a₁=2) → n·2ⁿ`, triple root `aₙ=3aₙ₋₁−3aₙ₋₂+aₙ₋₃ → n²`.

**Orthogonal polynomials** (Entry 37ii): added the five classical families as exact `CasExpr` polynomials via their three-term recurrences (shared `orthogonal_recurrence` helper, expanding at each step): `legendre_polynomial` `(n+1)Pₙ₊₁=(2n+1)xPₙ−nPₙ₋₁` (`P₂=(3x²−1)/2`), `hermite_polynomial` (physicists', `Hₙ₊₁=2xHₙ−2nHₙ₋₁`, `H₃=8x³−12x`), `chebyshev_t_polynomial` (`Tₙ₊₁=2xTₙ−Tₙ₋₁`, `T₃=4x³−3x`, `Tₙ(cos θ)=cos nθ`), `chebyshev_u_polynomial`, and `laguerre_polynomial` (`(n+1)Lₙ₊₁=(2n+1−x)Lₙ−nLₙ₋₁`). A classic SymPy/Mathematica capability (`legendre`, `hermite`, `chebyshevt/u`, `laguerre`) that was absent; CONSOLIDATED into the pre-existing `orthopoly` module (the earlier lib.rs `*_polynomial` duplicates were removed once `orthopoly.rs`, which already had legendre/hermite/chebyshev_t/u/laguerre, was discovered). Also added `gegenbauer(n, λ, var)` — the ultraspherical family with a rational parameter `λ` (`(k+1)Cₖ₊₁=2(k+λ)xCₖ−(k+2λ−1)Cₖ₋₁`), which generalizes them: `λ=1`→Chebyshev `Uₙ`, `λ=½`→Legendre `Pₙ` (both verified by the zero-test). And `jacobi_polynomial(n, α, β, var)` — the most general classical family (weight `(1−x)^α(1+x)^β` on `[−1,1]`), from which Legendre (`α=β=0`, verified), Gegenbauer, and Chebyshev all specialize; declines on a degenerate parameter (vanishing recurrence denominator). The full classical orthogonal set is now present. Plus `generalized_laguerre_polynomial(n, α, var)` — the associated Laguerre `Lₙ^{(α)}` (weight `xᵅe^{−x}`, hydrogen radial wavefunctions), reducing to ordinary Laguerre at `α=0`.

**Transcendental Laurent series** (Entry 37hh): `series_at` now expands a ratio with a **pole** at the center — `D` vanishes to order `m`, `N` to order `k<m`, principal part of order `p=m−k`. New `laurent_ratio_at_origin` cancels the common `xᵏ`, divides the two regular series, and shifts the regular quotient down by `p` to emit negative-power terms (built by `build_power_term`). Runs as a fallback after the regular/removable series path, before `taylor_by_derivatives`. Covers `1/sin x = 1/x + x/6 + 7x³/360`, `1/(eˣ−1) = 1/x − 1/2 + x/12 − …`, `cot x = 1/x − x/3 − x³/45`, double poles `1/(x·sin x) = 1/x² + 1/6 + …` — numerically verified against ground truth. `1/x` now returns its Laurent series `1/x` (was a decline); a branch point (`ln x` at 0) still declines (no Laurent).

**Series of a removable-singularity ratio** (Entry 37gg): `series_at` on `N(x)/D(x)` used to require `D(0)≠0`, so it MISSED ratios where numerator and denominator both vanish at the center but the ratio is regular. Now the `Div` case finds the denominator's lowest nonzero order `m`, requires the numerator to vanish to at least order `m` (else a genuine pole → decline), and cancels the common `xᵐ` from both coefficient sequences (computing `order+m` terms so `order` survive the shift). Closes the **Bernoulli generating function** `x/(eˣ−1) = 1 − x/2 + x²/12 − x⁴/720`, plus `sin(x)/x = 1 − x²/6 + …`, `(1−cos x)/x² = 1/2 − x²/24`, `x²/(eˣ−1)`. A true pole (`1/x`, numerator nonzero) still declines — Laurent, not Taylor.

**Log/exp positivity identities under assumptions** (Entry 37ff): `simplify_under_assumptions` (the `refine` engine) gained the log/exp inverse identities it was missing. `exp(ln u) = u` and `ln(uᵏ) = k·ln u` fold **only when `u > 0`** (`assumptions.is_positive`) — the real-branch conditions; `ln(exp u) = u` folds always. So under `x>0`: `exp(ln x)→x`, `ln(x³)→3 ln x`; without a positivity assumption `exp(ln x)` and `ln(x²)` are left intact (folding them would be unsound — e.g. `ln(x²)=2 ln|x|`, not `2 ln x`, for `x<0`). This is exactly SymPy's `refine`/`logcombine` positivity gating. Extended with `ln(u·v)=ln u+ln v` (every factor positive) and `ln(u/v)=ln u−ln v` (both positive) — so `ln(xy)→ln x+ln y`, `ln(3x)→ln 3+ln x` under `x,y>0`. All the log/exp identities live in a factored `refine_log_exp` helper.

**fold_trivial folds product sign** (Entry 37ee): `fold_trivial`'s `Mul` loop now flips the running constant sign on a `Neg` factor — `(−1)·(−x) → x`, `−2·(−3x) → 6x` — a safe canonicalization (chosen via the `simplify` candidate mechanism). (A stronger `Div`-numerator sign-pull `(−a)/b → −(a/b)`, which would also clean `L{t·eᵗ} = −((−1)/(s−1)²)` to `1/(s−1)²`, was explored but reverted — it changed canonical forms that integration certification depends on, breaking 3 tests. The `t·eᵗ` Laplace output stays in its correct-but-unfolded form.)

**simplify normalizes function arguments** (Entry 37dd): `simplify` treated a function head as an opaque atom, so identity junk *inside* a trig/transcendental argument survived — `sin(1·t)`, `cos(0+t)`, `sin(2·(1·t))` were left verbatim (only cosmetic — the zero-test canonicalizes atoms, so `equal(sin(1·t), sin(t))` already certified). Fixed by adding `fold_trivial` (which recurses into head arguments, folding `1·x→x`, `0+x→x`) as a size-competing candidate in `simplify` — chosen only when strictly smaller, so it can never de-simplify. Cleans up transform/inverse-transform output: `L⁻¹{1/(s²+1)} = sin(t)` (was `1·sin(1·t)`), `L⁻¹{s/(s²+4)} = cos(2t)`.

**Laplace division/negation linearity** (Entry 37cc): `laplace_transform` gained two linearity cases it was missing — `L{f/c} = (1/c)L{f}` (top-level division by a constant) and `L{−f} = −L{f}` (a `Neg` term). Together these transform the hyperbolic functions from their exponential form: `L{cosh t}=L{(eᵗ+e⁻ᵗ)/2}=s/(s²−1)`, `L{sinh t}=L{(eᵗ−e⁻ᵗ)/2}=1/(s²−1)`, `L{sinh 3t}=3/(s²−9)` — previously a flat MISS (the `Div`/`Neg` node fell through to the `_ => None` catch-all). `L{−eᵗ}=−1/(s−1)`.

**Symbolic constant-multiple integration** (Entry 37bb): `integrate` now pulls a **var-free symbolic** factor out of a product/quotient — `∫ c·g = c·∫g` for `c ∈ {π, √2, a parameter y, …}`, not just the rational constants `split_constant_factor` already handled. New `split_var_free_factor` partitions a `Mul`/`Div` (recursing through the numerator, handling `Neg`) into (var-free, var-dependent); the rule integrates the dependent core and re-attaches `c`, certified by differentiate-and-check. So `∫ π·sin x = −π cos x`, `∫ π·sin x/(1+cos²x) = −π·atan(cos x)`, `∫ √2·x² = (√2/3)x³`, `∫ y·cos x = y sin x`. Terminates (the extracted core has no further var-free factor). This was the gap the reverted x-weighted King's-rule attempt had exposed (`∫ π·h(sin x)` missed).

**Even/odd trig folding + reflection integrals** (Entry 37aa): two coupled additions. (1) `evaluate_trig` now folds negated arguments via a new `strip_negation` helper: `cos(−u)=cos u` (even), `sin(−u)=−sin u`, `tan(−u)=−tan u`, `atan/asin(−u)=−(…)` (odd) — a general simplification gap (SymPy folds these). This completes the co-function reduction: `sin(π/2−x) → cos x` now falls out of `expand_trig`+`evaluate_trig`. (2) `definite_reflection_symmetry` — **King's rule** `∫_a^b f = ∫_a^b f(a+b−x)`, so when `f(x)+f(a+b−x)` reduces to a constant `C`, the integral is `C·(b−a)/2`. A genuine proof, not a lookup: the reflected sum is reduced by identity-preserving transforms only (new `rewrite_tan_as_sin_cos`, new `distribute_trig_args` — which splits `(π−2x)/2 → π/2−x` via `expand` so `expand_trig` can decompose it — then `expand_trig`/`evaluate_trig`/`simplify`); a var-free reduced form certifies constancy, and a numeric quadrature guards integrability. Handles the classics `∫₀^{π/2} 1/(1+tanⁿ x)=π/4`, `∫₀^{π/2} sinⁿ/(sinⁿ+cosⁿ)=π/4`.

**Exponential frequency integral** (Entry 37z): `improper_exp_sinc_integral` — the Laplace transform of the sinc kernel `∫₀^∞ c·e^{−a x}·sin(b x)/x = c·arctan(b/a)` (`a>0`). The value is the genuine symbolic `atan(b/a)` (`evaluate_trig` folds special ratios: `atan 1=π/4`), no elementary antiderivative. New helper `find_linear_exp_rate` reads the `e^{k·var}` rate (mirrors `find_linear_trig`); `a=−rate` (must be `>0`), `b` from the `sin(b x)` factor; constant `c` recovered numerically then proven by the zero-test `equal(expr, c·e^{−a x}sin(b x)/x)`; numeric quadrature guards it. `∫₀^∞ e^{−x}sin x/x=π/4`, `∫₀^∞ e^{−x}sin(2x)/x=atan 2`, `∫₀^∞ 3e^{−x}sin x/x=3π/4`. Leaves the Dirichlet `∫₀^∞ sin x/x=π/2` (no exp) and FTC `∫₀^∞ e^{−x}sin x=½` (no `1/x`) paths untouched.

**Squared-sinc integral** (Entry 37y): `improper_sinc_squared_integral` — the Dirichlet-kernel classic `∫₀^∞ c·(sin(a x)/x)² = c·π|a|/2` (full line `∫_{−∞}^∞ = c·π|a|`, even integrand). No elementary antiderivative. Frequency `a` read off the `sin(a·var)` factor; constant `c` recovered numerically (samples at `x=c/|a|` avoiding the kernel's π-multiple zeros) then proven by the zero-test `equal(expr, c·(sin(a x)/x)²)`; a half-line numeric quadrature guards it (the removable `x=0` point avoided). `∫₀^∞ (sin x/x)²=π/2`, `∫_{−∞}^∞=π`, `∫₀^∞ (sin 2x/x)²=π`, and the `sin²x/x²` spelling. The divergent `(cos x/x)²` correctly declines.

**Bose–Einstein / Fermi–Dirac integrals** (Entry 37x): `improper_bose_einstein_integral` — the Mellin transforms `∫₀^∞ x^{n−1}/(e^x−1) = Γ(n)ζ(n) = (n−1)!·ζ(n)` (Bose) and `∫₀^∞ x^{n−1}/(e^x+1) = (1−2^{1−n})(n−1)!·ζ(n)` (Fermi, the Dirichlet-η factor). Closed only when `ζ(n)` is — even `n≥2`, a rational multiple of `π^n`; **odd `n` declines honestly** (`∫₀^∞ x²/(e^x−1)=2ζ(3)` has no elementary form), and the divergent `m=0` case declines. The value is genuinely derived from the rigorous `special::zeta` (Euler/Bernoulli) and `ntheory::factorial` — not a table; a numeric-quadrature cross-check guards it. `∫₀^∞ x/(e^x−1)=π²/6`, `∫₀^∞ x³/(e^x−1)=π⁴/15`, `∫₀^∞ x⁵/(e^x−1)=8π⁶/63`, `∫₀^∞ x/(e^x+1)=π²/12`, `∫₀^∞ x³/(e^x+1)=7π⁴/120`.

**Log-trigonometric integrals** (Entry 37w): `definite_log_trig_integral` — the classical `∫₀^{π/2} ln(sin x) = ∫₀^{π/2} ln(cos x) = −(π/2)ln2`, `∫₀^π ln(sin x) = −π·ln2`, `∫₀^{π/2} ln(tan x) = 0`, over their canonical intervals. No elementary antiderivative. Same soundness discipline as the dilog handler: constant `c` recovered numerically (interior samples avoiding the kernel's interior zero — `ln(tan)` vanishes at `π/4`) then **proven** by the zero-test `equal(expr, c·K)`; numeric quadrature guards the values. Constant multiples (`∫₀^{π/2} 3·ln sin x = −(3π/2)ln2`) work; a log-trig integral outside the table (`ln(1+sin x)`) is rejected by the gate, not mis-mapped.

**Gaussian–Fourier transform** (Entry 37v): `improper_gaussian_fourier` — `∫_{−∞}^∞ C·e^{−a x²+c}·cos(b x) dx = C·e^c·√(π/a)·e^{−b²/(4a)}` (and its half `∫₀^∞`, since `cos·Gaussian` is even). The base `√(π/a)` is the erf-asymptote-certified Gaussian obtained from the improper integrator itself; the `e^{−b²/(4a)}` damping (rational exponent → stays symbolic `exp(Const)`) is exact by completing the square in the complex exponent — certified by construction and confirmed by a numeric-quadrature cross-check (the Gaussian decays past `|x|>10/√a`; node count scales with `b` to resolve the oscillation). The `sin` variant is odd: full line → exactly `0` (certified); half line is a Dawson function → declines. Inherits the base's perfect-square-`a` limitation (`a=2` declines honestly; `a∈{1,4,…}` certify). So `∫_{−∞}^∞ e^{−x²}cos x=√π e^{−1/4}`, `∫₀^∞ e^{−x²}cos x=(√π/2)e^{−1/4}`.

**Dilogarithm integrals** (Entry 37u): `∫₀^1 c·K(x) dx` for the four canonical `Li₂(±1)` kernels — `ln(1−x)/x` and `ln x/(1−x)` (both `−ζ(2)`), `ln(1+x)/x` (`+ζ(2)/2`), `ln x/(1+x)` (`−ζ(2)/2`). None has an elementary antiderivative (FTC can't reach them). The value is built from the **rigorously derived** `special::zeta(2)=π²/6` (Euler's Bernoulli-number formula — not a literal). Soundness: the constant `c` is recovered numerically (`rationalize` of `expr/kernel` at three interior points, required constant) then **proven** by the zero-test (`equal(expr, c·kernel)`), so only genuine kernel multiples certify — a numeric quadrature cross-check guards the four hard-coded kernel values. So `∫₀^1 ln x/(x−1)=π²/6`, `∫₀^1 ln(1+x)/x=π²/12`, `∫₀^1 2·ln(1+x)/x=π²/6`. Verified NON-firing: `∫₀^1 ln(1+x²)/x=π²/24` (a real dilog value but not one of the four kernels) is rejected by the proportionality gate rather than mis-mapped — no false certificate.

**Half-line Fourier integrals** (Entry 37t): extended `improper_fourier_quadratic` to the half-line `[0,∞)` when the integrand is **even** (`function_parity == Even`) — then `∫₀^∞ = ½∫_{−∞}^∞`. So `∫₀^∞ cos x/(x²+1)=π/(2e)`, `∫₀^∞ cos2x/(x²+1)=π/(2e²)`, and `∫₀^∞ x·sin x/(x²+1)=π/(2e)` (`x·sin x` is even). Parity is the exact soundness guard: an odd/asymmetric integrand still declines on `[0,∞)` (its half-line value is *not* half the symmetric one). Certified by construction (residue theorem) + the zero-test.

**Session tally (Entries 37–37s): 39 substantial certified features** (incl. homogeneous linear-combination trig `cos x+sin x=0`, and exponential-base equations `2^x=8⇒3` via `solve_power_equation`) across integration (rational-trig
half/full period, Gaussian moments, Dirichlet/Fresnel, even quartics + `∫_{−∞}^∞1/(x⁴+1)=π/√2`),
series (Taylor w/ transcendental coeffs), limits (log-vs-power at +∞, conjugate `√(x²+x)−x=½`),
summation (geometric base any spelling), factoring (full ℚ-irreducible), ODEs (surd-root homogeneous,
variable/resonant first-order), `nsimplify`, and inverse Laplace. 355→456 tests.

**Gamma & polygamma heads — the deferred data-model frontier, cracked** (Entry 37ss): added `Γ(x)` and the **polygamma family** `ψ⁽ⁿ⁾(x)` as `UnaryFunc` heads. The long-standing blocker was the derivative tower (`Γ′=Γ·ψ`, `ψ′=ψ₁`, `ψ₁′=ψ₂`, …) needing an infinite set of heads or a 2-arg node. Solved by carrying the order in the variant: **`UnaryFunc::PolyGamma(u32)`** — so `d/dx ψ⁽ⁿ⁾ = ψ⁽ⁿ⁺¹⁾` just increments `n`, staying in the fragment (sound, no infinite heads, no `CasExpr` variant). `Digamma = PolyGamma(0)`, `Trigamma = PolyGamma(1)`. Only **4 exhaustive match sites** needed arms (`name`, `differentiate`, `evalf`, `series::unary_series`) — `name()` switched to `String` so the order encodes into the atom key (distinct orders never collide). Functional folds `Γ(n)=(n−1)!`, `Γ(k+½)=(2k)!/(4ᵏk!)·√π` (`gamma_of_rational`) reach `simplify` (via a `fold_gamma` prepass — folds even when the closed value has more nodes) and the **zero-test** (folded in `equal`'s canonicalization, so `Γ(5)=24`, `Γ(½)=√π`, `Γ(5)=4Γ(4)` all certify while `Γ(5)=25` stays false). Numeric `Γ`/digamma/polygamma via Lanczos + recurrence/asymptotic (`Γ(2.5)≈1.32934`, `ψ(1)=−γ`, `ψ₁(1)=π²/6`). The second derivative `Γ″=Γ(ψ²+ψ₁)` certifies via the closed tower. This is roadmap #11's headline gap and unblocks the digamma/polygamma special-function surface.

**Symbolic factorial & Beta on the Gamma head** (Entry 37tt): with `Γ` in place, two classic functions come almost free and inherit its folds. `CasExpr::factorial(self) = Γ(self+1)` — the gamma extension: `5! → 120`, symbolic `x!` stays `Γ(x+1)`. `beta_function(a,b) = Γ(a)Γ(b)/Γ(a+b)`: `B(2,3)=1/12`, `B(½,½)=π`, symmetric `B(a,b)=B(b,a)` — all certified via the zero-test. Required `fold_gamma` to fold `Γ` at a constant *after arithmetic* (`Γ(5+1)→120`, via `normalize`+`multipoly_as_constant`), not only a literal `Const`.

**Symbolic products → n!** (Entry 37uu): `finite_product` gained the symbolic-upper-bound case via the gamma head: for a unit-slope affine term `k+c`, `∏_{k=a}^n (k+c) = Γ(n+c+1)/Γ(a+c)`. Closes the long-noted gap `∏_{k=1}^n k = Γ(n+1) = n!` (also `∏_{k=3}^n k = Γ(n+1)/Γ(3) = n!/2`, `∏_{k=1}^n (k+1) = (n+1)!`). The symbolic form evaluates back to the concrete factorial when `n` is fixed (`n=5 → 120`) because the gamma folds kick in on substitution.

**Bessel Jₙ generalized to arbitrary order** (Entry 37vv): applied the same index-in-the-variant technique — replaced the two unit heads `BesselJ0`/`BesselJ1` with **`UnaryFunc::BesselJ(u32)`**, so the two-sided recurrence derivative `Jₙ′ = (Jₙ₋₁ − Jₙ₊₁)/2` (with `J₀′ = −J₁`) stays in the fragment for every order. `evalf` already took an arbitrary order (`bessel_j_f64`); `name()` (now `String`) encodes the order so orders don't collide as atoms. New `.bessel_j(n)` builder. `J₂′=(J₁−J₃)/2`, `evalf J₂(2)≈0.35283`, `J₃(5)≈0.36483`. (Note: `J₁′` now emits `(J₀−J₂)/2`, the recurrence form, rather than the old `J₀−J₁/x` — equal in value, but the zero-test only sees the emitted form since it carries no Bessel recurrence between atoms.)

**Digamma/trigamma at integers → harmonic numbers** (Entry 37ww): `fold_gamma` now also folds `ψ(n)` and `ψ₁(n)` at a positive integer, connecting the polygamma heads to harmonic numbers: `ψ(n) = −γ + H_{n−1}` (γ = the `EulerGamma` symbol) — `ψ(1)=−γ`, `ψ(3)=3/2−γ`, `ψ(4)=11/6−γ` — and `ψ₁(n) = π²/6 − H⁽²⁾_{n−1}` — `ψ₁(1)=π²/6`, `ψ₁(2)=π²/6−1`. All certify via the zero-test and are numerically consistent (`evalf ψ(3)=0.92278 = 3/2 − γ`). Matches SymPy's `digamma(3) = 3/2 − γ`.

**Nth-root head — cube roots and the fractional-power frontier** (Entry 37xx): added `UnaryFunc::NthRoot(u32)` (the degree carried in the variant, `q≥3`; `q=2` routes to `Sqrt`), a first real step into fractional powers. Derivative `d/dx u^{1/q} = (1/q)·u^{1/q}/u` stays in the fragment; `evalf` handles odd/even/negative correctly. Perfect-power folds (`nth_root_of_rational`) reach `simplify` and `equal` via `fold_gamma`: `∛8=2`, `∛27=3`, `root4(16)=2`, `∛(−8)=−2`, `∛(8/27)=2/3` certify. New `MultiPoly::fold_nth_root` (mirroring `fold_radical`/`fold_abs`) gives the zero-test `root_q(u)^q = u`: `(∛x)³=x`, `(∛x)⁶=x²`, `(root4 x)⁴=x` certify while `(∛x)²=x`, `∛7=2` stay false (sound). Builders `.cbrt()`, `.nth_root(q)`. (Now integrable: `∫∛x=(3/4)x∛x`, `∫x^{2/3}=(3/5)x∛x²`, `∫₀^8∛x=12` — `integrate_nth_root_power` (`∫x^{p/q}=q·x^{(p+q)/q}/(p+q)`), certified by differentiate-check via `root_q(u)^q=u`; the head, its derivative, and its arithmetic identities are in place.)

**Symbolic binomial coefficient** (Entry 37zz): `binomial_coefficient(n,k) = Γ(n+1)/(Γ(k+1)Γ(n−k+1))` on the gamma head. Folds to the exact integer for concrete args (`C(5,2)=10`, `C(10,3)=120`); the symbolic identities certify via the zero-test: `C(n,0)=1`, `C(n,n)=1`, symmetry `C(7,2)=C(7,5)`, Pascal's rule `C(6,3)=C(5,2)+C(5,3)`, and the binomial theorem `∑ₖ C(4,k)=16`. Completes the combinatorics-on-Γ layer (factorial, Beta, binomial).

**Airy functions Ai/Bi** (Entry 37ab2): added the Airy heads `Ai`, `AiPrime`, `Bi`, `BiPrime` (solutions of `y″ = x·y`). The derivative tower **closes** without an index — `Ai′ = AiPrime`, `AiPrime′ = x·Ai` (the Airy equation), likewise for Bi — so `Ai″ = x·Ai` certifies via the zero-test. `evalf` sums the two Maclaurin solutions of `y″=xy` via the `a_{n+2}=a_{n−1}/((n+2)(n+1))` recurrence and combines them with the standard `Ai(0)`,`Ai′(0)`,`Bi(0)`,`Bi′(0)` constants: `Ai(0)=0.35503`, `Ai(1)=0.13529`, `Ai(2)=0.03492`, `Bi(0)=0.61493`, `Bi(1)=1.20742` all match references. Builders `.airy_ai()`, `.airy_bi()`. Roadmap #11's Airy family, done.

**Lambert W** (Entry 37ab3): added the principal-branch `LambertW` head (inverse of `w·eʷ`). Single head, self-closing derivative `W′(x)=W(x)/(x·(1+W(x)))` (no tower needed). `evalf` via Halley iteration with a branch-aware initial guess (`ln(1+x)` up to `x=e`, else `ln x−ln ln x`): `W(0)=0`, `W(e)=1`, `W(1)=0.56714` (the omega constant), `W(2)=0.85261`, `W(10)=1.74553`, and the defining `W(x)·e^{W(x)}=x` verified. Builder `.lambert_w()`. Rounds out the special-function surface (Γ, ψ⁽ⁿ⁾, Jₙ, Ai/Bi, W, erf, Si/Ci/Ei, Fresnel, NthRoot).

**Lambert-W equation solving** (Entry 37ab4): wired the `LambertW` head into `solve` — `solve_lambert` recognizes `k·x·e^{a·x} + C = 0` (`a`,`k` rational, `C` var-free) and returns `x = W(a·d)/a` with `d = −C/k` (from `(ax)e^{ax}=a·d ⇒ ax=W(a·d)`). `x·eˣ=2 ⇒ W(2)`, `x·e^{2x}=3 ⇒ W(6)/2`, `2x·eˣ=6 ⇒ W(3)`, `x·eˣ=e ⇒ x=1` — all numerically verified against the defining equation. Makes the Lambert-W head useful for the transcendental equations only it can close.

**Puiseux series (fractional-power series)** (Entry 37ab5): `series_at` gained a Puiseux fallback (center 0) building on the `NthRoot` head — for a function of a single root `x^{1/q}` (`root_degree_of` finds `q`), substitute `t=x^{1/q}` (`root_q(x)→t`, `x→tᵠ`), take the ordinary Taylor series in `t` to order `q·order`, then re-substitute `t→x^{1/q}` (new `puiseux_at_origin`; `replace_subexpr` made `pub(crate)`). Closes `sin√x = √x − (√x)³/6 + (√x)⁵/120`, `e^√x = 1+√x+x/2+…`, `cos√x`, cube-root `e^∛x = 1+∛x+(∛x)²/2+…`, all numerically verified. Key subtlety: operate on the *un-shifted* `expr` — `simplify(exp(√x))` atomizes to an opaque `\0exp:\0sqrt:x`, hiding the root. Roadmap's "Puiseux" item (a documented "still open"), done.

**Euler–Cauchy ODEs** (Entry 37ab6): `dsolve_euler_cauchy([a₂,a₁,a₀], var)` solves `a₂x²y″+a₁xy′+a₀y=0` via the indicial equation `a₂r(r−1)+a₁r+a₀=0`, with `xʳ` written as `exp(r·ln x)` (so *any* `r` — rational, surd, complex — stays in the fragment). All three cases: distinct roots `C₀x^{r₁}+C₁x^{r₂}` (incl. surd `x^{±√2}`), repeated `(C₀+C₁ln x)xʳ`, complex `x^α(C₀cos(β ln x)+C₁sin(β ln x))`. Certified by applying the operator to the solution and zero-testing it to 0. Key fixes: fold `√disc` (`√16→4`, keep `√2`) so roots are clean, and certify on the **raw** (un-`simplify`d) solution — `simplify` atomizes `exp(r·ln x)` and breaks the differentiate/cancel. This was the last of the three data-model items the stop-hook named (Puiseux/factorial/**Euler-Cauchy**) — all now built via `exp/ln`, `Γ`, and `NthRoot`, none needing a `Pow`-representation change.

**Gamma integral for fractional powers** (Entry 37ab7): extended `∫₀^∞ x^p·e^{−x} = Γ(p+1)` to fractional `p` — `extract_gamma_form` now recognizes `NthRoot(q)(x)` (power `1/q`, and `NthRoot(q)(x)^m` → `m/q` via the existing `Pow` case), and the result falls back to the symbolic **Γ head** when `special::gamma` has no closed form. `∫₀^∞ √x·e^{−x}=Γ(3/2)=√π/2`, `∫₀^∞ e^{−x}/√x=√π`, `∫₀^∞ ∛x·e^{−x}=Γ(4/3)` (evalf 0.89298), `∫₀^∞ x^{2/3}e^{−x}=Γ(5/3)`. Convergence guarded (`p>−1`). A direct payoff of the Γ + NthRoot heads composing.

**Beta integral for fractional exponents** (Entry 37ab8): the mirror of the Γ-integral extension — `∫₀¹ x^{a−1}(1−x)^{b−1} = B(a,b)`. `extract_beta_form` now recognizes `NthRoot(q)` radicands (`root_q(x^p(1−x)^s) = x^{p/q}(1−x)^{s/q}`, coefficient must be a perfect q-th power to stay rational), and when `special::beta` has no closed form the result falls back to the symbolic **Beta head** `B(a,b) = Γ(a)Γ(b)/Γ(a+b)`. So `∫₀¹ x^{2/3}(1−x)^{1/3} = B(5/3,4/3) = Γ(5/3)Γ(4/3)/Γ(3)` (evalf ≈ 0.30843) resolves symbolically, alongside the existing half-integer cases (`∫₀¹ 1/√(x(1−x)) = B(½,½) = π`). Convergence guarded (`a>0`, `b>0`, i.e. both exponents `>−1`). Another payoff of Γ + NthRoot composing — Γ and Beta integrals now both reach fractional powers.

**gammasimp / combsimp — the Γ functional equation, and Gosper for factorials** (Entry 37ab9): taught the zero-test the functional equation `Γ(z+1)=z·Γ(z)` (`SymPy`'s `gammasimp`/`combsimp`), and used it to unlock **Gosper's algorithm on hypergeometric terms carrying factorials/binomials** — the classic `∑ k·k! = (n+1)!−1` domain that had been declining. `combine_gamma_ratios` now lowers *every* `Γ` head to a canonical base by stripping the integer part of its argument (`Γ(k+2) → (k+1)·k·Γ(k)`, `Γ(k−1) → Γ(k)/(k−1)`), an **expression-independent** rewrite (target base = the fractional part of the argument), so two spellings reach a common `Γ(k)`/`Γ(k+1)` atom that cancels in the normal form. This decides both additive identities `Γ(k+2) − (k+1)·Γ(k+1) = 0` and ratio identities `(k+1)!/k! = k+1` alike, and is wired into both `simplify` (size-gated `gammasimp` candidate) and `equal`'s canonicalization. Pure-constant `Γ`s are left to `fold_gamma` (lowering `Γ(2)` would hit the `Γ(0)` pole); span capped. **Gosper unblock:** `consecutive_ratio` now applies the lowering before `normalize_rational`, so a factorial term's ratio `t(k+1)/t(k)` becomes an honest rational function (`k·k! → (k+1)²/k`); the existing Gosper–Petkovšek + linear solve then runs, and the reconstruction `S(k) = (r(k−1)/p(k))·x(k)·t(k)` keeps the original factorial while the zero-test certifies via the new gammasimp. Now summable: `∑ k·k! = k!` (evalf-checked `∑₁⁴ = 119`), `∑ (k²+k+1)·k! = k·k!`, `∑ k/(k+1)! = −1/k!` (`∑₁⁴ = 119/120`); `∑ 1/k!` still declines honestly (no hypergeometric closed form). Elementary rational Gosper (`∑ 1/(k(k+1)) = −1/k`) and geometric Gosper are unaffected. This is the marquee summation-parity item that the symbolic factorial/binomial layer was built to enable.

**Γ reflection formula + special-angle trig in the zero-test** (Entry 37ac1): two composing gammasimp/combsimp additions. (1) `fold_gamma_reflection` applies `Γ(z)·Γ(1−z) = π/sin(πz)` to any product of two `Γ` heads whose arguments sum to 1 — connecting the two *fractional* towers that the integer-stripping `combine_gamma_ratios` leaves distinct (`Γ(¼)` vs `Γ(¾)`). (2) `evaluate_trig` (special-angle values `sin(π/4)=√2/2`, `cos(π/3)=½`, …, in twelfths of π — machinery that already existed but was never in the zero-test) is now part of `equal`'s canonicalization, so those special-angle identities decide directly. Together: `Γ(¼)Γ(¾) = π√2`, `Γ(⅓)Γ(⅔) = 2π/√3`, `Γ(½)² = π`, and the shifted `Γ(5/4)Γ(¾) = π√2/4` (via `Γ(5/4)=¼·Γ(¼)` lowering first, flattened so the exposed `Γ(¼)` pairs with `Γ(¾)`) all certify, while `Γ(¼)Γ(¾) ≠ π` stays false. Refactored the six-transform canonicalization prepass into one `canonicalize_for_equality` helper (combine_gamma_ratios → fold_gamma_reflection → fold_gamma → evaluate_trig → rewrite_exp/rewrite_log_exp → expand_log_over_primes). Key fix: lower *non-integer* constant `Γ`s too (`Γ(5/4)`, `Γ(−½)` are safe — base stays fractional), only skipping pure *integer* constants (the `Γ(0)` pole, `fold_gamma`'s job).

**Modified Bessel Iₙ** (Entry 37ac2): added the modified Bessel function of the first kind `Iₙ(x)` (`SymPy`'s `besseli`) as `UnaryFunc::BesselI(u32)`, via the same index-in-the-variant technique as `BesselJ`. The derivative recurrence `Iₙ′ = (Iₙ₋₁ + Iₙ₊₁)/2` (with `I₀′ = I₁` — all *plus* signs, unlike `Jₙ`) stays in the fragment for every order. `evalf` via `bessel_i_f64` — the `Jₙ` Maclaurin series without the alternating sign (`Iₙ(x)=Σ(x/2)^{2k+n}/(k!(k+n)!)`, ratio `+(x/2)²/(k·(k+n))`): `I₀(1)=1.26607`, `I₁(1)=0.56516`, `I₀(2)=2.27959`, `I₂(1)=0.13575` match references. Builder `.bessel_i(n)`. Four match sites (name/differentiate/evalf/series-decline) plus the enum + builder, per the proven pattern. Rounds the Bessel family toward `SymPy`'s (Jₙ, Iₙ done; Yₙ/Kₙ — with their log singularities — remain).

**Constant-denominator absorption in `cancel`/`simplify`** (Entry 37ac3): a display-quality fix with broad reach. `RatFunc::reduced()` was leaving a fully-*constant* denominator as a quotient — `(3/8·π)/2` stayed `((3/8)*π)/2` instead of folding to `(3/16)·π` — because a constant is a GCD unit, so the polynomial-GCD reduction never absorbed it. Added a step in the univariate branch: when the reduced denominator is degree 0, divide the numerator through by that constant and set the denominator to 1. Surgical (only fully-constant denominators; `1/(2x+2)` is untouched). Immediately cleans up the whole **Wallis/Beta** family of definite integrals, which were *value*-correct but unreduced: `∫₀^{π/2} sin⁴x = 3π/16`, `∫₀^{π/2} sin²x cos²x = π/16`, `∫₀^{π/2} sin⁶x = 5π/32` now render in lowest terms. The reduced result is also a genuine polynomial-over-atoms again (`normalize` succeeds), so downstream passes that need a polynomial see it.

**Fix `∑ k·cᵏ` boundary `0/0` — geometric Gosper before rational** (Entry 37ac4): a correctness fix surfaced by gap-probing. `∑_{k=0}^∞ k·(1/2)ᵏ` was returning the degenerate `-(0/0)` instead of `2`. Cause: after the gammasimp change let the rational Gosper path accept any term with a rational consecutive ratio, an *arithmetic-geometric* term `k·cᵏ` (ratio `(k+1)/(2k)`, rational) was being handled by `rational_gosper` — whose reconstruction `(r(k−1)/p(k))·x(k)·t(k)` carries a removable `1/p(k)` pole, so `definite_sum`'s boundary substitution at `k=0` hit `0/0`. `geometric_gosper` produces the clean pole-free `X(k)·cᵏ` for exactly these terms, so `gosper_sum` now tries it *first* (it declines for non-geometric terms, falling through to the rational/factorial path). `∑ k·(1/2)ᵏ = 2`, `∑ k·(1/3)ᵏ = 3/4`, finite `∑₀³ = 11/8` all correct now; plain geometric and factorial Gosper unaffected. Found by systematically probing common limits/sums/integrals for declines and degenerate forms.

**∫tanⁿx — tangent-power integrals** (Entry 37ac5): a surprising basic gap found by probing — `∫tan²x` (and higher) declined. Added `integrate_tan_power` using the reduction `∫tanⁿu = tanⁿ⁻¹u/(a(n−1)) − ∫tanⁿ⁻²u` (from `tan²u = sec²u − 1`), bottoming at `∫tan⁰=x`, `∫tan¹u=−ln(cos u)/a`, for `tanⁿ(a·x+b)`, `n ≥ 2`. So `∫tan²x = tan x − x`, `∫tan³x = tan²x/2 + ln(cos x)`, `∫tan⁴x = tan³x/3 − tan x + x`, plus affine (`∫tan²(2x)`) and scaled variants. Each certified downstream by differentiate-and-check — the `sec²=1+tan²` step decides through the Pythagorean/Euler zero-test. (`n=1` stays with the log-substitution finder.)

**Telescoping rational products with symbolic bound** (Entry 37ac6): `∏_{k=2}^n (1−1/k²) = (n+1)/(2n)` and friends now close in symbolic `n`. `finite_product`'s symbolic-upper branch gained `finite_product_symbolic_rational`: factor the rational term completely into linear factors over ℚ (`split_linear_over_q` — peel rational roots with multiplicity via synthetic division; decline on an irreducible ≥2 residual), map each factor `(k+c)` to `∏(k+c)=Γ(n+c+1)/Γ(a+c)` (root `r ⇒ c=−r`), the leading-coefficient ratio `L` to `L^{n−a+1}`, then let `simplify`'s `Γ(z+1)=z·Γ(z)` lowering collapse the Γ tower to a rational function of `n`. Directly powered by the gammasimp work (Entry 37ab9). Validated symbolic-vs-concrete: `∏(1−1/k²)` gives `(n+1)/(2n)` matching the concrete product at n=2,3,5,8; `∏k/(k+1)=1/(n+1)`; `∏2k=2ⁿ·n!`; the affine `∏k=n!` fast path and all concrete products unchanged; a non-splitting term (`1/(k²+1)`) declines.

**∫p(x)·√(ax+b) — polynomial times root of a linear form** (Entry 37ac7): the `Mul` companion to `∫p(x)/√(ax+b)`, found by probing. `integrate_poly_times_sqrt_linear` substitutes `u=a·x+b` (`x=(u−b)/a`), reducing to `(1/a)·Σ cₖ·(2/(2k+3))·uᵏ⁺¹·√u`. So `∫x√(x+1)=(2/5)(x+1)^{5/2}−(2/3)(x+1)^{3/2}`, `∫(2x+1)√(x−1)`, `∫x²√(2x+3)` all resolve and self-certify. The bare `√(ax+b)` (constant cofactor) still routes to the sqrt-power finder.

**∫eˣsin²x — even-trig-power integrals by power reduction** (Entry 37ac8): another probe find — `∫eˣsin²x` (even trig power alongside a factor the odd-power u-subs can't handle) declined. Added `integrate_power_reduced_trig` (a last-resort finder): rewrite `sin²u=(1−cos2u)/2`, `cos²u=(1+cos2u)/2`, then integrate the multiple-angle form via linearity + the exp×sinusoid finder. Two attempts: (1) integrate the *once-reduced* form directly — this preserves an exponential's rate (`expand` would rewrite `e^{2x}→(eˣ)²` and break exp×sinusoid recognition), closing `∫e^{ax}sin²x`, `∫x·cos²x`; (2) fall back to `expand`+reduce iterated to a fixpoint for a higher even power (`sin⁴→cos²2x→cos4x`). Guards: only the numerator of a `Div` is reduced (never mangle `1/(1+cos²x)`, which the tan-substitution finder integrates directly), placed last in the finder list so the canonical trig finders keep their forms, and declines when nothing reduces (no self-recursion). Fixes: drop the redundant `Pow(_,1)` wrapper for `n=2`. `∫eˣsin²x`, `∫eˣcos²x`, `∫eˣsin⁴x`, `∫e^{2x}sin²x`, `∫x·cos²x` all certified.

**∫sinh²x etc. — expand-and-integrate fallback** (Entry 37ac9): probe find — powers of the exponential sums `sinh`/`cosh` (`∫sinh²x`, `∫1/cosh²x`, `∫sinh³x`) declined. Added `integrate_via_expansion`, the *final* fallback finder: `expand` the integrand and integrate the expansion. `sinh²x = (eˣ−e^{−x})²/4` expands to `(exp(x)⁴ − 2·exp(x)² + 1)/(4·exp(x)²)`, a sum of exponential monomials each direct finder handles, closing by linearity. Declines when expansion changes nothing (no self-recursion), placed dead-last so every canonical finder wins first. Certified by differentiate-and-check.

**∫₀^∞ ln x/(1+x²) = 0 — reciprocal-reflection antisymmetry** (Entry 37ad1): probe find. Added `improper_reciprocal_antisymmetry`: on `∫₀^∞`, an integrand **antisymmetric under x→1/x** (`f(1/x)·x^{−2} = −f(x)`) integrates to 0, since the substitution maps `∫_1^∞ f = −∫₀^1 f`. `expand_log` reduces the reflected `ln(1/x)→−ln x` so `equal` decides the antisymmetry. Guard: a *decay* check `x·f(x)→0` at both `0⁺` and `∞` (necessary for convergence; the symmetric value is 0 whether or not it converges, so it can't distinguish — but `ln x/x`, antisymmetric yet divergent, has `x·f=ln x→∞` and is correctly declined). `∫₀^∞ ln x/(1+x²)=0` closes; `∫₀^∞ 1/(1+x²)=π/2` unaffected.

**∫cos(ln x), ∫sin(ln x) — functions of a logarithm** (Entry 37ad2): probe find. Added `integrate_ln_argument_substitution`: `∫F(ln x) dx` via `u=ln x` (`x=eᵘ`, `dx=eᵘ du`) → `∫F(u)·eᵘ du`, which the exp×sinusoid/polynomial finders handle. `∫cos(ln x)=x(cos(ln x)+sin(ln x))/2`, `∫sin(ln x)=x(sin(ln x)−cos(ln x))/2`. Key subtlety: the recovered antiderivative carries `eᵘ`, which must become `x` (not the positivity-dependent `e^{ln x}` the zero-test can't fold) — so `replace_subexpr(eᵘ → x)` is applied *before* `u→ln x`. Two termination guards (the finder calls `integrate` recursively): require a `ln(x)` head present, and require the substituted form to be **exp-free** (`ln(x²+1)→ln(e^{2u}+1)` has a residual `exp(u)`, is not a pure `F(ln x)`, and must decline rather than recurse).

**∫√(a²∓x²) for general a** (Entry 37ad3): probe find — `∫√(4−x²)` declined though `∫√(1−x²)` worked (the finder was hardwired to unit `c₀`). Added `integrate_sqrt_quadratic_general` for any `a²`: `∫√(a²−x²)=½(x√+a²·atan(x/√(a²−x²)))`, `∫√(a²+x²)=½(x√+a²·ln(x+√(x²+a²)))`, `∫√(x²−a²)=½(x√−a²·ln(x+√(x²−a²)))`. Key: the **atan/ln forms are chosen so their derivative carries the *same* radical `√(a²∓x²)`** as the integrand — the textbook `asin(x/a)`/`asinh(x/a)` forms differentiate to a rescaled `√(1∓x²/a²)` that the radical zero-test treats as an unrelated atom, so the certificate would fail. `∫√(4−x²)`, `∫√(x²+4)`, `∫√(x²−4)`, `∫√(2−x²)` (surd `a=√2`) all certify now.

**∫1/(x(1+ln x)), ∫1/(x ln x) — eᵘ cancellation in the log substitution** (Entry 37ad4): generalized `integrate_ln_argument_substitution`'s guard. The `eᵘ` from `dx = eᵘ du` can *cancel* an `eᵘ` in the transformed integrand's denominator (`1/(x(1+ln x)) → 1/(1+u)`, `1/(x ln x) → 1/u`), so the earlier "reject any residual `exp(u)`" guard was too strict. Now the termination test is on the actual integrand `F(eᵘ)·eᵘ` (post-simplify): it must depend on `u`, have no residual `x`, and carry no `ln`-of-`u` head (the real recursion trigger — `ln(x²+1)→ln(e^{2u}+1)·eᵘ` still declines). `∫1/(x(1+ln x))=ln(1+ln x)`, `∫1/(x ln x)=ln(ln x)` now close, and `∫cos(ln x)`, `∫ln(x²+1)` are unaffected.

**Zero-test: canonical argument ordering under transcendental atoms** (Entry 37ad5): a foundational completeness fix, surfaced while testing the log-substitution work. `equal(ln(x+1), ln(1+x))` was true but `equal(ln(ln x+1), ln(1+ln x))` was **false** — `atom_name` keyed a head on `normalize(arg).to_expr()`, but the plain polynomial `normalize` *declines* when the argument carries a transcendental atom (`ln(x)`), so it fell back to the raw, **source-order** argument, giving the two spellings different keys. Fixed by falling back to `normalize_rational` (which atomizes the inner head) before the raw clone. Now any commutative reordering inside a transcendental argument keys identically — `ln(ln x+1)=ln(1+ln x)`, `sin(ln x+1)=sin(1+ln x)`, `ln(eˣ+x)=ln(x+eˣ)` all decide — while genuinely different arguments stay unequal (sound). No regressions across the suite.

**Wilf–Zeilberger proofs of definite binomial sums** (Entry 37ad6): the marquee summation item — `∑_k C(n,k) = 2ⁿ` and `∑_k k·C(n,k) = n·2ⁿ⁻¹` are now **proven** (not sampled) by the WZ method, `prove_wz_sum`. With `f = F/rhs`, a rational certificate `R(n,k)` gives the telescoping pair `f(n+1,k) − f(n,k) = G(n,k+1) − G(n,k)` (`G=R·f`); summing over `k` collapses the RHS to 0, so `S(n)=∑_k f` is constant, pinned to 1 by the base case. **Discovery**: run the (now factorial-capable) `gosper_sum` on the WZ term at several concrete `n`, extract `R(nᵢ,k)`, normalize to a monic denominator, and interpolate each coefficient over `n` (Lagrange). **Soundness gate**: the discovered `R(n,k)` is then *verified symbolically* — `equal(G(n,k+1)−G(n,k), f(n+1,k)−f(n,k))` must certify with `n,k` both symbolic (this leans on gammasimp + the transcendental-atom-ordering fix); a wrong/under-fitted interpolation fails it and the prover declines. So a false identity (`∑C(n,k)=3ⁿ`) is correctly *not* proven. Two prerequisites landed alongside: gosper's `reduce_fraction` now divides out the common integer content (binomial consecutive ratios carry a large content that overflowed the dispersion resultant), and discovery tolerates per-`n` Gosper failures (large `n` overflow the rising factorials). `∑C(n,k)²=C(2n,n)` (higher-degree certificate) remains for a follow-up.

**WZ prover — rational certificate interpolation (∑k²C(n,k))** (Entry 37ad7): generalized `prove_wz_sum` to Zeilberger certificates whose coefficients are *rational* in `n` (not just polynomial). `interpolate_coeffs_over_n` now fits each `k`-coefficient with `rational_interpolate` (lowest-degree `P(n)/Q(n)` through the concrete samples, validated against all points — subsumes Lagrange). Two fixes made it land: (a) sample from *small* `n` (1,2,3,…) independent of `base`, since Gosper overflows the rising factorials at larger `n` and the low values yield the usable samples — the previous `base+1` start missed them; (b) the gosper dispersion-scan fix (Entry prior) lets Gosper discover the higher-degree k²-certificate at concrete `n`. `∑k²·C(n,k)=n(n+1)2ⁿ⁻²` now proven (certificate `R(n,k)` with `(n+1)/(n+2)`-type coefficients), joining `∑C(n,k)=2ⁿ` and `∑k·C(n,k)=n·2ⁿ⁻¹`; a false identity still declines. `∑C(n,k)²=C(2n,n)` remains open — Gosper declines its WZ term even at concrete `n` (a further Gosper-scope item, not the interpolation).

**Double-angle contraction in simplify** (Entry 37ad8): `simplify` now folds `2·sin x·cos x → sin 2x` and `cos²x − sin²x → cos 2x` (the reverse of `expand_trig`), a `trigsimp` gap SymPy handles. `fold_double_angle` recognizes the `c·sin(u)·cos(u)·rest` product (→ `(c/2)·sin(2u)·rest`) and the `cos²(u) − sin²(u)` sum pattern; value-preserving, added as a size-gated `simplify` candidate so it fires only when strictly smaller (`sin 2x` < `2 sin x cos x`) and never disturbs an already-expanded form a caller wants. Pythagorean `sin²+cos²=1` and unrelated trig sums unaffected.

**∫F(root_q x) — rational functions of √x, ∛x, …** (Entry 37ad9): probe find. `integrate_sqrt_rational_usub` substitutes `u=√x` (`x=u²`, `dx=2u du`): replace `√x→u`, `x→u²`, integrate `F(u)·2u`, back-substitute. Closes `∫1/(√x+1)=2√x−2ln(√x+1)`, `∫√x/(1+√x)`, `∫1/(√x(1+x))=2·atan(√x)`, `∫atan(√x)=(x+1)atan(√x)−√x`. Guards mirror the ln-substitution finder: fires only when the whole `x`-dependence is through `√x` (no residual `x`), and the `u`-integrand carries no `√u` (termination). Certified by differentiate-and-check.

**∫F(root_q x) generalization** (Entry 37ada): generalized the `√x`-substitution finder to any single root degree `q` — `integrate_root_rational_usub` detects the root of `x` present (`√x → q=2`, `root_q x → q`), substitutes `u=root_q x` (`x=u^q`, `dx=q·u^{q−1} du`), integrates, and back-substitutes. Adds `∫∛x/(∛x+1)`, `∫1/(1+∛x)`, etc. to the `√x` cases already handled. Declines when more than one root degree is present (would need `x^{1/lcm}`).

**Algebraic limit of a product with a radical** (Entry 37adb): `lim_{x→∞} x·(√(x²+1) − x) = ½` now decides. `limit_algebraic_at_infinity` gained an `expand` prepass so a *product* distributes to the √-sum the conjugate machinery expects (`x·(√(x²+1)−x) → x√(x²+1) − x²`), and `split_sqrt_term` now accepts a **polynomial** coefficient on a √ term (`x·√(x²+1)`), whose leading order `algebraic_leading_at_infinity` already handles. Existing conjugate limits (`√(x²+x)−x=½`, two-√ forms) unchanged; a genuinely divergent product (`x·(√(x²+2x)−x)→∞`) still declines.

**FIX: ∫sin^odd·cos^even infinite hang** (Entry 37adc): a serious bug — `integrate_power_reduced_trig` (the even-trig power-reduction finder) recursed without converging on `sin³cos²`, `sin³cos⁴`, `sin⁵cos⁴`, etc.: it power-reduced the even part while an odd sin/cos remained, and the recursive `integrate` re-entered on a still-odd form, hanging indefinitely. Fix: the finder now declines when *any* odd sin/cos power of the variable is present (`has_odd_trig_power`) — those belong to the `u=cos`/`u=sin` monomial finder and the expansion fallback. The intended all-even cases (`∫eˣsin²x`, `∫x·cos²x`, `∫e^{2x}sin²x`) are unaffected. Subtlety in the guard: for `Pow(cos x, 2)` don't recurse into the bare `cos x` base (which would falsely flag the even power as odd). Regression test added for the previously-hanging odd·even combinations.

**Fractional binomial series for the nth-root head** (Entry 37add): `series((1+x)^{1/q})` now works — `unary_series` handles `NthRoot(q)` via `require_unit + compose(binomial_reciprocal(q))`, the `(1+u)^{1/q}=Σ C(1/q,d) uᵈ` fractional binomial series (the `q`-th-root generalization of the existing `√` / `binomial_half`). `∛(1+x)=1+x/3−x²/9+5x³/81−…`, `∛(1+x²)`, `(1−x)^{1/4}` all series correctly (composing with the inner series). Removed `NthRoot` from the declining arm.

**Bivariate polynomial systems with surd solutions** (Entry 37ade): `solve_polynomial_system` was returning **0** solutions for `x²+y²=1 ∩ x=y` (which has `(±√2/2, ±√2/2)`) — a soundness-adjacent *incompleteness*. Cause: after substituting a surd `x`-root into the second equation, the `((½)√2)²` term was left as `(¼)(√2)²` (`simplify` expands the square but does not fold `(√2)²→2`), so the coefficients weren't clean rationals and the `y`-solve declined. Fix: `simplify_radicals` (which folds `(√u)²=u`) after the expanding `simplify`, so the surd root's square reduces before the y-solve. Now the surd system yields both certified pairs; rational systems (`x²+y²=25 ∩ x²−y²=7 → 4 solutions`, parabola∩line) unchanged. (A system leaving a surd *coefficient* on the remaining variable — `xy=1 ∩ x−y=1` — is still open.)

**Shared-base power-quotient fold (factored simplify)** (Entry 37adf): `simplify((s−3)/(s−3)⁴)` was returning the input unchanged — `cancel` reduces it correctly but *expands* the denominator (`1/(s³−9s²+27s−27)`), which is larger, so the size-gated `simplify` discards it and the nice factored `1/(s−3)³` never appears. Added `fold_power_quotient`: `(c·Gᵐ)/(d·Gⁿ) → (c/d)·G^{m−n}` for a shared base `G`, flattening nested powers (`(G²)²→G⁴`), pulling a rational coefficient out, and stripping leading `Neg`s / a constant numerator (so `−(−2·G)/…` and `−1/(s−1)²` fold their signs). Keeps Laplace/partial-fraction denominators factored: `L{t²e^{3t}}=2/(s−3)³`, `L{t³}=6/s⁴`. Value-preserving, size-gated; genuine rationals (`(x²−1)/(x−1)=x+1`) unaffected.

**∫1/(1+tan x) — pure-tan Weierstrass integrands** (Entry 37adg): `∫1/(1+tan x)` (and `∫tan x/(1+tan x)`) declined because `integrate_weierstrass`'s entry guard required a bare `sin`/`cos` head, rejecting a pure-`tan` integrand — even though `replace_trig_heads` already rewrites `tan` to the rational `2t/(1−t²)`. Widened the guard (and the post-substitution residual check) to `contains_trig` (sin/cos/**tan**). Now the pure-tan rational-trig integrals close via `t=tan(x/2)`; all existing sin/cos Weierstrass integrals unchanged.

**Vandermonde WZ proof — squared-binomial gamma towers** (Entry 37adh): `prove_wz_sum` now proves `∑ₖ C(n,k)² = C(2n,n)` and returns the exact rational certificate `R(n,k)=k²(2k−3n−3)/(2(2n+1)(k−n−1)²)`, whose fully symbolic WZ telescoping identity is rechecked by `equal`; the false near-miss `C(2n,n)+1` still declines. Three completeness fixes close the discovery path without enlarging the trust base: (1) `consecutive_ratio` cancels the exact common monomial content left after canonical gamma lowering (`Γ(−k)^6Γ(k)^6k^m`) before demanding a univariate ratio; (2) the bounded dispersion search tests the required shifted polynomial GCDs directly instead of materializing an overflow-prone symbolic resultant, skipping an overflowing irrelevant shift only as a completeness loss; and (3) WZ sampling folds the concrete summand and RHS separately before dividing, preserving the compact squared-gamma shape instead of expanding an equivalent quotient into large `i128` intermediates. Gosper's returned antidifference and `prove_wz_sum`'s final symbolic identity remain independently certified. A concrete `n=3` Gosper regression, the exact certificate check, the false-identity control, all 504 unit tests, and 147 doctests pass.

**Adjacent convolution + squared-binomial moments — rational poles and primitive Gosper GCD** (Entry 37adi): the next creative-telescoping probe closed all three ranked targets through the existing public `prove_wz_sum` route: `∑ₖC(n,k)C(n,k+1)=C(2n,n−1)` with `R=k(k+1)(2k−3n−2)/(2(2n+1)(k−n)(k−n−1))`; `∑ₖkC(n,k)²=(n/2)C(2n,n)` with `R=k(k−1)((2n+1)k−(3n+1)(n+1))/(2n(2n+1)(k−n−1)²)`; and `∑ₖk²C(n,k)²=n³C(2n,n)/(2(2n−1))` with `R=(k−1)²(2k−3n−2)/(2(2n−1)(k−n−1)²)`. Two exact-arithmetic completeness seams appeared. First, the first-moment coefficient `1/(2n)` cannot be represented by the old rational interpolator's `Q(0)=1` convention; denominators are now monic, and same-total-degree fits prefer balanced numerator/denominator degrees before every available sample is checked. Second, the `n=5` concrete WZ term produced degree-35 ratio polynomials with a degree-31 common factor: all coefficients fit `i128`, but unnormalized rational Euclid overflowed. `reduce_fraction` now removes joint scalar content before GCD, a local primitive-part Euclidean GCD removes content after every remainder, and Gosper may certify its exact reduced polynomial equation when expanding the original gamma-valued telescoping residual overflows. That reduced equation plus the exact normalized consecutive ratio is algebraically equivalent to the full antidifference; the outer WZ soundness gate is still the unchanged fully symbolic `equal` check. Exact-certificate regressions and `rhs+1` false controls cover the three identities, with a direct pole-at-zero interpolation test and an `n=5` reduced-Gosper test; all 508 unit tests and 147 doctests pass.

**Fixed-shift-two convolution + third squared-binomial moment — structured WZ differences** (Entry 37adj): `prove_wz_sum` now closes `∑ₖC(n,k)C(n,k+2)=C(2n,n−2)` and `∑ₖk³C(n,k)²=n³(n+1)C(2n,n)/(4(2n−1))`, returning exact certificates that pass the fully symbolic WZ identity; both `rhs+1` controls decline. The third moment exposed a representation-only overflow: forming the consecutive ratio of the expanded additive gamma tower `f(n+1,k)−f(n,k)` failed at `n=6`, although the ratio is small. The new structured fallback derives it exactly from `a=f(n,k+1)/f(n,k)`, `c=f(n+1,k+1)/f(n+1,k)`, and `d=f(n+1,k)/f(n,k)` as `(cd−a)/(d−1)`, then reconstructs the same difference as `f(n,k)(d−1)` so `G/f` remains cancellable. Fraction reduction now peels shared small integer linear factors and may prove coprimality through a good finite-field reduction before falling back to rational Euclid; neither shortcut cancels an unproved factor. The soft sample target rises from six to eight so degree-six rational coefficient fits have an extra validation point. Focused regressions cover the structured `n=6` certificate and the one-way modular coprimality claim; all 512 unit tests and 147 doctests, warning-denied all-target Clippy, wasm, links, and whitespace checks pass.

**Fixed-shift-three convolution + fourth squared-binomial moment — symbolic WZ ratios and bounded bignum interpolation** (Entry 37adk): `prove_wz_sum` now closes `∑ₖC(n,k)C(n,k+3)=C(2n,n−3)` with `R=k(k+3)(2k−3n)/(2(2n+1)(k−n−1)(k−n+2))`, and `∑ₖk⁴C(n,k)²=n³(n³+n²−3n−1)C(2n,n)/(4(2n−3)(2n−1))`; their exact returned certificates pass the fully symbolic WZ identity and both `rhs+1` controls decline. The fourth moment exposed three independent representation limits. First, concrete factorial constants overflowed after the small samples even though `a=f(n,k+1)/f(n,k)` and `d=f(n+1,k)/f(n,k)` stay small, so those ratios are now derived while `n` is symbolic, common canonical gamma atoms are removed, and only then are they specialized. `h=f(d−1)` gives `h(k+1)/h(k)=a(d(k+1)−1)/(d(k)−1)`, eliminating the redundant third ratio. Polynomial gamma arguments are canonicalized before functional-equation lowering, so equivalent bases such as `Γ(2(k+1)−2)` and `Γ(2k)` cancel. Second, some concrete ratios retain a shared irreducible denominator cofactor after all integer-root factors are peeled; it is cancelled only when exact division of both numerator and denominator succeeds. Third, the twelve-sample 5/5 rational interpolation has `i128`-overflowing Gauss–Jordan intermediates although its answer fits, so linear solving retains the fast `i128` path and falls back only for systems of dimension at most 16 to exact `BigRational`, accepting only final coefficients convertible back to `i128`. These are completeness changes only: the reduced Gosper polynomial equation and final symbolic WZ equality remain exact gates. Focused regressions cover all three seams; all 516 unit tests and 147 doctests, warning-denied all-target Clippy, wasm, links, and whitespace checks pass.

**Fixed-shift-four convolution + fifth squared-binomial moment — symmetric symbolic-ratio compaction** (Entry 37adl): `prove_wz_sum` now closes `∑ₖC(n,k)C(n,k+4)=C(2n,n−4)` with `R=k(k+4)(2k−3n+1)/(2(2n+1)(k−n−1)(k−n+3))`, and `∑ₖk⁵C(n,k)²=n⁴(n+1)(n²+2n−5)C(2n,n)/(8(2n−3)(2n−1))`; the exact returned certificates pass the fully symbolic WZ identity and both `rhs+1` controls decline. The fifth moment exposed one remaining asymmetry: `wz_symbolic_ratios` cancelled common canonical gamma atoms only from the inverse RHS ratio, not from `f(n,k+1)/f(n,k)` or the summand's outer `n` ratio. The latter therefore specialized back into concrete `Γ(n)` factorial towers and stopped normalizing at `n=13`, leaving ten samples and an under-fit certificate. A shared exact compaction closure now treats all three symbolic ratios identically before specialization. With factorial growth removed, sixteen samples are available; raising the target from 12 to 16 (scan 24 to 32) rejects the spurious lower-degree fits and recovers the exact fifth-moment certificate without raising the existing dimension-16 `BigRational` fallback cap. The reduced Gosper equation and fully symbolic WZ equality remain the soundness gates. The full nine-family WZ regression set remains about 16 seconds; all 518 unit tests and 147 doctests, warning-denied all-target Clippy, wasm, links, and whitespace checks pass.

**Fixed-shift Vandermonde as a checked family — direct certificate, shared verifier** (Entry 37adm): added public `prove_fixed_shift_binomial_convolution(shift)`, which constructs `R=k(k+r)(2k−3n+r−3)/(2(2n+1)(k−n−1)(k−n+r−1))` for one concrete nonnegative `r`, then returns it only if the fully symbolic WZ telescoping identity and exact base case at `n=r` certify. This is neither interpolation nor a lookup table: the formula is an untrusted candidate passed through the same checker as discovered `prove_wz_sum` certificates. The symbolic/base logic was extracted into one private `certifies_wz_sum` route so the two APIs cannot diverge. Regressions cover `r=0..7` and reject a zero certificate; `r=8` currently declines because exact canonicalization exceeds the bounded coefficient path, which remains a completeness limit exposed as `None`, not a false family claim. The foundational DAG and research-question register were checked before adding the public helper; no new IR operator, backend semantics, or unresolved CAS-specific ADR boundary is introduced. All 519 unit tests and 147 doctests, warning-denied all-target Clippy, wasm, links, and whitespace checks pass.

**Squared-binomial raw moments as a checked family — Stirling generation, proof-carrying result** (Entry 37adn): added public `prove_squared_binomial_moment(moment)`, which generates `∑ₖk^mC(n,k)²=C(2n,n)∑ⱼS(m,j)(n)ⱼ²/(2n)ⱼ` from the exact power-to-falling-factorial expansion and Vandermonde. This replaces an open-ended table of isolated moment formulas with one derivation route. The generated rational is exactly reduced, its numerator and denominator are normalized to monic form before factorization (preventing harmless polynomial contents such as `1024/32768` from exhausting WZ's bounded `i128` path), and the compact candidate is accepted only when `prove_wz_sum` discovers a certificate and the unchanged fully symbolic WZ plus exact base-case checker passes. `CertifiedSquaredBinomialMoment` carries the order, closed form, and rational certificate, and `is_certified()` independently rechecks that payload. `MAX_PROVED_SQUARED_BINOMIAL_MOMENT=5` exposes the current resource boundary and rejects larger inputs before generation; an exploratory sixth-order request did not pass bounded WZ discovery. Regressions cover orders `0..=5`, direct finite-sum cross-check every member, recover the known fifth-moment closed form, reject both a tampered RHS and a zero certificate, and exercise the ceiling. The foundational DAG and research-question register were checked; no new IR operator, backend semantics, or ADR is required. All 520 unit tests and 147 doctests, warning-denied all-target Clippy, wasm, links, and whitespace checks pass.

**Direct falling-factorial WZ family + composite sixth raw moment** (Entry 37ado): the raw-moment generator no longer asks interpolation to rediscover one increasingly large WZ certificate. `prove_squared_binomial_falling_moment(order)` constructs `R=k(j−k)(jk−2j(n+1)−2k(n+1)+3(n+1)²)/((j−2n−2)(j−2n−1)(k−n−1)²)` for `∑ₖ(k)ⱼC(n,k)²=(n)ⱼC(2n−j,n−j)` and accepts it only through the same `certifies_wz_sum` symbolic/base checker. `CertifiedSquaredBinomialMoment` now carries the nonzero falling-factorial component proofs; its independent checker replays each WZ proof, proves `k^m=∑ⱼS(m,j)(k)ⱼ` by exact normalization, and proves that the weighted component RHSs equal the compact monic-factorized closed form. This composition closes the sixth raw moment `n³(n⁶+3n⁵−13n⁴−15n³+30n²+8n−2)C(2n,n)/(8(2n−5)(2n−3)(2n−1))`, while cutting its family regression from about 55 seconds through order five to about 15 seconds through order six. Public resource ceilings are explicit at 6; order seven currently exceeds bounded exact symbolic checking and declines before public proof work. Regressions cover both families `0..=6`, concrete sums, compact fifth/sixth forms, tampered RHS/certificate, missing components, and the ceilings. The foundational DAG and research-question register remain satisfied: this is explicit compositional evidence, not a new IR/backend semantic. All 521 unit tests and 147 doctests, warning-denied all-target Clippy, wasm, links, and whitespace checks pass.

**Strict rustdoc cleanup across the CAS crate** (Entry 37adp): `RUSTDOCFLAGS="-D warnings" cargo doc -p axeyum-cas --no-deps` exposed ten pre-existing documentation failures outside the moment implementation. The fixes are markup-only: render `𝔽ₚ[x]` as code so brackets are not parsed as a link, make references to private helpers code spans in public docs, qualify `crate::equal` from the orthogonal-polynomial module, and remove redundant explicit targets where the link label already resolves. Strict rustdoc now passes under both stable and the local nightly; no API, algorithm, or runtime semantics changed. The 521 unit tests, 147 doctests, warning-denied all-target Clippy, WASM build, relative-link validation, and whitespace check remain green.

**Concrete WZ base preprocessing extends both moment families through order seven** (Entry 37adq): the parameterized falling-factorial certificate at order seven already passed the fully symbolic WZ identity; the decline was isolated to its exact base case at `n=7`. The checker accumulated all `k=0..7` substitutions before simplifying, so the seven terms that are zero because `(k)₇=0` retained avoidable gamma products and drove rational normalization to `Unknown`. `certifies_wz_sum` now simplifies each fully concrete summand and the concrete RHS before exact equality. This is a completeness-only preprocessing change: every simplification is value-preserving, the symbolic WZ gate is unchanged, and the base is still an exact equality proof. `MAX_PROVED_SQUARED_BINOMIAL_FALLING_MOMENT` and `MAX_PROVED_SQUARED_BINOMIAL_MOMENT` rise from 6 to 7; the composite route recovers `∑ₖk⁷C(n,k)²=n⁴(n+1)(n⁵+5n⁴−15n³−35n²+70n−14)C(2n,n)/(16(2n−5)(2n−3)(2n−1))`. Order eight was separately probed and remains a symbolic `Unknown`, so the public bound stays explicit and fail-closed. Regressions cover both families through seven, the compact fifth/sixth/seventh raw forms, concrete sums, tampered/missing evidence, and the ceiling. All 521 unit tests and 147 doctests, warning-denied all-target Clippy, strict stable/nightly rustdoc, WASM, links, and whitespace checks pass.

**Product-aware symbolic WZ checking + bounded common-denominator composition** (Entry 37adr): order eight's direct `G(n,k+1)−G(n,k)=f(n+1,k)−f(n,k)` expansion was correct but overflowed exact polynomial normalization. `certifies_wz_sum` now falls back only from `Unknown` to the algebraically equivalent quotient identity `R(n,k+1)f(n,k+1)/f(n,k)−R(n,k)=f(n+1,k)/f(n,k)−1`, whose consecutive gamma factors cancel before expansion; a certified-false direct identity still rejects immediately. This remains a fully symbolic exact gate, not sampling. It carries the direct falling-factorial family through order 14; order 15 is the first measured decline. The raw compositor separately replaces an unreduced sum of rational terms with one exact numerator over the known `(2n)ₘ` denominator, then strips a factor `(2n−j)` only when exact polynomial division succeeds. Raw orders `0..=10` now compose and independently recheck; order 11 constructs the common numerator and cancels proven factors but declines in bounded numerator factorization. The compact eighth identity is `∑ₖk⁸C(n,k)²=n³(n⁹+6n⁸−31n⁷−106n⁶+315n⁵+294n⁴−693n³+18n²+96n−20)C(2n,n)/(16(2n−7)(2n−5)(2n−3)(2n−1))`. Regressions cross-check every admitted member against a concrete sum, retain fifth/sixth/seventh forms, add the eighth form, reject tampered RHS/component certificates/missing components, and enforce distinct 14/10 ceilings. All 521 unit tests and 147 doctests, warning-denied all-target Clippy, strict stable/nightly rustdoc, WASM, links, and whitespace checks pass.

**Pre-expansion product cancellation closes the fifteenth falling-factorial moment** (Entry 37ads): the order-15 ratio fallback still returned `Unknown` after Entry 37adr because `wz_symbolic_ratios` simplified the summand and RHS on each side before division. The `k` quotient normalized, but the outer `n` quotient expanded `(n)₁₅` and its shifted copy before their fourteen shared factors could cancel. A new exact preprocessing step flattens one quotient, canonicalizes each polynomial factor, and removes only structurally identical numerator/denominator factors; canonical gamma lowering and the existing rational symbolic equality still provide the proof gate afterward. Falling-factorial proof objects retain `(k)ⱼ` and `(n)ⱼ` as their defining products along this route instead of expanding them prematurely. Order 15 now passes symbolic telescoping, exact base checking, concrete-sum replay, and tampered-certificate rejection; order 16 is the first measured decline, so `MAX_PROVED_SQUARED_BINOMIAL_FALLING_MOMENT=15` while the separately bounded raw ceiling remains 10. The full 521 unit tests and 147 doctests, warning-denied all-target Clippy, strict stable/nightly rustdoc, WASM, links, and whitespace checks pass.

**Structured exact base evaluation extends falling-factorial moments through eighteen** (Entry 37adt): order 16's symbolic quotient identity already certified after Entry 37ads; its remaining `Unknown` came from the exact base term `(16)₁₆(16!/16!)²`. Whole-expression rational normalization multiplied through overflowing factorial intermediates before cancelling the unit quotient, although the small trusted evaluator's recursive expression order reduces the quotient first. `certifies_wz_sum` now tries that existing exact rational evaluator on each fully substituted summand and RHS, replacing a successful result with its rational constant and retaining the previous simplifier/normalizer route as a fail-closed fallback. This is concrete proof preprocessing only: the direct symbolic equality, quotient fallback, and final exact base equality are unchanged. Orders 16, 17, and 18 now pass symbolic telescoping, exact base checking, concrete-sum replay, and tampered-certificate rejection; order 19 is the first measured decline and fails in the symbolic quotient check, before the base case. `MAX_PROVED_SQUARED_BINOMIAL_FALLING_MOMENT=18`; the independently composed raw ceiling remains 10. The full 521 unit tests and 147 doctests, warning-denied all-target Clippy, strict stable/nightly rustdoc, WASM, links, and whitespace checks pass.

**Nested quotient-factor cancellation extends falling-factorial moments through thirty-three** (Entry 37adu): order 19's outer WZ ratio was small but Gamma lowering represented it as a product of nested divisions. The earlier exact preprocessor flattened only multiplication immediately under the outer numerator and denominator; equal Gamma atoms and sixteen shared polynomial factors remained buried, so rational normalization expanded the RHS quotient into degree-36 polynomials and overflowed. `cancel_common_product_factors` now recursively collects factors across multiplication and division (reversing numerator/denominator ownership under a divisor), canonicalizes polynomial factors plus Gamma arguments, and removes only structurally equal pairs before normalization. The order-19 RHS ratio becomes `(n−18)²/((2n−17)(2n−18))`, and the unchanged exact symbolic WZ equality carries every direct member through order 33. Order 34 also passes that symbolic quotient gate but both exact base evaluations decline because `34!` exceeds `i128`; the public cap is therefore 33. A focused ratio regression freezes the compact form, and every admitted family member is replayed against an independent checked-`i128` finite sum before tampered evidence and the ceiling are rejected. Raw order 11 was freshly re-probed and remains a distinct bounded numerator-factorization decline; its public ceiling stays 10. The full 522 unit tests and 147 doctests, warning-denied all-target Clippy, strict stable/nightly rustdoc, WASM, links, and whitespace checks pass.

**Structured normalized composition extends raw squared-binomial moments through nineteen** (Entry 37adv): raw order 11 exposed two completeness artifacts rather than a false identity. The public factorizer peeled its exact roots `0` (multiplicity four) and `−1`, then exhaustive rational-root search overflowed on the remaining degree-11 factor; the raw compositor now peels only exactly dividing bounded integer roots and retains any residual that general factorization cannot split. Its denominator is constructed directly from the uncancelled factors of the known `(2n)ₘ` denominator and accepted only after exact reconstruction of the computed monic polynomial. The old proof checker then overflowed while expanding one weighted sum of eleven Gamma-valued component RHSs. The replacement is compositional and fail-closed: replay every WZ component, certify `k^m=ΣⱼS(m,j)(k)ⱼ`, cancel the common central binomial in each component and the final result, cancel only known `(2n)ⱼ` linear factors by exact polynomial division, and compare the separately normalized monic numerator/denominator coefficient vectors. This closes every raw order through 19, including an explicit regression for the compact order-11 form; bounded concrete sums and tampered closed forms, certificates, and component lists are still checked. Order 20 is the first measured decline: all twenty falling-factorial WZ candidates construct, but exact normalization of common-numerator Stirling term 13 exceeds `i128`. The public raw cap is therefore 19, independently of the falling-factorial cap 33 and its order-34 factorial boundary. The foundational DAG and research-question register still require no ADR because no public operator, backend, or logic semantics changed. The full 522 unit tests and 147 doctests, warning-denied all-target Clippy, strict stable/nightly rustdoc, WASM, links, and whitespace checks pass.

**Pre-cancelled exact composition aligns raw and falling squared-binomial moments at thirty-three** (Entry 37adw): raw order 20's common-numerator overflow came from expanding terms over the full `(2n)ₘ` denominator before cancelling factors already present in `(n)ⱼ²` or the denominator complement. The compositor now removes every even factor `2n−2r` at product level: it either deletes the matching complement factor or removes one `n−r` factor and records the exact scalar `1/2`. Only odd common-denominator factors remain. Reduced dense terms accumulate with exact `BigRational` intermediates, and the independent Stirling power identity uses the same exact coefficient domain; no bignum representation enters `CasExpr`, and the candidate declines unless every final coefficient converts to the public checked-`i128` `Rational`. Higher component quotients exposed a second representation seam: mathematically identical products differed by leading scalars, positive-power spelling, and factor order. The quotient preprocessor now expands only powers through a fixed bound, extracts exact polynomial leading coefficients, converts each factor to monic form, cancels structurally equal factors, and sorts the survivors by a deterministic structural key. Both component quotients and the final central-binomial quotient may close by exact canonical product equality before the existing rational expansion fallback. Every raw order `0..=33` now constructs, replays all direct WZ components, certifies the Stirling identity, passes a bounded direct sum, and rejects tampered evidence plus order 34. Focused regressions independently reconstruct every pre-cancelled Stirling term through order 12 and freeze scalar/power/order canonicalization. The concrete-sum control retains `n=8` through order 25 and uses the nontrivial exact `n=2` sum for orders 26–33; larger samples in that range return `Unknown` only because the small equality evaluator's `i128` intermediates overflow. Order 34 remains the shared boundary because its mandatory falling component reaches the already measured exact-base limit `34! > i128::MAX`; no raw-specific overflow occurs first. The foundational DAG and research-question register still require no ADR because this changes proof preprocessing and bounded exact intermediates, not public operators, backends, or logic semantics. The full 524 unit tests and 147 doctests, warning-denied workspace all-target/all-feature Clippy, strict stable/nightly rustdoc, WASM, links, and whitespace checks pass.

**Bounded bignum WZ bases extend direct moments through 255 and raw moments through 35** (Entry 37adx): the symbolic direct/quotient WZ identity remains the mandatory soundness gate, but a symbolically proved sum whose checked-`i128` finite base comparison returns `Unknown` may now retry that base in a private exact `BigRational` evaluator. The fallback accepts only fully concrete rational `+`, `*`, negation, division, bounded nonnegative powers, and positive-integer Gamma values; it rejects variables, unsupported unary heads, Gamma poles/nonintegers, powers above 1024, and Gamma arguments above 256. A definite `false` base result never falls back. Exact product-leading scalars also use bignum intermediates before converting back to the public checked-`i128` `Rational`, removing the `2^127` transient at falling order 128, and the Gamma-ratio span guard is aligned at 256 so the compact symbolic quotient remains bounded. Every falling order `0..=255` now constructs and replays, with independent exact `BigInt` direct samples, tamper rejection, and the cap check. Order 256 is the first explicit resource decline: its compact quotient still certifies symbolically, but its direct base requires `Gamma(257)`, just beyond the declared evaluator ceiling. Raw-moment monic normalization similarly performs exact division and leading-scalar arithmetic in `BigRational`, accepting the result only if every final coefficient fits the existing public rational domain. This closes raw orders 34 and 35; order 36 declines because its exact monic numerator already needs coefficients wider than `i128`, not because of another avoidable intermediate overflow. Raw regressions retain independent exact `BigInt` direct sums at `n=8` for every high admitted order, evaluate the stored form through the bounded concrete checker, reconstruct pre-cancelled Stirling terms, freeze the overflow-before-reduction case, and reject tampered results, certificates, missing components, and the ceiling. No bignum coefficient enters `CasExpr`, no symbolic proof obligation is weakened, and no public operator, backend, evidence format, or logic fragment changes; the foundational DAG and research-question register therefore require no ADR. The full 525 unit tests and 147 doctests, warning-denied workspace all-target/all-feature Clippy, strict stable/nightly rustdoc, WASM, links, and whitespace checks pass.

**Polynomial-geometric Z transforms and repeated positive-rational poles** (Entry 37ady): a timeout-bounded cross-area probe first separated real gaps from already-covered families. Fourier series of `|x|` and `e^x`, inhomogeneous ODEs (`y''−y=sin x`, `y''+y=1/x`), positive-assumption radical refinement, and polynomial-times-exponential/repeated-pole Laplace controls succeeded; `Z{n·2ⁿ}`, `Z{n²·2ⁿ}`, and double/triple inverse-Z poles were the measured standard declines. `z_transform` now recognizes exact linear combinations of `P(n)aⁿ` with a rational polynomial `P` of degree at most 32 and positive rational `a`. It converts powers to the falling-factorial basis `P(n)=Σqᵣ(n)ᵣ`, applies `Z{(n)ᵣaⁿ}=r!aʳz/(z−a)ʳ⁺¹`, and composes the terms over their known common denominator using bounded private `BigRational` polynomial intermediates; acceptance still requires every final coefficient to convert to public checked-`i128` `Rational`. `inverse_z_transform` now factors the strictly proper `X(z)/z` into positive-rational poles of multiplicity at most 32. For each pole it differentiates the analytic factor `H(z)=(z−a)^mX(z)/z` to recover exact principal-part coefficients and maps `Cⱼ/(z−a)ʲ` to `Cⱼ binomial(n,j−1)a^(n−j+1)`; the existing exact forward round trip remains mandatory. Regressions cover the explicit first two polynomial pairs, a rational base, rational-coefficient division syntax, independent reciprocal-series coefficients across four bases and three polynomial shapes, an independently generated Eulerian row at degree 32, all unit-pole multiplicities 1 through 32, and a mixed simple/repeated case. Degree 33, multiplicity 33, nonlinear exponents, non-positive or irrational poles, improper inputs, and overflow decline. The foundational DAG and research-question register require no ADR because no public operator, backend, evidence format, or logic fragment changed. The full 527 unit tests and 147 doctests, warning-denied workspace all-target/all-feature Clippy, strict stable/nightly rustdoc, WASM, links, and whitespace checks pass.

**Exact symmetric-period rational-trig Fourier coefficients** (Entry 37adz): a second timeout-bounded probe kept the gap search broad. Fourier series of `x³` and `eˣ`, inhomogeneous ODEs with `1/x` and `x·eˣ` forcing, positive-product radical refinement, and repeated-root recurrences succeeded; the elliptic prototype `∫dx/√(1−x⁴)` declined at its expected new-head boundary. Every repeated irreducible-quadratic inverse-Laplace control (`1/(s²+1)²`, `s/(s²+1)²`, the cubic power, a shifted quadratic, and a mixed real/quadratic denominator) declined and is now the next measured transform family. Before that feature work, the probe exposed a proof-boundary seam in the ostensibly successful rational-trig Fourier case `1/(2+cos x)`: `fourier_series` integrates on `[-π,π]`, but `definite_full_period_rational_trig` recognized only `[0,2π]` and `[0,π]`. Generic FTC therefore substituted `±π` into its value-correct but discontinuous `tan(x/2)` antiderivative, returning coefficients with `tan(±π/2)`. Floating evaluation happened to approach the correct numbers, but exact equality with `2π/√3` and the first cosine coefficient certified false because those endpoint terms are not valid exact boundary values. The full-period helper now recognizes both canonical full-period spellings. On `[-π,π]`, `t=tan(x/2)` maps monotonically from `−∞` to `∞`; on `[0,2π]`, its two branches concatenate to the same whole-real-line rational integral. The existing certified improper integrator remains the sole value route, and `[0,π]` remains a half-line integral. A focused regression proves `∫₋π^π dx/(2+cos x)=2π/√3`, proves the first cosine coefficient `2π−4π/√3`, and checks the two-harmonic series against `(1/√3)[1+2Σₖ(√3−2)^k cos(kx)]`; adjacent full/half-period and polynomial Fourier controls remain green. This corrects a proof boundary without adding a public operator, backend, evidence format, or logic fragment, so the foundational DAG and research-question register require no ADR. The full 528 unit tests and 147 doctests, warning-denied workspace all-target/all-feature Clippy, strict stable/nightly rustdoc, WASM, links, and whitespace checks pass.

**Bounded repeated irreducible-quadratic inverse Laplace** (Entry 37aea): the repeated quadratic controls isolated by the previous broad probe now reconstruct exactly when the completed-square shift and frequency are rational. The certified `apart` decomposition already emits each repeated irreducible factor as `(A(s))/q(s)^m`; `inverse_laplace_quadratic_pole_term` places its inverse in the exact `2m`-dimensional basis `tʳe^{αt}{cos,sin}(βt)`, `0≤r<m`. Rather than introducing a second transform formula stack, it asks the existing forward `laplace_transform` for every basis column, normalizes those rational functions over the target `q^m` denominator, and solves one exact rational system. Mixed real/quadratic denominators work because each `apart` term dispatches independently to the closed-form real-pole rule or the quadratic reconstruction. The existing whole-result forward transform plus certified zero-test remains mandatory, so a solvable local system alone never admits an answer. Regressions freeze `L⁻¹{1/(s²+1)²}=(sin t−t cos t)/2`, `L⁻¹{s/(s²+1)²}=t sin t/2`, the cubic formula, a shifted damped double pole, and `1/((s−2)(s²+1)²)`; SymPy independently agrees with the mixed partial fractions and inverse. Every unit-quadratic multiplicity 1 through 7 additionally round-trips. Multiplicity 8 is the first measured resource decline because its required `t⁷cos(βt)` forward expression is constructible but rational normalization exceeds the public checked-`i128` coefficient path; irrational frequencies likewise decline because the forward-certification fragment cannot represent them. No public operator, backend, evidence format, or logic fragment changed, so the foundational DAG and research-question register require no ADR. The full 529-unit/147-doctest suite, warning-denied workspace all-target/all-feature Clippy, strict stable/nightly rustdoc, WASM build, links, and whitespace checks pass.

**Exact rational-scale/shift Bessel-`J₀` Laplace pairs** (Entry 37aeb): a timeout-bounded third cross-area probe found a clean existing-head transform gap: `J₀(t)`, `J₀(2t)`, `e^tJ₀(2t)`, `1/√(s²+1)`, and `1/√((s−1)²+4)` all declined. In contrast, inversion across two distinct rational quadratics, full-period rational-sine integration and Fourier coefficients, and an exact nonzero-point IVP remained green; the elliptic new-head control still declined. `laplace_base` now implements NIST DLMF 3.5.40, `J₀(bt) ↦ 1/√(s²+b²)`, for rational `b`. The existing exponential-shift and transform-derivative rules supply `e^{at}J₀(bt)` and `t^kJ₀(bt)` without duplicating formulas, while `J₀(0)` routes to `1/s` rather than the branch-dependent spelling `1/√(s²)`. The inverse route extracts exactly one rational-scaled square-root quadratic, completes its square with the same rational parameter helper as sinusoidal poles, requires a rational square root of the leading coefficient, and constructs `(c/√lead)e^{at}J₀(bt)`. It still returns only after the public forward transform and exact zero-test reproduce the complete input, so structural recognition alone grants no answer. NIST fixes the base identity and an independent SymPy run agrees on the unit, scaled, and shifted forwards. Regressions additionally freeze the polynomial-weighted derivative route and a rational half-frequency shifted inverse; `J₁`, irrational frequency, and nonquadratic radicals explicitly decline. The same probe records exact/symbolic IVP data and generic first-order inhomogeneous dispatch as the next two concrete gaps. No expression head, public operator, backend, evidence format, or logic fragment changed, so no ADR is required. The full 530-unit/147-doctest suite, warning-denied workspace all-target/all-feature Clippy, strict stable/nightly rustdoc, WASM build, links, and whitespace checks pass.

**Exact-expression initial-condition data** (Entry 37aec): the wave-three oscillator declines are now closed for exact radical and symbolic parameter data whenever the evaluated basis matrix remains rational. `y(0)=√2, y′(0)=1` specializes to `√2 cos x+sin x`; `y(0)=A, y′(0)=B` specializes to `A cos x+B sin x`; and the retained rational `x=π/2` control stays `−3 cos x+2 sin x`. SymPy independently agrees on all three. The implementation leaves matrix discovery in the old exact rational fragment, obtains each inverse column through the existing checked-`i128`/bounded-bignum solver, and only then combines arbitrary exact `CasExpr` right-hand sides. This avoids unproved symbolic pivot or nonzero-denominator assumptions. After substitution, every original condition is differentiated, evaluated, and accepted only when the zero-test certifies exact equality, strengthening the rational path as well as enabling the new one. Expression-valued systems are capped at 16 constants; `C<digits>` data, ODE-variable-dependent data, nonrational basis coefficients, singular systems, and dimension 17 decline. A 17-constant rational system still succeeds, proving that cap does not narrow the existing path. No expression head, operator, backend, evidence format, or logic fragment changed, so no ADR is required. The full 533-unit/147-doctest suite, warning-denied workspace all-target/all-feature Clippy, strict stable/nightly rustdoc, WASM build, links, and whitespace checks pass.

**Certified generic first-order inhomogeneous routing** (Entry 37aed): the wave-three dispatch gap is closed without adding a second ODE algorithm. Before the change, `dsolve_inhomogeneous([1,1], e^x)`, the sine analogue, scaled-leading forms, and a resonant exponential all declined, while direct calls to `dsolve_first_order_linear` succeeded; polynomial forcing and second-order variation of parameters were already green. The non-polynomial route now trims the characteristic coefficients, requires exact degree one, and normalizes `c₁y′+c₀y=f` to `y′+(c₀/c₁)y=f/c₁` with checked rationals. The existing integrating-factor solver retains its normalized-equation residual certificate, and the wrapper adds an independent zero-test of the original scaled operator. Regressions cover exponential/sine forcing, positive and negative nonunit leading coefficients, resonance, derivative-only and trailing-zero operators, independent residual replay, and removal of the homogeneous constant before comparing a particular solution. Degree-zero/cubic operators and the unintegrable forcing `1/(x²+1)` decline; the polynomial and second-order controls remain unchanged. Independent SymPy checks agree on `y′+y=e^x`, `y′+y=sin x`, `2y′+4y=e^x`, and `2y′−2y=e^x`. No public operator, expression head, backend, evidence format, or logic fragment changed, so no ADR is required. The full 534-unit/147-doctest suite passed (the unit gate took 900.77 s), together with warning-denied workspace all-target/all-feature Clippy, strict stable/nightly rustdoc, and the WASM build.

**Arbitrary-order rational-scale/shift Bessel-`Jₙ` Laplace transforms** (Entry 37aee): a fourth timeout-bounded cross-area probe separated a clean existing-head transform gap from adjacent work. `J₁(t)`, `J₂(2t)`, shifted and polynomial-weighted `J₁`, modified Bessel `I₀/I₁`, inverse `J₁`/`I₀` forms, Bessel integrals/asymptotics, and a quadratic inverse-Z form declined, while exact Fourier controls for `|sin x|` and `sign(sin x)` remained green. `laplace_base` now applies the nonnegative-integer specialization of NIST DLMF 10.22.49, `L{Jₙ(bt)}=((√(s²+b²)−s)/b)ⁿ/√(s²+b²)`, to every public Bessel-J order at exact nonzero rational scale. At `b=0`, order zero retains `1/s` and every positive order returns zero. The result uses one symbolic power rather than an order-sized construction loop, so an explicit `u32::MAX` control returns promptly. Existing exponential-shift and transform-derivative rules compose unchanged for `e^{at}Jₙ(bt)` and `t^kJₙ(bt)`. Regressions cover orders 1--4, positive/negative integer and half scales, shift, polynomial weight, zero argument, and the extreme order; modified Bessel, irrational scale, and affine argument explicitly decline. A separate exact family scenario independently replays the derivative identities `sF₀+bF₁=1` and `sFₙ=(b/2)(Fₙ₋₁−Fₙ₊₁)` through order 17 at scales `1`, `−2`, and `1/2`, and SymPy independently simplifies the closed-form difference to zero for representative orders 0--3. No public expression head, operator, backend, evidence format, or logic fragment changed, so no ADR is required. The full 536-unit/147-doctest suite, warning-denied workspace all-target/all-feature Clippy, strict stable/nightly rustdoc, WASM build, links, and whitespace checks pass.

**Arbitrary-order rational-scale/shift modified-Bessel-`Iₙ` Laplace and inverse `I₀`** (Entry 37aef): the handoff-ranked follow-up probe confirmed that forward `I₀`, `I₁`, scaled `I₂`, shifted `I₀`, polynomial-weighted `I₁`, and unit/shifted inverse `I₀` all declined while the arbitrary-order Bessel-J control stayed green. Laplace-transforming the integer-order NIST DLMF 10.32.3 integral representation yields `L{Iₙ(bt)}=((s−√(s²−b²))/b)ⁿ/√(s²−b²)` for nonzero exact rational `b` in the convergence half-plane `Re(s)>|b|`; `laplace_base` now emits that exact form for every public modified-Bessel order. At `b=0`, order zero returns `1/s` and positive orders return zero; one symbolic power, not an order-sized loop, covers the complete `u32` domain. Existing exponential shifts and transform differentiation compose unchanged. Regressions cover orders 0--4, positive/negative integer and half scales, shift, polynomial weight, zero argument, and `u32::MAX`; a separate exact scenario independently replays `sF₀−bF₁=1` and `sFₙ=(b/2)(Fₙ₋₁+Fₙ₊₁)` through order 17 at scales `1`, `−2`, and `1/2`, while SymPy independently agrees on representative orders 0--4. The inverse route now recognizes rational-scale/shift `c/√((s−a)²−b²)`, reconstructs `c·e^{at}I₀(bt)`, and returns only after the existing public forward transform plus zero-test certify the complete input. Unit, signed-scale, shifted integer-frequency, and shifted half-frequency pairs pass; irrational forward scales, affine arguments, irrational inverse frequency, non-square leading scale, and branch-degenerate zero-frequency radicals explicitly decline. No public expression head, operator, backend, evidence format, or logic fragment changed, so no ADR is required. The full 539-unit/147-doctest suite passed (the unit gate took 886.62 s), together with warning-denied workspace all-target/all-feature Clippy, strict stable/nightly rustdoc, WASM build, links, and whitespace checks.

**Exact rational-scale/shift order-one Bessel inverse Laplace pairs** (Entry 37af0): a fifth timeout-bounded broad probe found a sharply bounded existing-head gap. Unit, scaled, and shifted inverse `J₁`/`I₁` pairs and order-two controls all declined; Bessel Maclaurin series, zero limits, and elementary antiderivatives also declined, while two rational-trigonometric Fourier families and representative exact Gaussian/rational integrating-factor ODEs were already green. `inverse_laplace_bessel_order_one` now finds exactly one distinct square-root atom, normalizes its quadratic radicand to recover a rational shift and positive rational frequency, constructs the corresponding `J₁` or `I₁` candidate, and requires the complete input to reduce to a rational multiple of that candidate's public forward transform. The outer public route then independently repeats the complete forward transform and exact zero-test before returning, so structural discovery alone never admits an answer. Regressions cover both families over positive/negative integer and half frequencies, three rational shifts, expanded unit spellings, and an independent outer scale; negative frequencies canonicalize through odd parity. Order two, irrational frequency, a malformed numerator, two distinct radicals, and zero frequency explicitly decline. SymPy independently agrees on unit, integer/half-frequency, and shifted formulas. No expression head, public operator, backend, evidence format, or logic fragment changed, so no ADR is required. The full 541-unit/147-doctest suite passed (the thermally throttled unit gate took 1308.60 s), together with warning-denied workspace all-target/all-feature Clippy, strict stable/nightly rustdoc, WASM build, links, and whitespace checks.

**Exact arbitrary-order Bessel Maclaurin series and zero limits** (Entry 37af1): the handoff-ranked series follow-up is now closed for both existing nonnegative integer-order families whenever the argument vanishes at the origin. `series` composes the exact DLMF 10.2.E2 / 10.25.E2 coefficients through the checked recurrence `c₀=1/(2ⁿn!)`, `cₖ=cₖ₋₁/(4k(n+k))`, with alternating signs for `Jₙ` and positive signs for `Iₙ`. A valuation check precedes all order-dependent work, so an order beyond the requested truncation—including `u32::MAX`—returns the exact zero truncation promptly. Every rational operation remains checked; the first coefficient whose denominator exceeds the public `i128` representation makes the whole expansion decline rather than wrap. Independent fixtures freeze `J₀/J₁/J₂` and `I₀/I₁/I₂` through degree eight or nine, SymPy agrees on those fixtures plus `J₀(2x)` and `I₁(x+x²)`, and a separate exact scenario checks both defining Bessel ODEs for every order 0 through 16 and every coefficient through degree 24. Public `limit` now obtains `Jₙ(x)/xⁿ=Iₙ(x)/xⁿ→1/(2ⁿn!)` at zero for orders 0 through 8 through the ordinary series path. Explicit tests freeze the `J₀/I₀` degree-32 success and degree-34 overflow decline, the `J₁` degree-33 success and degree-35 decline, nonvanishing/foreign-argument declines, and nonlinear composition. Series remains an explicitly non-proof-carrying compute operation; the independent fixtures and ODE checks are test evidence, while no public operator, expression head, backend, evidence format, or logic fragment changed, so no ADR is required. The full 544-unit/147-doctest suite passed (the unit gate took 923.30 s), together with warning-denied workspace all-target/all-feature Clippy, strict stable/nightly rustdoc, the WASM build, links, and whitespace checks.

**Certified direct order-one Bessel antiderivatives** (Entry 37af2): the first antiderivative follow-up now accepts rational-affine `J₁` and `I₁` arguments with arbitrary variable-free outer factors, using `J₀′=−J₁` and `I₀′=I₁` plus the exact chain factor. Every candidate passes the ordinary public differentiate-and-zero-test certificate; unit, shifted, reflected, rational-scaled, symbolic-outer-factor, and definite-FTC controls pass. Orders zero/two/extreme, nonlinear or symbolic slopes, reciprocal overflow, and weighted `xJ₀`/`xI₀` remain honest declines because the latter need a separately justified Bessel recurrence normalization. The extreme-order decline exposed and fixed a pre-existing `order+1` panic in differentiation: only at `u32::MAX`, the exact backward recurrences avoid overflow. No public operator, backend, evidence format, or logic fragment changed, so no ADR is required. The full 545-unit/147-doctest suite passed (933.50 s for units), with workspace warning-denied Clippy, strict stable/nightly rustdoc, WASM, links, and whitespace green.

**Certified weighted order-zero Bessel antiderivatives** (Entry 37af3): the measured `xJ₀`/`xI₀` gap is closed without changing the public derivative representation or introducing division by the Bessel argument. DLMF 10.6.1 and 10.29.1 give the polynomial recurrences `uJ₂(u)=2J₁(u)−uJ₀(u)` and `uI₂(u)=uI₀(u)−2I₁(u)`. The zero-test now applies either recurrence only when the complete coefficient of the matching order-two atom is exactly divisible by the normalized argument; every successful replacement strictly lowers that atom's exponent, so the reduction is value-preserving, bounded, and valid through `u=0`. The integration finder accepts `c·u·J₀(u)` / `c·u·I₀(u)` for nonconstant rational-affine `u` and variable-free `c`, including exact rational rescalings such as `xJ₀(2x)`, then retains the ordinary public differentiate-and-zero-test certificate. Unit, scaled, shifted, reflected, symbolic-factor, recurrence, near-miss, and FTC controls pass; unweighted or mismatched weights, higher order, nonlinear arguments, symbolic slopes, and reciprocal overflow decline. No expression head, public operator, backend, evidence format, or logic fragment changed, so the foundational DAG and research-question register require no ADR. The full 547-unit/147-doctest suite passed (998.34 s for units), together with warning-denied workspace all-target/all-feature Clippy, strict stable/nightly rustdoc, WASM, links, and whitespace checks.

**Exact rational-scale/shift order-two Bessel inverse Laplace pairs** (Entry 37af4): a sixth timeout-bounded cross-area probe measured unit and shifted `J₂`/`I₂` inverse transforms as the best sharply bounded existing-head gap. Order three, `x²J₁`, `x²I₁`, elliptic integration, and quadratic-pole inverse Z still declined, while representative Fourier-exponential and second-order ODE controls were already green. NIST DLMF 10.22.49 and 10.32.3 support the same indexed closed forms already implemented by the public forward transformer. The order-one inverse helper is now an order-parameterized private recognizer, but public dispatch explicitly calls it only for orders one and two: it finds one exact quadratic radical, reconstructs the rational shift and positive frequency, requires the complete input to be a rational multiple of the selected basis's public transform, and returns only after the outer inverse route independently repeats the full forward transform plus exact zero-test. Regressions cover both families over positive/negative integer and half frequencies and three shifts, independent explicit unit formulas, and an outer-scaled shifted case. They freeze odd parity at order one, even parity at order two, and continued declines for order three, irrational frequency, malformed numerators, multiple radicals, and zero frequency. No expression head, public operator, backend, evidence format, or logic fragment changed, so no ADR is required. The thermally managed full gate passed 548 unit tests in 1646.20 s and 147 doctests, together with warning-denied workspace all-target/all-feature Clippy (2m14s), strict stable/nightly rustdoc, WASM, links, and whitespace checks.

**Certified additive radical-bearing inverse Laplace closure** (Entry 37af5): a seventh timeout-bounded cross-area probe found that same-radical `J₀+J₁`, distinct-radical `J₀+I₀`, and rational-plus-Bessel inverse transforms all declined. Polynomially weighted `tJ₀`/`tI₀` transforms, order three, `x²J₁`/`x²I₁` antiderivatives, Bessel limits/improper integrals, and quadratic-pole inverse Z remained larger gaps; nonzero-center Bessel series and Fourier-exponential/Euler-Cauchy controls were already green. Linearity follows directly from the NIST DLMF 1.14.17 integral definition. The new route is deliberately guarded by square-root structure so ordinary rational sums retain whole-expression inversion, recursively inverts only strict additive children, requires every summand to pass its existing inverse certificate, and then independently forward-transforms and zero-tests the complete reconstructed sum. A supported term plus order three or irrational frequency makes the whole sum decline. The probe also exposed a pre-existing zero-pole seam: `1/s` constructed `exp(0t)`, which the forward table could not replay; the simple-pole route now emits exact one at a zero pole. Regressions cover same and distinct Bessel families/frequencies, nested sums, `1/s+J₀`, a shifted/scaled order-two plus nonzero rational pole, full round trips, both unsupported-term boundaries, and a rational cancellation whose individually improper term proves the established rational route is unchanged. Multiple independently supported radicals now compose; an atomic malformed radical form still declines. No expression head, public operator, backend, evidence format, or logic fragment changed, so no ADR is required. The thermally managed full gate passed 549 unit tests in 1392.88 s and 147 doctests, together with warning-denied workspace all-target/all-feature Clippy, strict stable/nightly rustdoc, WASM, links, and whitespace checks.

**Certified weighted order-one Bessel antiderivatives** (Entry 37af6): the next measured existing-head gap now accepts `c·u²·J₁(u)` and `c·u²·I₁(u)` for nonconstant rational-affine `u` and variable-free `c`, including exact rational rescalings of `u²`. NIST DLMF 10.6.6 and 10.29.4 give `d(u²J₂(u))/du=u²J₁(u)` and `d(u²I₂(u))/du=u²I₁(u)`. Candidate construction remains heuristic: the public result is returned only after the ordinary full differentiate-and-zero-test certificate succeeds. To close that certificate without introducing a `1/u` seam, the prior order-two reducer is now a bounded recurrence reducer for target orders two and three. It processes higher orders first and rewrites only when the complete target coefficient is exactly divisible by the normalized argument, using `uJₙ=2(n−1)Jₙ₋₁−uJₙ₋₂` and `uIₙ=uIₙ₋₂−2(n−1)Iₙ₋₁`; every step lowers the target atom and introduces only lower orders. Unit, rational-scale, shift, reflection, symbolic-factor, exact J/I recurrence, derivative replay, and definite-FTC controls pass. Weights `u` or `u³`, mismatched affine weights, order two integrands, nonlinear arguments, symbolic slopes, and reciprocal overflow explicitly decline. The recurrence descriptor collector remains deliberately limited to orders two and three, so this increment does not imply arbitrary-order product normalization. No expression head, public operator, backend, evidence format, or logic fragment changed, so no ADR is required. The thermally managed full gate passed 550 unit tests in 1446.42 s and 147 doctests, together with warning-denied workspace all-target/all-feature Clippy (2m49s), strict stable/nightly rustdoc, WASM, links, and whitespace checks.

**Certified weighted integer-order Bessel antiderivative family** (Entry 37af7): a ninth timeout-bounded cross-area probe confirmed that polynomial-weighted Bessel Laplace transforms were already supported, while weighted order-two/three antiderivatives, order-three inverse Laplace, `J₀` at positive infinity and its improper integral, and quadratic-pole inverse Z still declined. NIST DLMF 10.6.6 and 10.29.4 are order-generic, so weighted integration now accepts `c·uⁿ⁺¹Jₙ(u)` and `c·uⁿ⁺¹Iₙ(u)` for rational-affine `u`, variable-free `c`, and the explicit discovery cap `0≤n≤32`, returning `(c/slope)uⁿ⁺¹Jₙ₊₁(u)` or its `I` analogue only after the unchanged full differentiate-and-zero-test certificate. Order 33 and mismatched powers decline. Recurrence normalization itself is finite per input and needs no discovery cap: exact argument divisibility applies `uJₙ=2(n−1)Jₙ₋₁−uJₙ₋₂` or `uIₙ=uIₙ₋₂−2(n−1)Iₙ₋₁` for every public `u32` order, with the coefficient widened to checked `i128` before doubling. Tests cover J/I orders 2, 3, 8, 16, and 32; shifted, reflected, nested symbolic-factor, derivative replay, and definite-FTC cases; arbitrary-order recurrence checks through `u32::MAX`; and order-33/wrong-power declines. The nested symbolic/reflected case exposed that `split_var_free_factor` inspected only one multiplication layer; it now uses the stable recursive product flattener, preserving value and making the documented variable-free-factor contract independent of association. No expression head, public operator, backend, evidence format, or logic fragment changed, so no ADR is required. The thermally managed full gate passed 551 unit tests in 1574.57 s and 147 doctests, together with warning-denied workspace all-target/all-feature Clippy (42.14 s on the warm cache), strict stable/nightly rustdoc, WASM, links, and whitespace checks.

**Certified bounded integer-order Bessel inverse-Laplace family** (Entry 37af8): a tenth bounded follow-up audited the existing positive-order recognizer after wave nine left order three as the nearest measured transform gap. NIST DLMF 10.22.49 and 10.32.3 support the indexed `Jₙ` and `Iₙ` forward forms already emitted by the public transformer, so public inverse dispatch now tries that unchanged private recognizer for the explicit resource-bounded family `1≤n≤32`; the existing order-zero routes complete the documented `0≤n≤32` family. Recognition remains discovery only: each candidate must be an exact rational multiple of its selected public forward basis, and the outer inverse route independently forward-transforms and zero-tests the complete input before returning. Regressions cover J/I orders 3, 8, 16, and 32, a scaled and shifted order-seven `I` pair, full forward roundtrips, and an additive `J₀+J₃` inverse. Order 33 and `u32::MAX`, irrational frequency, a malformed numerator, zero frequency, and an additive supported-plus-order-33 input all decline. The bounded loop prevents hostile public orders from driving unbounded search, and the additive route still fails closed when any radical-bearing summand is unsupported. No expression head, public operator, backend, evidence format, or logic fragment changed, so no ADR is required. The thermally managed full gate passed 551 unit tests in 1936.53 s and 147 doctests, together with warning-denied workspace all-target/all-feature Clippy, strict stable/nightly rustdoc, WASM, links, and whitespace checks.

**Certified rational-scale integer-order Bessel-J improper integrals** (Entry 37af9): wave eleven compared the remaining measured Bessel improper/asymptotic gap with the quadratic-pole inverse-Z gap. The latter requires a new oscillatory-sequence transform fragment and exact angle representation, while NIST DLMF 10.22.41 gives the sharply bounded existing-head identity `∫₀^∞Jₙ(t)dt=1` for every public nonnegative integer order. `improper_integrate` now applies its exact scale change to `c·Jₙ(ax)` for nonzero rational `a` and any `x`-free factor `c`; a negative scale uses the exact parity identity `Jₙ(−u)=(−1)ⁿJₙ(u)`. The rule is constant-time in `n`, so regressions cover orders 0, 1, 2, 7, 32, and `u32::MAX`, integer/half and reflected scales, rational and symbolic outer factors, and the checked-negation boundary. Modified Bessel `I`, shifted, nonlinear, irrational, and zero scales, the minimum-integer scale whose absolute value cannot fit, and a nonzero lower bound explicitly decline. SymPy independently agrees on orders 0 through 3 at scales `1/2`, `2`, and `−2`. The exact DLMF theorem supplies the value certificate without claiming an elementary antiderivative; no expression head, public operator, backend, evidence format, or logic fragment changed, so no ADR is required. The thermally managed full gate passed 552 unit tests in 1614.65 s and 147 doctests, together with warning-denied workspace all-target/all-feature Clippy (131.99 s), strict stable/nightly rustdoc, WASM, links, and whitespace checks. The non-mutating formatter check still exposes broad pre-existing local-toolchain drift but proposed no change around the owned lines, so no unrelated formatting was applied.

**Certified affine integer-order Bessel-J limits at both infinities** (Entry 37afa): wave twelve's timeout-bounded probe confirmed that standalone and rational-affine `Jₙ` limits still declined alongside modified `Iₙ`, irrational/nonlinear arguments, reciprocals, and polynomial weights. NIST DLMF 10.17.3 gives fixed order an oscillatory `O(|z|^{-1/2})` envelope, while 10.11.1 transfers the result across the negative real direction for integer order. `limit` now returns exact zero for `c·Jₙ(ax+b)` at either real infinity for every public nonnegative integer order, nonzero rational `a`, rational `b`, and any `x`-free factor `c`. The rule is constant-time in `n`; regressions cover orders 0, 1, 2, 7, 32, and `u32::MAX`, positive half and positive/negative integer scales, rational shifts, both infinities, symbolic outer factors, and additive linearity. Modified Bessel `I`, irrational or nonlinear arguments, symbolic shifts, reciprocals, and polynomial weights explicitly decline, while constant and finite-point `J₀(0)=1` behavior remains unchanged. SymPy independently agrees on orders 0 through 3 across half, shifted positive, and shifted negative scales. No expression head, public operator, backend, evidence format, or logic fragment changed, so no ADR is required. The thermally managed full gate passed 553 unit tests in 1527.65 s and 147 doctests, together with warning-denied workspace all-target/all-feature Clippy (2m14s), strict stable/nightly rustdoc, WASM, links, and whitespace checks. The non-mutating formatter check still exposes broad pre-existing local-toolchain drift but proposes no change around the owned lines, so no unrelated formatting was applied.

**Certified rational-polynomial integer-order Bessel-J limits** (Entry 37afb): wave thirteen's cross-area probe compared the adjacent nonlinear Bessel limit gap with quadratic-pole inverse Z. The latter still needs an oscillatory-sequence transform fragment, whereas every nonconstant real polynomial has unbounded magnitude at both real infinities and therefore remains under NIST DLMF 10.17.3's fixed-order `O(|z|^{-1/2})` envelope plus 10.11.1's integer-order continuation. `limit` now returns exact zero for `c·Jₙ(p(x))` at either real infinity for every public order, nonconstant rational-coefficient polynomial `p`, and any `x`-free factor `c`. The rule remains constant-time in `n`; regressions cover orders 0, 3, 32, and `u32::MAX`, degrees two through four, both leading signs and infinities, a half coefficient, shifts, and symbolic outer factors. Rational-function arguments such as `x+1/x`, irrational or symbolic polynomial coefficients, modified Bessel `I`, and variable-dependent weights explicitly decline. SymPy independently agrees for orders 0 through 3 on all four polynomial shapes. No expression head, public operator, backend, evidence format, or logic fragment changed, so no ADR is required. The thermally managed full gate passed 554 unit tests in 1478.68 s and 147 doctests, together with warning-denied workspace all-target/all-feature Clippy (10.69 s warm), strict stable/nightly rustdoc, WASM, links, and whitespace checks. The non-mutating formatter check still exposes broad pre-existing local-toolchain drift but proposes no change around the owned lines, so no unrelated formatting was applied.

**Certified unbounded rational-function integer-order Bessel-J limits** (Entry 37afc): wave fourteen's adjacent probe found that degree-growing rational arguments such as `x+1/x`, `(x³+1)/(x²+1)`, and `(1−x⁴)/(2x²+3)` still declined, while bounded equal-degree forms declined and the established decaying control `J₀(1/x)→1` remained green. Writing an exact rational argument as `p(x)/q(x)`, the decidable condition `deg p>deg q` proves `|p(x)/q(x)|→∞` at both real infinities; NIST DLMF 10.17.3's fixed-order `O(|z|^{-1/2})` envelope and 10.11.1's integer-order continuation therefore apply unchanged. `limit` now returns exact zero for `c·Jₙ(p(x)/q(x))` at either infinity for every public order, rational-coefficient `p,q` satisfying that degree condition, and any `x`-free `c`. The rule remains constant-time in `n`; regressions cover orders 0, 3, 32, and `u32::MAX`, all three signed rational shapes, and both infinities. Equal-degree bounded arguments, symbolic denominator coefficients, irrational coefficients, modified Bessel `I`, and variable-dependent weights explicitly decline, while the decaying control retains its exact value. SymPy independently agrees for orders 0 through 3 on all three degree-growing shapes at both infinities. No expression head, public operator, backend, evidence format, or logic fragment changed, so no ADR is required. The thermally managed full gate passed 555 unit tests in 1451.33 s and 147 doctests, together with warning-denied workspace all-target/all-feature Clippy, strict stable/nightly rustdoc, WASM, links, and whitespace checks. The non-mutating formatter check still exposes broad pre-existing local-toolchain drift but proposes no change around the owned lines, so no unrelated formatting was applied.

**Exact finite-rational inner-limit composition for integer-order Bessel J/I** (Entry 37afd): wave fifteen's bounded cross-area probe compared the adjacent equal-degree rational Bessel seam with variable-dependent Bessel weights and quadratic-pole inverse Z. `Jₙ((x²+1)/(x²+2))` and its modified-Bessel counterpart declined at both infinities despite their exact inner limit, while lower-degree `Jₙ(1/x)`/`Iₙ(1/x)` already reached their zero-argument values; bounded and decaying variable weights and the oscillatory inverse-Z form remained larger rate/representation gaps. NIST DLMF 10.2(ii) and 10.25(ii) define the first-kind functions as entire in their argument for fixed nonnegative integer order, so continuity gives `lim Hₙ(r(x))=Hₙ(lim r(x))` for `H∈{J,I}`. `limit` now applies that composition when the complete inner limit is a literal exact rational, retaining an outer factor only when it is independent of the limiting variable. The rule is constant-time in the public order; regressions cover orders 0, 3, 32, and `u32::MAX`, limiting values `1`, `−2`, and `1/2`, both heads, both real infinities, a symbolic outer factor, and the zero-argument fold. Non-rational or nonexistent inner limits, unbounded modified-Bessel arguments, variable-dependent outer factors, and Bessel denominators explicitly decline, while the earlier unbounded rational `Jₙ→0` route remains green. SymPy independently agrees on all 48 combinations of heads, orders 0 through 3, three shapes, and two infinities. No expression head, public operator, backend, evidence format, or logic fragment changed, so no ADR is required. The thermally managed full gate passed 556 unit tests in 1639.99 s and 147 doctests, together with warning-denied workspace all-target/all-feature Clippy (2.89 s warm), strict stable/nightly rustdoc, WASM, links, and whitespace checks. The non-mutating single-file formatter audit proposed no owned-line changes, so no unrelated formatting was applied.

**Certified bounded rational-weight integer-order Bessel-J limits** (Entry 37afe): wave sixteen's bounded cross-area probe compared bounded rational weights on the established unbounded-argument Bessel limit with growing and subcritical-rate Bessel products, the modified-Bessel neighbor, Bessel denominators, and quadratic-pole inverse Z. Exact rational weights with numerator degree no greater than denominator degree were the smallest theorem-backed extension; the rate-sensitive growing cases and oscillatory inverse-Z representation remain deliberately deferred. NIST DLMF 10.17.3 gives `Jₙ(z)=O(|z|^{-1/2})` for fixed order on the positive-real asymptotic route and 10.11.1 supplies the exact integer-order continuation across the negative-real direction. Consequently, when an exact rational-coefficient argument `r(x)` has numerator degree greater than denominator degree and an exact rational-coefficient weight `w(x)` has numerator degree no greater than denominator degree, `w(x)` remains bounded at either real infinity and `w(x)Jₙ(r(x))→0`. `limit` now implements precisely that condition, retaining any additional factor only when it is independent of the limiting variable. The rule is constant-time in the public order; regressions cover orders 0, 3, 32, and `u32::MAX`, weights `x/(x+1)`, `(x²+1)/(2x²+3)`, and `1/(x²+1)`, affine/cubic/rational degree-growing arguments, both infinities, symbolic outer factors, and reflected coefficients. Growing weights `x·J₀(x)` and `x·J₀(x²)`, the true but intentionally deferred subcritical-rate case `x·J₀(x³)`, modified Bessel `I`, Bessel denominators, symbolic rational coefficients, multiple Bessel factors, and bounded Bessel arguments explicitly decline. SymPy independently agrees on all 24 combinations of orders 0 through 3, the three admitted weight/argument pairs, and two infinities. No expression head, public operator, backend, evidence format, or logic fragment changed, so no ADR is required. The thermally managed full gate passed 557 unit tests in 1821.62 s and 147 doctests; the same test process was paused and resumed under thermal contention rather than restarted. Workspace warning-denied all-target/all-feature Clippy (5.94 s warm), WASM (5.24 s), strict stable/nightly rustdoc (1.89/1.79 s), links, and whitespace checks all pass. The non-mutating single-file formatter audit proposed no owned-line changes, so no unrelated formatting was applied.

**Certified subcritical rational-rate integer-order Bessel-J limits** (Entry 37aff): wave seventeen's bounded probe measured the precise rate seam left by the previous bounded-weight rule. Polynomial cases `x·J₀(x³)` and `x²·J₃(x⁵)`, a rational weight growing like `x` against a rational argument growing like `x³`, and a reflected signed case all declined before the change; the borderline `x·J₀(x²)`, supercritical `x²·J₀(x³)`, modified-Bessel, and denominator controls also declined. For an exact rational-coefficient argument `r(x)=Θ(|x|^d)` and exact rational-coefficient weight `w(x)=O(|x|^e)`, NIST DLMF 10.17.3's fixed-order envelope and 10.11.1's integer-order negative-real continuation give `w(x)Jₙ(r(x))=O(|x|^(e-d/2))`. `limit` now computes the exact degree growths and returns zero only under the strict integer condition `2e<d`, conservatively treating bounded and decaying weights as `e=0`; any remaining factor must be independent of the limiting variable. Regressions cover orders 0, 3, 32, and `u32::MAX`, the three polynomial/rational rate pairs, reflected signs, symbolic outer factors, and both real infinities. Equality `2e=d` is deliberately rejected because the envelope is only `O(1)` there; supercritical rates, modified Bessel `I`, Bessel denominators, symbolic rational coefficients, multiple Bessel factors, and bounded arguments remain fail-closed. SymPy leaves the prototype `x·J₀(x³)` unevaluated, so it is recorded as a parity non-result rather than agreement. An independent 80-digit mpmath comparison of every order 0 through 3, all three rate pairs, and both directions against the leading fixed-order asymptotic passes 24/24 with maximum envelope-scaled error 0.00215744. No expression head, public operator, backend, evidence format, or logic fragment changed, so no ADR is required. The thermally managed full gate passed 558 unit tests in 2086.07 s and 147 doctests; the same test process was repeatedly paused and resumed under external thermal contention, then completed on one pinned CPU without restart. Workspace warning-denied all-target/all-feature Clippy (5.10 s warm), WASM (5.21 s), strict stable/nightly rustdoc (2.25/2.09 s), links, and whitespace checks all pass. The non-mutating single-file formatter audit proposed no owned-line changes, so no unrelated formatting was applied.

**Certified rational-rate products of integer-order Bessel J** (Entry 37b00): wave eighteen probed the nearest existing-head composition seam after the strict single-factor rate rule. Direct products `J₀(x)J₁(x)`, `xJ₀(x)J₃(x²)`, `x²J₂(x³)Jₘ((x⁵+1)/(x²+1))`, and `xJ₀(x)J₁(x)J₂(x)` all declined, as did the correct combined borderline/supercritical, modified-I, and bounded-argument controls. NIST DLMF 10.17.3 and 10.11.1 apply independently to each fixed public integer order. Thus for exact rational-coefficient arguments `rᵢ(x)=Θ(|x|^dᵢ)` and an exact rational-coefficient weight `w(x)=O(|x|^e)`, the finite direct product satisfies `w(x)∏Jₙᵢ(rᵢ(x))=O(|x|^(e-Σdᵢ/2))`. `limit` now collects every direct Bessel-J factor, requires each rational argument to have positive exact degree growth, checked-adds those growths, and returns zero only under the strict checked condition `2e<Σdᵢ`; bounded and decaying weights remain conservatively represented by `e=0`, and every remaining factor must be independent of the limiting variable or part of the exact rational weight. Regressions cover two and three Bessel factors, polynomial and rational arguments, weights through degree two, orders 0, 1, 2, 3, 7, 32, and `u32::MAX`, reflected signs, symbolic outer factors, and both real infinities. Equality in the combined rate gives only an `O(1)` envelope and declines; supercritical weights, any bounded Bessel argument, modified Bessel `I`, Bessel denominators, and symbolic rational coefficients remain fail-closed. An independent 80-digit mpmath comparison of all four admitted product shapes at both directions against the product of their leading fixed-order asymptotics passes 8/8 with maximum envelope-scaled error 0.0115689. SymPy does not decide the same set within a 120-second timeout, which is recorded as a parity non-result rather than agreement. No expression head, public operator, backend, evidence format, or logic fragment changed, so no ADR is required. The thermally managed full gate passed 559 unit tests in 2347.62 s and 147 doctests with `RUST_TEST_THREADS=2` constrained to one CPU; the same process was repeatedly paused and resumed under external Java/Python thermal contention without restart. Workspace warning-denied all-target/all-feature Clippy (7.00 s warm), WASM (5.66 s), strict stable/nightly rustdoc (2.14/1.79 s), links, and whitespace checks all pass. The non-mutating single-file formatter audit proposed no owned-line changes, so no unrelated formatting was applied.

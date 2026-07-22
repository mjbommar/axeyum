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

**Session tally (Entries 37–37h): 24 substantial certified features** (incl. homogeneous linear-combination trig `cos x+sin x=0`, and exponential-base equations `2^x=8⇒3` via `solve_power_equation`) across integration (rational-trig
half/full period, Gaussian moments, Dirichlet/Fresnel, even quartics + `∫_{−∞}^∞1/(x⁴+1)=π/√2`),
series (Taylor w/ transcendental coeffs), limits (log-vs-power at +∞, conjugate `√(x²+x)−x=½`),
summation (geometric base any spelling), factoring (full ℚ-irreducible), ODEs (surd-root homogeneous,
variable/resonant first-order), `nsimplify`, and inverse Laplace. 355→456 tests.

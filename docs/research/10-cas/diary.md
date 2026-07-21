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

# CAS certificate audit: what reconstructs, what could, what is `cas-internal`

Dispatched against
[`2026-09-01-the-cas-certifies-far-more-than-the-ledger-records.md`](2026-09-01-the-cas-certifies-far-more-than-the-ledger-records.md).
The rule the findings in section 3 share is recorded as [ADR-1400](../09-decisions/adr-1400-a-certificate-must-record-every-distinction-its-acceptance-depends-on.md).

Every verdict below cites a file and a function that was read. No verdict rests
on a module doc — a file that records obstacles accumulates stale ones by
construction, and its authority is exactly what makes them expensive.

## Both of the parent document's headline numbers are wrong, in opposite directions

The parent's finding — the CAS certifies more than the ledger records — survives.
Its two numbers do not. Both came from string queries answering a narrower
question than the one asked, and they err in **opposite** directions, so the gap
the parent reports (40 modules against 19 facts) is roughly twice the real one.

### The numerator: `40 of 53` counts doc-comment prose

The parent's query is `certificate|Certificate|fn verify|fn check_` over
`crates/axeyum-cas/src/*.rs` with no masking. This crate's doc comments are
unusually discursive — several modules discuss certificates at length precisely
to say they emit none (`series.rs:11-13` and `orthopoly.rs:16-18` both state
outright that they are compute operations with no certificate attached) — so the
pattern matches text, not code.

Re-measured with Rust line comments, block comments and string literals masked
out:

| query | modules |
| --- | --- |
| the parent's pattern, unmasked | **41 of 55** |
| the same pattern, comments and string literals masked | **27 of 55** |
| a second, differently-shaped query: `struct`/`enum` named `*Certificate`/`*Cert`/`*Witness`, or `fn verify_*`/`check_*`/`certify_*`/`validate_*`, masked | **23 of 55** |
| union of the two masked queries | **30 of 55** |

Two independent shapes agreeing at 27 and 23 is the check a single grep does not
have. **The certificate-carrying surface is ~27 modules, not 40.** (The module
count also moved, 53 → 55, because the tree advanced between the two
measurements. Quote 55.)

### The denominator: `^F-cas-` counts a filename convention, not a route

`ls artifacts/facts/ | /usr/bin/grep -c "^F-cas-"` returns **19**, and that is a
correct answer to a question about filenames. The ledger's own notion of a CAS
result is `proof_route`, which `scripts/validate-facts.py` reports directly:

```
routes: cas-certificate=48(kernel-reconstructed=14,cas-internal=34) …
```

**48 facts at the start of this audit, not 19.** The 29 the filename query misses
are named for their mathematics rather than their producer: nine telescoping
facts (`F:apery-numbers-recurrence`, `F:franel-numbers-recurrence`,
`F:chu-vandermonde-convolution` and six binomial row-sum identities), seventeen
geometry facts, four GF(2) facts.

This falsifies one specific claim in the parent: that Gosper and Zeilberger
creative telescoping have "no ledger fact at all". `telescoping.rs` and
`telescoping_check.rs` are each named by **nine** settled facts. `gosper.rs`
genuinely has none — and, as §3 below shows, it emits nothing that could carry
one.

### The measurement that actually answers the question

The gap is *certificate-carrying modules that no fact names*, which needs both
sides joined per module. Joining the masked certificate-surface query against
every fact's `artifact` and `checker_command` strings:

| | naming fact | no naming fact |
| --- | --- | --- |
| **certificate surface** | 14 | **13** |
| **no certificate surface** | 6 | 22 |

The thirteen uncovered certificate-carrying modules were `boolean_circuit`,
`geometry_json`, `gf2_artifact`, `gf2_independent`, `gf2_search`, `gf2_shard`,
`gf2_tensor`, `gosper`, `groebner_cert`, `lib`, `ratint`, `sos`,
`telescoping_json`.

The six modules with a fact but no certificate surface of their own —
`cofactor_ansatz`, `geometry`, `geometry_corpus`, `linear_elim`, `mvpoly`,
`sturm` — are not an anomaly: they are consumed by a certifier in a sibling
module. That is this repository's documented retrieval hazard (general
infrastructure filed under its first consumer) showing up in a coverage metric,
and any module-granular metric will misreport them in one direction or the
other.

**So the honest statement of the deficiency is thirteen modules, not
thirty-four.** That is smaller and more actionable, and every module in it is
named.

## The verdict table

Read `RECONSTRUCTS (partial)` carefully. In every case the kernel re-checks a
**strictly weaker** claim than the certificate makes, and the ledger already
handles this correctly with sibling facts (see
`F:cas-ivt-sign-bracket-cbrt2-kernel-checked`, whose whole design is to claim
less than `F:cas-ivt-cbrt2-in-1-2`). The residue column is what is *not*
reconstructed.

### RECONSTRUCTS TODAY (9 modules, all partial)

| module | bridge | what the kernel re-checks | residue |
| --- | --- | --- | --- |
| `real_algebraic.rs` (`IvtCertificate`, `:342`) | `rat_prelude/cas_ivt_bridge_tests.rs::ivt_sign_bracket_cbrt2_kernel_checked` | the sign bracket `p(a) < 0 < p(b)` at rational endpoints | root containment (`minpoly ∣ poly`) and the Sturm uniqueness count; the translator `sign_bracket_to_int:134` deliberately drops `cert.root` |
| `partial_fractions.rs` (`PartialFractionCertificate`, `:186`) | `cas_partial_fractions_bridge_tests.rs::cas_partial_fractions_mixed_general_case_kernel_checked` | the reconstruction identity `p = whole·q + leading·Σ(N×cofactor)` by coefficient matching | the irreducibility, pairwise-coprimality, power-set and degree guards |
| `geometry_certify.rs` (`GeometryCertificate`, `:529`) | `cas_geometry_bridge_tests.rs`, `_mul_`, `_frac_`, `_pair_` (8 tests) | `conclusion = Σ cofactorᵢ·generatorᵢ` as a `Rat` ring identity | the **whole non-degeneracy half**: the kernel does not know `d·z − 1` means `d ≠ 0`, and never sees the degenerate witnesses |
| `groebner_cert.rs` (`CofactorOutcome::Reduced`, `:142`) | same geometry bridges (via `certify_by_linear_elimination`) | the cofactor identity, which is monomial-order-independent | `CasIdealCertificate` (`axeyum-solver/src/cas_poly.rs:190`) has no bridge at all |
| `cofactor_ansatz.rs` (`AnsatzOutcome::Solved`, `:108`) | same | same | `NotInDegree(d)` — a decided negative with no certificate type |
| `linear_elim.rs` (`LinearElimination`, `:118`) | same | same | records `powers[i]`, the determinant exponent, which most siblings lose |
| `mvt.rs` (`MvtCertificate`, `:168`) | `cas_mvt_secant_bridge_tests.rs::mvt_secant_endpoints_kernel_checked` | the secant-slope arithmetic at rational endpoints | the witness `c` is an `AlgebraicReal`; no kernel carrier |
| `extremum.rs` (`ExtremumCertificate`, `:195`) | `cas_extremum_deriv_bridge_tests.rs::extremum_deriv_sign_bracket_kernel_checked` | the rational-endpoint derivative sign bracket | comparison of two `RealAlgebraic` values |
| `taylor.rs` (`TaylorCertificate`, `:178`) | `cas_taylor_remainder_bridge_tests.rs::taylor_remainder_lhs_kernel_checked` | the left-hand side `p(b) − T_n(b)` | evaluating a polynomial at an algebraic `ξ` |

### COULD RECONSTRUCT (8 modules) — with the missing piece named

| module | the specific missing piece |
| --- | --- |
| `telescoping.rs` (`TelescopingCertificate`, `:456`) | multivariate `Rat`-coefficient polynomial arithmetic with exact division and GCD over `ℚ[n,k]`, to redo `telescoping_check::symbolic_identity_holds:216`'s cross-multiplication. `rat_prelude/polynomial.rs` is univariate (`Rat.polyEval`, `:433`) and its module doc says explicitly there is **no `polyEval_mul`**. |
| `telescoping_check.rs` | the same, plus integer-root enumeration by the rational-root theorem for `leading_integer_zeros:1439`. |
| `telescoping_json.rs` | the same, plus a JSON reader and an `MvPoly`-shaped term representation to read into. |
| `sturm.rs` | **the first blocker is in the CAS, not the kernel.** `sturm_chain:22` is a local and is discarded; `count_real_roots_in:92` returns `Option<usize>`. Emit the chain as data and the kernel can already evaluate each member with `Rat.polyEval` and compare with `Rat.lt`; then it needs polynomial *remainder* as a coefficient operation to re-derive the chain, and Sturm's theorem itself as an assumed lemma. |
| `normalforms.rs` | the kernel *has* `rat_prelude/matrix.rs`, `matrix_det.rs`, `matrix_invertible.rs`, so `U·A = H` and `det(U) = ±1` are in reach at small fixed dimensions. Missing: an integer divisibility predicate for the invariant-factor chain — **and, more fundamentally, the CAS does not emit those facts at all** (see §3), so there is nothing to hand the kernel. |
| `boolean_circuit.rs` (`BooleanCircuitArtifact`, `:67`) | the kernel has `rat_prelude/decidable.rs` and `boolean.rs`; the missing piece is a bridge test importing `axeyum_cas::boolean_circuit`, of which there is none. **The cheapest `COULD RECONSTRUCT` in the crate.** |
| `sos.rs` + `sos/` | the *identity* half (each `SosSum` expands to its stated target) reduces to the same flat ring-lemma chain the geometry bridges emit, generalized to squares. The *interesting* half — sum of squares with nonnegative weights ⟹ nonnegative at every point of every ordered field — needs an ordered-field nonnegativity predicate over `Rat` that the prelude does not have. |
| `CasIdealCertificate` (`axeyum-solver/src/cas_poly.rs:190`) | a translator from `CasIdealEntry`/`AtomPoly` to the geometry bridges' flat ring-lemma chain, plus sign accounting (`lower`/`real_strict`) which has no kernel analogue. |

### `cas-internal`, with a reason (the rest)

| module(s) | why the kernel cannot re-check this object |
| --- | --- |
| `gosper.rs` | **there is no object.** `gosper_sum:105` returns the antidifference as a bare `CasExpr`; the certification (`certifies_telescoping:371`, `certifies_gosper_equation:328`) runs in-process and returns a `bool` that is discarded. Re-checking means re-running the CAS's own multivariate zero-test — a decision procedure, not a proof object. |
| `lib.rs::integrate` (`CertifiedIntegral`, `:13442`) | the witness is a `MultiPoly` over *atomized* transcendental heads (`ln`, `sin`, `BesselJ`, `sqrt` as opaque atoms) plus a side-relation dictionary built in `equal_core:2293-2340`. The kernel has no transcendental atom, no derivative operator and no `ln`. |
| `ntheory_certify.rs` (4 certificate types) | no `Nat` modular-exponentiation development in `rat_prelude/`; reconstructing the order-of-an-element obligation over unary `Nat` would be `Eq.refl`-shaped, which the fact itself already says. |
| `rationality.rs` (`RationalityCertificate`, `:113`) | needs divisor enumeration and Sturm sign-variation counting; neither exists in `rat_prelude/`. |
| the seven-module GF(2) cluster | there is **no `GF(2)[x]` in this kernel**. Building one is a new prelude, not a translator — unlike every `COULD RECONSTRUCT` row above, there is no bounded piece of work that would move these. |
| `geometry_json.rs`, `geometry_corpus.rs`, `geometry.rs` | a serializer, input data, and concrete `Rational` predicates. None makes a claim of its own. |
| `series.rs` | deliberately compute-only, and says so at `:11-13`. See §3 — this is the most consequential of the deliberate absences. |
| `interval_arith.rs` | exact `Rational` endpoints, no witness object, and no floating point, so there is nothing to certify beyond the arithmetic itself. |
| `algebraic.rs` (`AlgebraicReal`, `:21`) | a representation, not a certificate; its isolation invariant is re-checked by *consumers*, uniformly and to their credit. |
| `groebner.rs` | emits no certificate: `groebner_basis:448` returns `Option<Vec<MvPoly>>`, `ideal_contains:496` returns `Option<bool>`. |
| `inverse.rs` (`InverseCertificate`, `:159`) | strictly this is COULD RECONSTRUCT (missing: algebraic-real comparison), listed here only for reading order; its checker is the best-separated in the crate — `checker_derivative`/`checker_trim`/`checker_shift_by` are deliberately checker-local. |
| `gfp.rs`, `orthopoly.rs`, `combinatorics.rs`, `permutation.rs`, `matrix.rs`, `approx.rs`, `factor_int.rs` | **no certificate object at all.** `factor_int::factor_expr:115` and `permutation:178` both self-check and discard the evidence. For these seven the useful ledger entry is a labelled absence. |

**Counts: 9 reconstruct today (all partial), 8 could reconstruct with a named
missing piece, the remainder `cas-internal`.**

## §3 — Certificates that cannot express a distinction their producer makes

This is the highest-value output of the audit and the reason it was worth
reading code rather than counting greps. The pattern to look for is the one
`nra_monomial_bound_cert` shipped: the producer distinguishes `M < k` from
`M ≤ k`, the certificate records only `k`, and the checker therefore cannot tell
them apart. Mutation testing cannot find these — it measures the guards you
have, and a guard that was never written has nothing to delete.

Ranked by consequence.

**1. `gosper.rs:153` — `rational_gosper_with_ratio` has three acceptance modes
and returns a value recording which one fired nowhere.** Modes A and B (`:184`,
`:187`) return after the **full exact zero-test** certified
`S(k+1) − S(k) ≡ term`. Mode C (`:194`) returns *because the full test did not
certify it*, on the strength of the smaller reduced polynomial identity alone.
The three returns are indistinguishable `CasExpr` values. Two things make mode C
strictly weaker rather than merely cheaper: `certifies_telescoping:371` returns
`false` **both** for `ZeroTest::Unknown` (the overflow case the comment
justifies) **and** for `Certified { equal: false }` — a positively decided
*disagreement* — and line `:194` does not separate them; and mode C returns
`simplified` while nothing has checked that `simplified` agrees with `sum`,
since that check is exactly what failed at `:184`. By contrast
`geometric_gosper:350` has one acceptance mode and demands
`Certified { equal: true }`.

**2. `gf2_shard.rs:245` — `ShardStatus::Exhausted` is accepted on the producer's
word.** "Every sparse candidate at this degree was reducible" is a genuine
negative theorem. `check_shard_directory:178` re-checks `Found` rows thoroughly
(SHA-256 binding, canonical re-parse, both algebraic checkers) and for the other
two arms the entire body is `summary.exhausted += 1`. `candidates_tested` is
never re-derived; there is no witness form for "reducible". A forged manifest
claiming `Exhausted` at a degree where a half-degree irreducible exists passes,
and `--require-all-found` is opt-in so the default invocation does not notice.
The manifest *does* record the enumeration policy that would make re-derivation
possible, which is more than most negative claims here carry.

**3. `telescoping_check.rs:115` + `telescoping_json.rs:218` — the pole count is
computed, used, and then not written.** `confirm_telescoping:571-583` detects
that the certificate denominator `Q` vanishes at an integer window point,
**skips the pointwise identity there** (`poles += 1; continue`) and still returns
`Verified`. The count lands in `CheckReport::certificate_poles_in_window`, which
`write_options:218` does not serialize — the codec writes exactly `samples`,
`window`, `min_ratio_samples`. And there is no floor on `pointwise_samples` at
all (`check_certificate:194` rejects only on `recurrences == 0`), where there
*is* one on `ratio_samples`. **Consequence: a certificate whose `Q` vanishes at
every sampled point, so the pointwise layer ran zero times, and one confirmed at
all 75 grid points produce byte-identical files and the identical
`Verdict::Verified`.** No test asserts `certificate_poles_in_window == 0`. The
ledger already pays for this in an axiom
(`cas.telescoped-term-natural-boundary`), which is honest, but the axiom names
the boundary condition rather than this gap.

**4. `normalforms.rs:399`,`:423` — the producer verifies the factorization and
never the normal form.** `certify_product_equals` + `is_unimodular` check
`U·A = H` (resp. `U·A·V = D`) and `det = ±1`. They do not check
upper-triangularity, positive pivots, reduction of above-pivot entries into
`0..pivot`, diagonality, or **the invariant-factor divisibility chain — the
entire point of the Smith normal form**. `(U, H) = (I, A)` passes as a Hermite
normal form. Every one of those is a producer distinction with no field in the
returned tuple and no check outside the unit tests.
`F:cas-smith-normal-form-two-six-twelve` (landed by this audit) makes one of
those tests load-bearing for a ledger claim; the real fix is a certificate type.

**5. `sturm.rs:87-88` — the half-open `(lower, upper]` convention lives only in
prose.** `count_real_roots_in` counts roots in `(lower, upper]` and the bisection
at `:158-168` *relies* on it. The returned `(Rational, Rational)` is
indistinguishable from a closed interval; a consumer reading `(1,2)` as closed
and a producer meaning `(1,2]` differ on `p(x) = x − 2`, and nothing in the data
adjudicates. `real_algebraic::verify_ivt_certificate` consumes this on trust,
and `rationality.rs`'s `lower`/`upper` carry the same convention *plus* a second
semantics when `lower == upper` (an exact point) — two claims overloaded onto two
fields, disambiguated only by an equality test. This is literally the `<` versus
`≤` shape. Also: `isolate_real_roots:139` calls `squarefree_part`, so
multiplicity is deliberately erased with no field to record it, and
`saturating_sub` at `:100` turns an inverted interval into `Some(0)` —
"no roots" — rather than a decline.

**6. `geometry_certify.rs:723` versus `geometry_check.rs:283-345` — the
degenerate witness's side condition is asserted by the producer and dropped by
the checker.** `subset_is_refuted` requires a witness to satisfy every
hypothesis, **keep every other condition of the subset nonzero**, and falsify a
conclusion. The checker's step 4 drops the middle clause: it checks the
hypotheses vanish, the *named* condition vanishes, and some conclusion is
nonzero. So one witness breaking two conditions at once can be filed under
either, and the checker accepts it as evidence that *that particular* condition
is necessary. `DegenerateWitness` (`:398`) has no field for the distinction.
Separately, minimality — a real claim the producer makes by walking subsets
smallest-first (`certify:777`) — has no field either; the checker verifies each
listed condition is **used** (nonzero cofactor), and used is not needed.
Minimality is pinned out of band, by
`tests/geometry_certificate_artifacts.rs:505`, so a certificate mailed to a third
party carries no minimality claim they can re-check.

**7. `series.rs` versus `taylor.rs` — the same mathematical situation, and only
one records the truncation order.** `series(expr, var, order)` takes the order as
an *input* and returns a bare `CasExpr` that does not record that it is a
truncation, to what order, or that a remainder was discarded. `TaylorCertificate`
(`taylor.rs:186`) has `n` as a field and the checker re-derives `T_n` and
`p⁽ⁿ⁺¹⁾` from `(poly, a, n)`, claiming nothing beyond order `n`. The
consequence for `series.rs` is concrete: the crate's own doc examples
(`series.rs:191`, `:328`) pattern-match `ZeroTest::Certified { equal: true, .. }`
on `equal(&series(f, …, 3), &expected)`, and that verdict certifies **equality of
two order-3 truncations** while the surrounding text reads as certifying an
identity. Nothing in the emitted object stops a downstream caller citing it as
the identity. `taylor.rs` shows the fix twenty files away.

**8. `ratint.rs:378`,`:479` — two well-built independent checkers that are dead
code in production.** `verify_horowitz` and `verify_log_terms` both carry
`#[cfg_attr(not(test), expect(dead_code, …))]` and are called from nowhere
outside their module. `lib.rs::integrate_rational:18371` calls
`ratint::horowitz` and never `verify_horowitz`;
`lib.rs::integrate_log_part:18423` calls `log_terms` and never
`verify_log_terms`. The shipped path is checked only by `prove_derivative`,
which shares `normalize_rational` with the producer. This matters most for
`log_terms`' incompleteness: `rational_roots:264` can return *some* residues when
others are irrational, giving a **wrong** antiderivative, and the completeness
re-derivation (`∏vᵢ == monic(q̄)`, `:519-527`) is exactly the dead code.

**9. `lib.rs:13391-13399` — `prove_derivative`'s half-angle fallback returns a
witness an independent re-checker cannot reproduce.** When the direct test fails
it returns `half_result`, computed on `rewrite_double_angle(expand_trig(·))`-
rewritten expressions rather than on `d/dx F` against the integrand. The returned
`ZeroTest` does not record that a rewrite was applied. Related, and worse in
kind: **a certified equality can depend on an `f64` sign test** —
`equal_core` → `canonicalize_for_equality` → `expand_log_over_primes`'s
positivity side condition is `evalf(e, &[]).is_some_and(|v| v > 0.0)` at
`lib.rs:2238`, inside a path that can yield `Certified { equal: true }`, and the
witness records nothing about it.

**10. `gf2_extension.rs:326` — `ExtensionTraceHankelMinor` does not carry its own
input.** The nonzero Bareiss determinant is the witness; the trace sequence it
was computed from is not a field. A holder cannot re-derive it. That is the one
property a witness must not have, and the fix is cheap.

**11. The decided negatives have no certificate type, anywhere.**
`AnsatzOutcome::NotInDegree(d)` (`cofactor_ansatz.rs:118`),
`groebner::ideal_contains == Some(false)`, and
`ProofOutcome::NotInSaturatedIdeal { remainder }` (`geometry_certify.rs:566`,
which `geometry_json.rs` does not serialize at all) are confident producer claims
no object expresses. Note the degenerate case at `cofactor_ansatz.rs:169-176`:
with an empty generator list and a nonzero target it returns
`NotInDegree(limits.max_cofactor_degree)` — an ideal-level negative dressed in
the vocabulary of a degree slice, with the *caller's ceiling* as its bound.

### Two places where the distinction IS carried, and why they are the models

Worth naming, because "record the distinction as a field" is not the only fix and
is not always the best one.

- **`cas_poly.rs` / `cas_certificate.rs` — re-derivation beats recording.** The
  producer's `Candidate { floor, real_strict }` (`cas_poly.rs:836-845`)
  distinguishes `p > 0` over ℤ (floor 1) from `p > 0` over ℝ (floor 0,
  `real_strict`) from `p ≥ 0`. `CasIdealCertificate` stores **neither** — and
  this is not the failure shape, because `check_cas_ideal_certificate:559-580`
  *rebuilds* `lower` and `real_strict` from the hypothesis itself and applies the
  same verdict table. A field can be forged; a re-derivation cannot.
  `gf2_artifact::validate:203-211` does the same thing with the half-degree
  bound, recomputing `degree / 2` rather than reading the serialized
  `tail_degree_bound`, with the parsed artifact re-rendered and byte-compared.

- **The SOS format expresses strictness as a numeric margin.** `sos.rs` has no
  strictness flag — a sum-of-squares identity gives `≥ 0`, never `> 0`. Where
  strictness is needed the barrier certificate carries an explicit margin
  (`B ≤ −1` and `B ≥ 1`, not `B < 0` and `B > 0`), so a zero-margin certificate
  is a different *file*, rejected, rather than the same file read two ways —
  and `artifacts/instances/sos/negative-controls/barrier-zero-margin.json` is the
  committed control. The Lyapunov certificate does the same with separate
  `lower`/`upper`/`decay` fields and four boundary controls.

### The one good-news finding, stated because the opposite was expected

**There is no floating point anywhere in the SOS subtree.** Grepping `f64|f32`
across `sos.rs` and `sos/*.rs` returns one hit and it is the word "sqrt" in a doc
comment. The PSD test is exact rational LDLᵀ (`sos/psd.rs:53`) with overflow
returning `Psd::Overflow`, a *decline*, never `NotPsd`; the wide path
(`sos/psd_big.rs`) is `BigRational` with explicit bit budgets and also declines.
The serialization encodes every rational as `[numerator, denominator]` and a
decimal point anywhere is a hard parse error (`sos/json.rs:664`), with a
committed `float-coefficient.json` negative control proving the gate bites. The
rounded-versus-exact ambiguity that would be the obvious hazard for an SOS
certificate is **structurally impossible here, not merely absent.**

## What this audit landed in the ledger

Six facts, all `cas-certificate` / `cas-internal`, taking the route from 48 to
54. `scripts/validate-facts.py`: 2529 facts, 0 errors.

| fact | why its `checker_command` cannot pass on a broken run |
| --- | --- |
| `F:cas-sos-motzkin-psd-not-sos` | `sos_certify --expect-checks 5`; measured, `--expect-checks 4` on the **unchanged** honest artifact exits 1, and `motzkin-tampered-square.json` exits 1 |
| `F:cas-sos-damped-rotation-lyapunov` | additionally `--expect-rate 1/26`; `--expect-rate 1/25` on the unchanged artifact exits 1. The rate pin fails a certificate that discharges every obligation but proves a **weaker** bound, which a count pin cannot see |
| `F:cas-sos-energy-barrier-unreachability` | `--expect-checks 6`, plus six committed tampered fixtures the gate asserts are rejected |
| `F:cas-gf2-degree-400-trinomial-irreducible` | two evidence rows, one per checker, with disjoint arithmetic; the paired negative control `independent_checker_rejects_packed_checker_mutations` shows the independent checker can reject |
| `F:cas-ratint-horowitz-x-over-x-minus-one-squared` | two surgical fixtures, each a mutant over an instance where **every other guard passes**; each fixture independently establishes its mutant is genuinely wrong before asserting rejection |
| `F:cas-smith-normal-form-two-six-twelve` | the exact invariant factors `(2,6,12)` are asserted, not merely "some diagonal form exists" |

All six use the shape
`cargo test … -- --exact 2>/dev/null | grep -cE '^test <path> \.\.\. ok$'`.
`grep -c` consumes the pipe so it cannot SIGPIPE, and the count is tested.
Measured on this host: the five real tests give `count=1 exit=0`; a deliberately
absent test gives `count=0 exit=1`. **That last line is the point** — a bare
`cargo test` with a filter matching nothing prints `0 filtered out` and exits 0,
so this shape catches a renamed or deleted test as well as a failing one.

One statement was **weakened after drafting**: the ratint fact initially claimed
the rational part is `−1/(x−1)`. That is true, it follows from the classical
uniqueness of the Horowitz split, and it is *not pinned by the cited tests* —
they pin `deg D₂ = 1` and the five guards. It is now labelled hand-derived
context, explicitly separated from the checked content.

## What did not get done, and by which route

Written as a hypothesis about one route rather than as a property of the target,
because a lane's report of what remains is reliably pessimistic.

- **The thirteen-module gap is now seven.** Facts landed for `sos`, `ratint`,
  `gf2_independent` and (via the GF(2) fact's two rows) `gf2`; `normalforms` and
  `boolean_circuit` were audited, and `normalforms` now has a fact. Still with no
  naming fact: `boolean_circuit`, `geometry_json`, `gf2_artifact`, `gf2_search`,
  `gf2_shard`, `gf2_tensor`, `gosper`, `groebner_cert`, `lib`,
  `telescoping_json`. Of these `boolean_circuit` and `gf2_tensor` are the
  cheapest — both have exhaustive replay checkers that name a counterexample
  (`BooleanCircuitCheck::Failed { input, expected, observed }`,
  `Gf2TensorCheck::Failed { coordinate, expected, observed }`) and both are one
  fact away.
- **No new kernel bridge was attempted.** The `boolean_circuit` bridge is,
  on the reading in the table above, the cheapest available — `rat_prelude` has
  `decidable.rs` and `boolean.rs` and the missing piece is a bridge test
  importing the CAS type. That is a *sizing from reading the two crates*, not
  from trying it.
- **`cargo test --workspace` did not run.** Nothing in this lane touched Rust
  source. `scripts/validate-facts.py` ran and is green at 0 errors;
  `scripts/check-fact-evidence-replay.sh` **did not run** — it executes every
  settled fact's `checker_command` verbatim and would take the full battery, and
  the coordinator re-runs the aggregate gate before merging regardless. Each of
  the six new commands was verified individually, which is the part a lane can
  do and the aggregate cannot substitute for.

## Round two (lane cas-facts-round-two): re-deriving the list, not trusting it

The "thirteen-module gap is now seven" paragraph above names a list that
disagrees with its own count (ten names for "seven"). Rather than resolving
that inconsistency by inspection, this lane re-derived which of the ten named
modules actually have no naming fact today, by checking what each existing
fact's `checker_command` / `evidence.checkers` actually exercises (not just
grepping the module's own filename against fact text — several facts name a
*test file* that imports the module rather than the module's own basename,
which is why a literal string search under-counted).

Re-derived, before this lane's own additions:

| module | status | how |
| --- | --- | --- |
| `boolean_circuit` | closed | `F:cas-boolean-circuit-nand-only-full-adder` |
| `gf2_tensor` | closed | `F:cas-gf2-tensor-karatsuba-degree-2-rank-three` |
| `gf2_artifact` | **closed, previously miscounted** | `F:cas-gf2-tensor-karatsuba-degree-2-rank-three`'s own evidence text names it explicitly as excluded, but `F:gf2-general-monomial-composition-criterion`'s `--test gf2_artifact_cli capell_audit` row directly imports and calls `axeyum_cas::gf2_artifact::{ArtifactLimits, HalfDegreeArtifact, to_canonical_json}` |
| `geometry_json` | **closed, previously miscounted** | 17 `F:geometry-*` facts cite `cargo test -p axeyum-cas --test geometry_certificate_artifacts`, whose test file imports `axeyum_cas::geometry_json::{from_json, to_json}` directly — the fact text never says "geometry_json" but the checker exercises it |
| `telescoping_json` | **closed, previously miscounted** | nine telescoping facts (`F:apery-numbers-recurrence` and siblings) run `cargo test -p axeyum-cas --test telescoping_certificate_artifacts`, which imports `axeyum_cas::telescoping_json::{CertificateDocument, from_json, to_json}` |
| `gf2_search` | open (closed by this lane, see below) | no fact's checker touched it |
| `gf2_shard` | open (closed by this lane, see below) | no fact's checker touched it |
| `gosper` | open (closed by this lane, see below) | no fact's checker touched it |
| `groebner_cert` | open (closed by this lane, see below) | reachable indirectly through the geometry bridges' `certify_by_linear_elimination`, but no fact's checker names its own tests |
| `lib` (`integrate`/`CertifiedIntegral`) | open (closed by this lane, see below) | no fact's checker touched `integrate` specifically |

So the real gap **before this lane** was five modules, not seven or ten:
`gf2_search`, `gf2_shard`, `gosper`, `groebner_cert`, `lib`. Three of the
`cas-internal` ADR-1400 violations §3 named had also been repaired since the
audit was written and were verified by reading the current code, not assumed
from the earlier prose: `gosper.rs` now has a typed `GosperEvidence` recording
which of five acceptance modes fired (§3 finding #1); `gf2_shard.rs` now
re-derives an `Exhausted` claim by re-running `gf2_search::search_sparse_half_degree`
under the manifest's own declared policy rather than trusting the producer's
word (§3 finding #2); and the `f64` sign test §3 finding #9 flagged inside
`equal`'s log-canonicalization path (`evalf(e, &[]).is_some_and(|v| v > 0.0)`)
has been replaced by an exact structural predicate, `is_certainly_positive`,
whose own doc comment explains why the `f64` version was unsound. The
half-angle fallback in finding #9 (an unrecorded rewrite) is **still open** —
this lane's `lib`-naming fact deliberately routes around it rather than
claiming it is fixed.

Four facts landed, closing all five remaining modules (`gf2_search` and
`gf2_shard` share one fact, since the re-derivation in `gf2_shard` calls
`gf2_search` directly):

- `F:cas-gf2-degree-8-trinomial-exhaustion-rederived` — `gf2_shard`, `gf2_search`
- `F:cas-gosper-acceptance-mode-distinguishes-geometric-from-telescoping` — `gosper`
- `F:cas-groebner-cofactor-unit-ideal-witness` — `groebner_cert`
- `F:cas-lib-integrate-polynomial-certified` — `lib`

**The thirteen-module gap from the original audit is now genuinely zero** —
every module the audit's masked certificate-surface query flagged is named by
at least one fact's evidence, whether or not that fact's own prose happens to
contain the module's filename. `scripts/validate-facts.py`: 2536 facts, 0
errors; `cas-certificate` routes now 60 (46 `cas-internal`, 14
`kernel-reconstructed`), up from 56.

What this round did NOT do, each marked by why: no new kernel bridge was
attempted (same reasoning as the first round — every `COULD RECONSTRUCT` row
above is a sizing from reading the crate, not from trying it); `gosper`'s
`ReducedGosperIdentity` fallback mode — the specific case §3 finding #1 was
most worried about — is asserted to fire by a comment in
`weighted_vandermonde_wz_term_uses_reduced_certificate`, but that test never
inspects `.evidence`, so this round's fact does not claim to have exercised it
and neither should a reader infer it from the comment alone; `cargo test
--workspace` did not run (no Rust source was touched); each of the four new
`checker_command`s was verified individually, both for a real test path and a
deliberately wrong one.

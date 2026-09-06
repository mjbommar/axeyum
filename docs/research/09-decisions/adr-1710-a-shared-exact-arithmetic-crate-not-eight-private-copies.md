# ADR-1710: A shared exact-arithmetic crate `axeyum-arith` on `num-bigint`, not eight private copies

Index-summary: Adds `axeyum-arith` below `axeyum-ir` as the shared exact-arithmetic layer — measured eight duplicated ℚ[x] implementations, six Sturm chains, five `pow_mod`s and six exact Gauss–Jordans; priced `malachite`/`dashu` against `deny.toml` and shipped a certified `Dyadic`/`Radix` interface sketch
Index-status: Proposed
Status: proposed
Date: 2026-09-05
Lane: `arith-design`

**Extends:** [ADR-1670](adr-1670-i128-fast-path-with-a-big-integer-overflow-fallback-for-the-cas-zero-test.md),
[ADR-1702](adr-1702-rational-i128-fast-path-bignum-slow-path.md).
**Supersedes:** nothing.
Design note: [`docs/research/10-cas/axeyum-arith-design.md`](../10-cas/axeyum-arith-design.md).

## Context

Two ADRs landed on 2026-09-05 about the width of the CAS coefficient type.
ADR-1670 measured the `i128` wall and kept `Rational` at the API with an
unbounded zero-test underneath. ADR-1702 gave `axeyum_ir::Rational` an opt-in
`wide_*` family after discovering that a *global* widening breaks
`axeyum-cas`, which uses `i128` exhaustion as a termination argument: 25 unit
tests failed and about seven stopped terminating.

Both are about **the coefficient type**. Neither addresses **the algorithms
underneath it**, and that is where the measured waste is.
[`13-computer-algebra.md`](../../math-department/13-computer-algebra.md) names
the pattern — *"Every module that needed more precision grew its own
`BigRational` path beside the core"* — but records it as a count of modules,
not as a list of what each one re-derived.

This lane made that list. Every entry was read, not grepped.

## The measurement

| duplicate family | copies | where |
|---|---|---|
| univariate polynomial over ℚ (or an equivalent ring) | **8** — five over `BigRational`, one over `BigInt`, two over i128 `Rational` | `qe_big.rs`, `numberfield.rs`, `fps_analytic.rs`, `qe_fibre.rs`, `ir/poly_big.rs`, `mvpoly/big.rs`, `ir/poly.rs`, `ratint.rs` (+ two derived layers: `qe_bivariate.rs` ℚ[x][y] and `qe_fibre.rs` K[y], each re-deriving its own divmod/gcd/derivative/Sturm at its own level) |
| Sturm chain | **6** | `qe_big.rs:266`, `qe_fibre.rs:703`, `fps_analytic.rs:1018`, `sturm.rs:22`, `ir/poly.rs:343`, `ir/poly_big.rs:297` |
| extended Euclid over ℚ[x] | **3** (two sharing a name *and* a signature) | `numberfield.rs:460` `poly_ext_gcd`, `fps_analytic.rs:828` `poly_ext_gcd`, `qe_fibre.rs:293` `xgcd` (half-extended) |
| modular exponentiation | **5** | `ntheory.rs:60`, `ntheory.rs:374`, `ntheory_certify.rs:77`, `gfp.rs:343`, `factor_int.rs:462` |
| exact Gauss–Jordan / determinant / null space | **6** + `matrix::Matrix::rref` | `enclosure_special.rs:859`, `ratint.rs:48`/`:99`, `fps.rs:1328`, `numberfield.rs:531`, `gfp.rs:534`, `factor_int.rs:550` |
| 𝔽ₚ[x] ring | **2** independent | `gfp.rs`, and `factor_int.rs:336`–`:628`'s local `fp_*` block |

Two further facts from the same pass:

- **`fps_analytic.rs` imports nothing from `qe`**, and its
  `poly_trim/degree/add/mul/scale/eval/derivative/divrem/monic/gcd/squarefree`
  plus its Sturm chain are the same routines as `qe_big.rs:74`–`:342`,
  independently written. Its chain normalizes members to primitive integer
  polynomials; `qe_big.rs`'s does not. **That difference is why a naive merge
  would be wrong**, and why the design note splits that slice five ways.
- `num-bigint`, `num-rational`, `num-integer` and `num-traits` are pinned
  **literally in four member manifests** and are absent from the root
  `[workspace.dependencies]`.

The full table, with a file:line for every cell, is in
[the design note §2](../10-cas/axeyum-arith-design.md).

## Decision

**Add `axeyum-arith` as a new workspace member below `axeyum-ir`: the shared
exact-arithmetic layer, on `num-bigint` and `num-rational` only, pure Rust,
`wasm32`-clean, with a certificate on every operation whose result a caller
could re-derive.**

Landed in this slice, with tests:

- `Dyadic` — exact `mantissa · 2^exponent`, canonical odd mantissa, five
  rounding directions, `round_outward` as the single interval-facing entry,
  exact `to_rational` and single-rounding `from_rational`, and an explicit
  width contract (`MAX_ALIGN_BITS`, `align_cost_bits`, `checked_*`) so an
  exact operation declines rather than allocating without bound.
- `Radix` / `RadixCertificate` and `MixedRadix` / `MixedRadixCertificate` —
  positional notation in any base `b ≥ 2` (the base is a `BigUint`, so `2^k`
  is expressible), with a `verify` that re-derives the value by Horner and
  trusts nothing the producer computed.

Signature-only, each naming its migration slice: `Normalize` +
`NormalizationReceipt`, `UnivariatePoly`, `FractionFree`,
`BezoutCertificate`, `SturmCertificate`, `ModularRing` +
`PowModCertificate`, `HenselLift`, `AlgebraicNumber`.

**No existing crate depends on it in this slice.** The migration is eight
lanes, ordered in the design note §8, each with a differential test against
the copy it replaces.

Two placement decisions taken here rather than deferred:

- **`AlgebraicNumber` lands as a trait; the two concrete carriers stay put.**
  `axeyum_ir::RealAlgebraic` (`real_algebraic.rs:84`) and
  `poly_big::BigAlgebraic` (`poly_big.rs:71`) are the same triple, but
  `RealAlgebraic` is a variant of `axeyum_ir::Value` (`value.rs:45`) and moving
  it is a public IR type change — the churn ADR-1702 declined for `Rational`.
- **`NumberFieldElement` stays in `axeyum-cas`.** `qe_fibre.rs`'s on-demand
  modulus splitting (`:524`, `:533`, `Inner::Split` `:217`) is a decision
  procedure's control flow, not arithmetic. What moves is the half-extended
  Euclid under it, with the non-unit gcd as a first-class *outcome*.

## The option table

Priced against the inventory above and the ecosystem survey in the design
note §3.1.

| option | what it costs | what it buys | verdict |
|---|---|---|---|
| **(a) Keep the eight private copies** | Nothing today. Every future lane pays the re-derivation, and each copy carries its own bug surface — `fps_analytic.rs:2672` exists precisely because two of them disagreed | Zero risk to five in-flight lanes | **Rejected.** The department file has ranked this first of ten for two months and nothing in the tree has moved |
| **(b) Consolidate on `num-bigint` (this ADR)** | One new crate; eight migration lanes; each must preserve a bound that today is `i128` exhaustion or a `Cost` budget | One implementation, one certificate discipline, one benchmark. No new dependency, no new registry version, no license question, `wasm32` unchanged | **Accepted** |
| **(c) Adopt `malachite`** | **`cargo deny check` goes red.** `deny.toml`'s `[licenses] allow` list is MIT / Apache-2.0 / Apache-2.0-WITH-LLVM-exception / BSD-2 / BSD-3 / ISC / Unicode-3.0 / Unicode-DFS-2016 / Zlib / bzip2-1.0.6 / CC0-1.0 / CDLA-Permissive-2.0. `LGPL-3.0-only` is not there. Rust statically links, so LGPL-3.0 §4d1's shared-library escape is unavailable — least of all for `wasm32-unknown-unknown`. Plus a rewrite of ~18 files off `num_rational::Ratio<BigInt>` | Genuinely the best pure-Rust engine: subquadratic half-gcd (`HGCD_THRESHOLD 140`), FFT at 450 limbs, Barrett/Newton division, **arbitrary-`Natural`-base divide-and-conquer radix conversion**, `forbid(unsafe_code)`, `u64` limbs even on wasm32 | **Rejected**, and it is not a lane's decision to reverse — it needs its own ADR, a `deny.toml` change, and a redistribution obligation |
| **(d) Adopt `dashu`** | Same ~18-file rewrite off `BigRational`; ~102 `unsafe` sites in `dashu-int`; still Lehmer gcd, no half-gcd; its arbitrary-base `to_digits`/`from_digits` is quadratic | MIT OR Apache-2.0. Released NTT multiplication above 4 000 words, Burnikel–Ziegler division, Lehmer gcd, a whole ℤ/ℚ/ℝ tower at one version, and a `fuzz/` suite with a `rug`(GMP) differential oracle — the closest thing in the ecosystem to this repository's own discipline | **Deferred, not rejected.** Re-open when a design-note §7 benchmark shows the base layer is the bottleneck. `axeyum-arith`'s trait boundary is what makes the swap a crate-local change rather than an 18-file one |
| **(e) Write the integers ourselves** | Möller's own line counts: 1 967 lines / cyclomatic complexity 292 for the Schönhage-1971 gcd route, 733 / 133 for his; and *"it is seldom spelled out in detail in textbooks, and when it is, it has been plagued by errors"* | Full control of the trusted base | **Rejected.** Nothing in the flywheel needs `BigUint` to be trusted — the kernel checks *certificates*, not the search |

The choice between (b) and (d) is deliberately **not** made on today's
benchmark, because there is no honest one to make it on: no published
cross-library benchmark covers post-NTT `dashu` (the NTT shipped in
`dashu-int` 0.4.3 on 2026-06-21; both public benchmark suites pin 0.4.2), and
the dev box is under concurrent-lane load. The design note §7 names the
measurement that would decide it.

## Evidence

**In-tree, read at `0d4209d29` + the lane's own commits.** Every file:line in
the measurement table above was opened. The load-bearing ones were re-verified
by hand after the sub-agent pass: the six Sturm chain definitions, the three
ext-gcds, the five `pow_mod`s, `mvpoly/big.rs`'s `gcd` `:584` and `normalized`
`:552`, `ir/poly_big.rs`'s full function list, and `deny.toml`'s allow list.

**`num-bigint` 0.4.6 — the version `Cargo.lock` actually resolves — read from
the vendored source**, not from the 0.5.1 docs:

| property | source |
|---|---|
| schoolbook ≤32 limbs, half-Karatsuba, Karatsuba ≤256, **Toom-3 ceiling, no FFT** | `src/biguint/multiplication.rs:101, 107, 165, 279` |
| **Stein's binary gcd** (no Lehmer, no half-gcd) | `src/biguint.rs:227` |
| **Knuth Algorithm D division only**, no Burnikel–Ziegler | `src/biguint/division.rs:190, 232, 251` |
| radix 2..=256 for byte digits, 2..=36 for strings; **no divide-and-conquer symbol in 0.4.6** | `src/biguint/convert.rs:158, 222` |

So the base layer's leverage is *not* in tuning a threshold — it is in calling
the underlying multiply less often, which is what fraction-free elimination
and on-demand normalization buy. ADR-1670 already measured that effect
in-tree: at the one comparison that isolates the ring, `BigInt` coefficients
are 6% *cheaper* than `i128` rationals by degree 64 and still opening the gap,
*"because every `Rational::checked_mul` runs a Euclidean gcd to renormalize,
on every coefficient, on every product; the integer ring pays no gcd at all."*

**Literature.** Full citations in the design note §3.2. Four premises this
lane started with turned out to be **wrong**, and are recorded rather than
quietly dropped:

1. GMP's *Rational Internals* argues **for** eager normalization
   (*"better to do a few small ones immediately than to delay and have to do a
   big one later"*), not against it; the pro-laziness sentence is in the
   Efficiency chapter and is scoped to forming a big product.
2. **Bernstein has no note on binary/decimal conversion**, and *"Fast
   multiplication and its applications"* has no section on radix conversion —
   base conversion appears once, in §12.7 *History*, p. 350. Cite
   Brent–Zimmermann *Modern Computer Arithmetic* §1.7.2 and GMP §15.6 instead.
3. **`Nat.binaryRec` is Mathlib, not Lean 4 core**
   (`Mathlib/Data/Nat/BinaryRec.lean:88`).
4. **A radix certificate is not cheaper to *run* than the conversion** —
   Horner is Θ(n²), a divide-and-conquer producer is O(M(n) log n). What it
   makes small is the *trusted code surface*.

**Gates run, with counts rather than the word "passed":**

| gate | result |
|---|---|
| `scripts/cargo-serialized.sh check -p axeyum-arith` | exit 0 |
| `scripts/cargo-serialized.sh clippy -p axeyum-arith --all-targets -- -D warnings` | exit 0 |
| `scripts/cargo-serialized.sh test -p axeyum-arith --lib` | **25 passed, 0 failed, 0 ignored** |
| `rustfmt --edition 2024 crates/axeyum-arith/src/lib.rs` | clean |
| `./scripts/check-links.sh` | see the lane's report |

The five forgery cases in `forged_radix_certificates_all_fail_verification`
are the crate's own answer to *a checker that cannot fail is worse than no
checker*: each of `RadixCertificate::verify`'s four conditions has a test that
defeats only it, and the fourth case is an out-of-range digit arranged so that
**Horner evaluation still reproduces the value** — the case a value-only check
would pass.

## Alternatives

See the option table. Two narrower alternatives also considered and rejected:

- **Put the shared code in `axeyum-ir` rather than a new crate.**
  `axeyum-ir` is the term IR — sorts, arena, interning, evaluation. Adding
  Sturm sequences, Hensel lifting and modular rings to it makes the IR's
  dependency surface the union of every consumer's arithmetic needs, and
  `axeyum-fp` and `axeyum-lean-kernel` would then depend on the term arena to
  get a rounding mode. ADR-0001's rule cuts the other way here: the boundary
  is proven by eight committed duplicates.
- **Make the coefficient ring generic instead of adding a crate.** ADR-1670
  priced this as option (c) and rejected it: *"it turns each of the same 71
  signatures generic and pushes monomorphization into every consumer."* That
  judgement is unchanged, and this ADR does not reopen it — `axeyum-arith`
  ships concrete carriers, not a generic ring.

## Consequences

**Easier.** A ninth lane that needs a Sturm chain has one to call. A
certificate discipline exists in one place rather than being re-argued per
module. Swapping the bignum base layer becomes a crate-local change. The
`RadixCertificate` gives the kernel-numeral bridge (design note §9) a concrete
Rust-side artifact to build the prelude theorem against.

**Harder, and named.** Eight migration lanes, each of which must preserve a
resource bound that today is often `i128` exhaustion or a `Cost` budget —
ADR-1702's lesson applies to every one of them: **a slice that removes a bound
must add one, and its test must name the input that would otherwise run away.**
Slice 4 (five Sturm chains with two different normalization conventions) is the
largest single risk in the plan and is deliberately not scheduled first.

**Revisited when.** (i) A design-note §7 benchmark shows `num-bigint`'s
Toom-3 ceiling or Stein gcd dominating a real workload — then option (d).
(ii) The determinant certificate hole is closed by the Zhou–Jeffrey
`PA = L D⁻¹ U` form, which also removes the reason `matrix.rs:18` gives for
not using Bareiss over `CasExpr`. (iii) A prelude lane lands `Nat.ofDigits`
and the `norm_digits`-shaped step lemma, at which point ADR-1622's modulus
ceiling stops being about the size of `101`.

### `ir/poly_big.rs` is a public IR change, not a migration slice (added by slice 4)

Migration slice 4 was asked to take `ratint.rs`, `qe_fibre.rs`'s K[y] layer and
`ir/poly.rs`, and to stop before `ir/poly_big.rs`. It stopped, and this is the
paragraph the coordinator decides from. It is deliberately **not** a new ADR
number: nothing here is decided yet.

**What the move would change for `axeyum_ir::Value`.** `poly_big::BigAlgebraic`
(`poly_big.rs:71`) and `real_algebraic::Repr` (`real_algebraic.rs:96`) are the
same three fields — `Vec<BigInt>` plus two `BigRational` endpoints — and
`RealAlgebraic::combine` destructures one straight into the other
(`real_algebraic.rs:384`). `RealAlgebraic` is a variant of `axeyum_ir::Value`
(`value.rs:45`), so the storage type is reachable from the IR's public value
enum. Moving `poly_big` to `axeyum-arith` therefore does one of two things:
either `axeyum-arith` gains the carrier and `axeyum-ir` re-exports it — which
puts a second crate's type inside `Value` — or the carrier stays and only the
*algorithms* move, which is the cheaper half and the one worth pricing.

The move also has a **dependency-graph consequence that is larger than the
diff**. `axeyum-arith` depends on `num-bigint` and `num-rational` and on nothing
else (`crates/axeyum-arith/Cargo.toml`), so there is no cycle: `axeyum-ir` may
depend on `axeyum-arith`. But `axeyum-arith` is today a dependency of exactly one
crate, `axeyum-cas`. Adding the `axeyum-ir → axeyum-arith` edge puts
`axeyum-arith` beneath **every** crate in the workspace, because everything
depends on `axeyum-ir`. That is a placement decision, not a refactor.

**Who consumes it, grepped rather than remembered.** `BigAlgebraic`, `Combine`
and `combine_retry` have exactly one consumer in the tree:
`crates/axeyum-ir/src/real_algebraic.rs`. Nothing outside `axeyum-ir` names them.
`RealAlgebraic` itself — the type that would inherit any carrier change — is
named in 21 files outside `axeyum-ir`, across `axeyum-cas` (`extremum`,
`inverse`, `mvt`, `taylor`, `real_algebraic`), `axeyum-solver` (`nra_real_root`,
`smtlib`, `auto`, `support_matrix`, `capabilities`, and five test files),
`axeyum-rewrite`, `axeyum-property`, and `axeyum-py`'s `convert.rs`
`RealAlgebraicValue` binding. One further consumer the earlier inventory missed:
`big_determinant` is `#[doc(hidden)] pub` and is called **in production from
another crate**, at `crates/axeyum-cas/src/fps_analytic.rs:994`. So
`poly_big`'s cross-crate surface is not one test; it is one test plus one CAS
hot path.

**Two bounds would have to be replaced, not dropped.** `poly_big` terminates on
`BIG_MAX_SYLVESTER_DIM = 24`, `BIG_MAX_DEGREE_GUARD` and
`BIG_COMBINE_REFINE_ROUNDS = 200` (`poly_big.rs:51`–`:56`). `axeyum-arith`'s only
comparable knob is `DEFAULT_ISOLATION_STEPS`, which bounds root isolation and
nothing else. This is the standing rule above: a slice that removes a bound must
add one.

**One differential test must not lose both arms.**
`crates/axeyum-ir/tests/sylvester_determinant_diff_bignum.rs` compares
`big_determinant` against `big_determinant_leibniz`. Both live in `poly_big.rs`.
Replacing them with a single shared routine makes that test compare the shared
code against itself — the same defect slice 3 avoided by leaving `sturm.rs` in
place.

**The two options.**

- **(A) Move the algorithms, keep the carrier.** `poly_big`'s Sturm chain,
  Euclidean gcd, squarefree part, Bareiss determinant and Newton interpolation
  are already over `BigRational` and are type-compatible with
  `axeyum_arith::{QPoly, SturmChain}`. `BigAlgebraic`, `Combine` and
  `combine_retry` stay in `axeyum-ir`, so `Value` does not change and no crate
  outside `axeyum-ir` recompiles differently. Costs: the new
  `axeyum-ir → axeyum-arith` edge; explicit replacements for the three caps;
  keeping one determinant arm private to `poly_big` so the differential test
  survives. Buys: two of the six inventoried Sturm chains and one of the
  duplicate Bareiss routines, with no public surface change.
- **(B) Move the carrier too.** `BigAlgebraic` becomes
  `axeyum_arith::AlgebraicNumber`'s concrete carrier and `axeyum_ir::Value`
  stores it. Costs: a public IR type change across 21 files including the
  Python binding, which is precisely the churn ADR-1702 declined for
  `Rational`, plus everything in (A). Buys: one algebraic-number representation
  in the workspace instead of two, which is what the `AlgebraicNumber` trait was
  a placeholder for.

Slice 4's own recommendation is **(A)**, and only after the three copies below
are settled — but the choice is the coordinator's, not a lane's.

### What slice 4 measured about the other three copies

All three were opened rather than grepped, and all three **stopped**. Recording
why, so the next lane does not re-derive it (the standing cost in CLAUDE.md):

- **`ratint.rs` has no ℚ[x] layer of its own to migrate.** Its module doc says
  so — *"Everything here operates on `poly.rs`'s public exact primitives"* — and
  the file confirms it: `divrem` (`:37`) is three calls into `axeyum_ir::poly`,
  and `is_zero`/`monomial` are one-liners. What it privately owns is the
  **Gauss–Jordan pair** `solve_linear_i128`/`solve_linear_big` (`:53`, `:99`),
  which is the *linear-algebra* row of the inventory above, not the ℚ[x] row —
  and `axeyum-arith` has no linear algebra at all today. So this copy is not
  slice-4 work; it is the `PA = LD⁻¹U` slice, and it needs a home built first.
- **`qe_fibre.rs`'s K[y] layer is not univariate over a field.** `K = ℚ[x]/(m)`
  with `m` deliberately allowed to be **reducible** (`RealField`, `:346`), so
  `invert` (`:500`) has three outcomes and one of them, `Inner::Split`, means
  *"abandon this computation, the ambient ring was wrong"*. `ktrim` (`:538`) is
  partial for the same reason: deciding whether a leading coefficient is zero is
  deciding a sign at α. A generic `UPoly<F>` cannot host this — it would need a
  *ring-object* trait whose `inv` **and** `is_zero` are both fallible and whose
  error can demand a different ring. That is the control flow this ADR already
  placed outside the arithmetic layer. The cheaper shared piece, if one is
  wanted later, is a `SturmChain` generic over a **sign oracle** rather than over
  a coefficient field: that would absorb `KSturm` (`:667`) and `qe_big`'s chain
  together.
- **`ir/poly.rs` is the i128 differential oracle, and migrating it dissolves
  three test families.** `crates/axeyum-cas/src/sturm.rs:16`–`:41` already
  records this decision for the Sturm chain, and `sturm.rs` is built entirely on
  `poly::{rat_trim, rat_degree, rat_derivative, rat_rem, squarefree_part,
  eval_rat_poly}` — so migrating `poly.rs` migrates `sturm.rs` transitively and
  makes `fps_analytic`'s `bignum_and_machine_sturm_counts_agree`,
  `sturm.rs`'s own `shared_and_machine_routes_agree_where_both_answer`, and
  `nra_real_root`'s `real_algebra_parity` compare the shared chain against
  itself. Second and independent: every `None` in `poly.rs` is an **overflow
  decline** that callers branch on (`RootCounter::Machine` falls through to the
  bignum chain on `None`), and `axeyum_arith`'s carriers cannot produce one.
  Migrating is therefore the global widening ADR-1702 measured and rejected —
  25 failing tests and about seven non-terminating ones — arriving by a
  different door.

# Decision Records

Status: draft
Last updated: 2026-06-11

## Purpose

The research-questions register says every open question should resolve into
"an ADR, benchmark, implementation result, or explicit deferral" — this
directory is where those resolutions live. Research notes describe the option
space; decision records close questions.

## Process

- One file per decision: `adr-NNNN-short-slug.md`, numbered sequentially.
- Status is one of: `proposed`, `accepted`, `superseded by adr-NNNN`,
  `deferred`.
- Each ADR links the research-questions entries it closes; the closed
  question in `08-planning/research-questions.md` gets a link back.
- ADRs are immutable once accepted; reversals get a new ADR that supersedes
  the old one.

## Template

```markdown
# ADR-NNNN: Title

Status: proposed | accepted | superseded by adr-NNNN | deferred
Date: YYYY-MM-DD

## Context

What question this closes and why it must be decided now.
Link the research notes and register entries involved.

## Decision

The decision, stated as a single committed sentence, then detail.

## Evidence

Benchmarks, prototypes, references, or reasoning that justified it.

## Alternatives

What was rejected and why.

## Consequences

What becomes easier, what becomes harder, what gets revisited and when.
```

## Index

| ADR | Title | Status |
|---|---|---|
| [0001](adr-0001-vertical-slice-first.md) | Vertical slice before horizontal layers | accepted |
| [0002](adr-0002-ground-up-identity-oracle-bootstrap.md) | Ground-up identity, oracle as bootstrap scaffolding | accepted |
| [0003](adr-0003-m0-ir-representation.md) | M0 IR representation choices | accepted |
| [0004](adr-0004-defer-second-native-backend.md) | Defer the second native backend | accepted |
| [0005](adr-0005-phase3-query-evidence-rewrite-contracts.md) | Phase 3 query, evidence, and rewrite contracts | accepted |
| [0006](adr-0006-phase4-bit-order-and-lowering-entry-contract.md) | Phase 4 bit order and lowering entry contract | accepted |
| [0007](adr-0007-first-pure-rust-sat-adapter.md) | First pure Rust SAT adapter | accepted |
| [0008](adr-0008-consumer-scenario-models.md) | Consumer scenario models for testing and optimization | accepted |
| [0009](adr-0009-incremental-sat-and-solving.md) | Incremental SAT and incremental solving | accepted |
| [0010](adr-0010-arrays-via-eager-elimination.md) | Arrays (QF_ABV) via eager elimination to QF_BV | accepted |
| [0011](adr-0011-drat-unsat-proof-checking.md) | DRAT UNSAT proof format with an in-tree checker | accepted |
| [0012](adr-0012-proof-producing-sat-core.md) | First proof-producing pure-Rust SAT core | accepted |
| [0013](adr-0013-uninterpreted-functions.md) | Uninterpreted functions (EUF) via Ackermann reduction | accepted |
| [0014](adr-0014-first-arithmetic-fragment.md) | First arithmetic fragment: linear integer arithmetic, bit-blasted | accepted |
| [0015](adr-0015-linear-real-arithmetic.md) | Linear real arithmetic via exact-rational simplex | accepted |
| [0016](adr-0016-quantifiers-binder-representation.md) | Quantifiers: named binders and finite-domain semantics | accepted |
| [0017](adr-0017-wasm-target-support.md) | WebAssembly as a supported target (browser + WASI) | accepted |
| [0018](adr-0018-smtlib-text-front-door.md) | SMT-LIB text front door (`solve_smtlib`) in the solver crate | accepted |
| [0019](adr-0019-swappable-solving-strategies.md) | Swappable solving strategies (high-memory eager vs low-memory oracle) | accepted |
| [0020](adr-0020-unbounded-lia-branch-and-bound.md) | Unbounded QF_LIA via branch-and-bound over the simplex | accepted |
| [0021](adr-0021-boolean-structured-lia-dpll.md) | Boolean-structured QF_LIA via lazy-SMT over the integer simplex | accepted |
| [0022](adr-0022-first-class-datatype-sort.md) | First-class datatype sort in the IR (recursive datatypes) | accepted |
| [0023](adr-0023-floating-point-bv-lowering.md) | Floating-point (IEEE 754) as bit-vector formula builders, non-arithmetic core first | accepted |
| [0024](adr-0024-nra-linear-abstraction.md) | Nonlinear real arithmetic via linear abstraction + replay (sound, incomplete) | accepted |
| [0025](adr-0025-bounded-strings-bv-lowering.md) | Bounded-length strings by bit-vector lowering (BMC fragment) | accepted |
| [0026](adr-0026-first-class-float-sort.md) | First-class floating-point sort in the IR (disambiguates FP conversions) | accepted |
| [0027](adr-0027-milp-branch-and-bound.md) | Mixed integer/real arithmetic by branch-and-bound over the Farkas-checked LRA engine | accepted |
| [0028](adr-0028-fp-arithmetic-validation-oracle.md) | A software-float oracle (`rustc_apfloat`) for validating wide-format FP arithmetic | accepted |
| [0029](adr-0029-smtlib-string-front-end.md) | SMT-LIB string front-end over the bounded-string BV lowering (equality slice done; full str.* deferred) | accepted |
| [0030](adr-0030-incremental-lazy-arrays.md) | Incremental arrays for symbolic memory (eager-route slice done; warm lazy deferred) | accepted |
| [0031](adr-0031-reduction-trust-ledger.md) | Reduction trust ledger (typed, countable trust holes) | accepted |
| [0032](adr-0032-egraph-crate.md) | Standalone congruence-closure e-graph crate (`axeyum-egraph`) | accepted |
| [0033](adr-0033-double-duty-educational-artifacts.md) | Double-duty educational artifacts (test/benchmark = curriculum) | accepted |
| [0034](adr-0034-word-level-preprocessing-default.md) | Word-level preprocessing is opt-in, default-off pending broad-corpus measurement | accepted |
| [0035](adr-0035-cdcl-xor-search-acceleration.md) | CDCL(XOR) search acceleration with a ledgered `XorGaussian` trust hole | accepted |
| [0036](adr-0036-lean-kernel-crate.md) | Standalone in-tree Lean kernel crate (`axeyum-lean-kernel`), ported from nanoda | accepted |
| [0037](adr-0037-destination-2-reduction-over-custom-core.md) | Destination-2 priority is word-level reduction, not a custom default SAT core | accepted |
| [0038](adr-0038-real-algebraic-numbers.md) | Real algebraic numbers (defining poly + isolating interval); single-variable NRA decider with irrational witnesses (slice 1) | accepted |
| [0039](adr-0039-degree-2-sos-psd-certificate.md) | Degree-2 sum-of-squares / PSD nonnegativity certificate for NRA (multivariate AM–GM and globally-(non)negative quadratic forms decide Unsat exactly) | accepted |
| [0040](adr-0040-sos-lean-reconstruction.md) | SOS certificate → Lean reconstruction via minimal commutative-ordered-ring axioms + a degree-2 ring normalizer (kernel-checked proof for the SOS unsat route) | accepted |
| [0041](adr-0041-lean-backed-sos-evidence.md) | Lean-backed SOS evidence — the SOS unsat's `Evidence::UnsatSos` carries its kernel-checked Lean module, re-derived+re-checked on `Evidence::check` | accepted |
| [0042](adr-0042-integer-prelude.md) | Integer prelude (discretely-ordered commutative ring + `no_int_between`) — the trusted-kernel foundation for integer-arithmetic / Diophantine Lean reconstruction | accepted |
| [0043](adr-0043-lean-backed-diophantine-evidence.md) | Lean-backed Diophantine evidence — integer-infeasibility `Evidence::UnsatDiophantine` carries a self-check + kernel-checked Lean module; `TrustId::Diophantine` | accepted |
| [0044](adr-0044-algebraic-field-arithmetic.md) | Algebraic field arithmetic (α±β, α·β, −α) on `RealAlgebraic` in the IR value layer; moves the exact-poly + Sturm primitives down to `axeyum-ir` (one isolation impl); `eval` upgrades from `Err` to computed — the multivariate unlock | accepted |
| [0045](adr-0045-bignum-algebraic-path.md) | Arbitrary-precision (`num-bigint`/`num-rational`, pure Rust, feature-gated `bignum`) on the algebraic path — intermediate resultant/Sturm overflow becomes a decision; core i128 `Rational` untouched; the prerequisite for a useful CAD/nlsat | accepted |
| [0046](adr-0046-bignum-real-algebraic-value.md) | Bignum `Value::RealAlgebraic` — unconditional `num-bigint`/`num-rational` storage (`Vec<BigInt>` + `BigRational`); removes the i128-storage ceiling so higher-degree coupled NRA decides; collapses the i128/retry split; supersedes ADR-0045's `bignum` feature gate | accepted |
| [0047](adr-0047-craig-interpolation-proof-based.md) | Craig interpolation as a verified proof transform — read the interpolant off the already-checked Farkas (LRA) / congruence-explanation (EUF) refutation, re-verify the three Craig conditions before returning, decline otherwise; partial generator kept sound by the verify-before-return contract | accepted |

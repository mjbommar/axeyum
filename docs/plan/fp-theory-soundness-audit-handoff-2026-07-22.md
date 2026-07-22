# Floating-point soundness audit: state and resume handoff

Date: 2026-07-22

Work stream: SMT-LIB floating-point soundness and completeness audit

Primary repository: `/home/mjbommar/projects/personal/axeyum`

Development branch used for the audit: `repro/smtcomp-scoring`

Severity: P0 soundness repair plus follow-on completeness work

## Executive state

The full-library inventory found a genuine wrong-`sat` in a QF_ABVFP KLEE
benchmark. Axeyum returned `sat`; the benchmark status, cvc5, and Bitwuzla all
returned `unsat`. The arrays-free QF_BVFP twin failed in the same way, isolating
the original defect to the floating-point path rather than array combination.
The immediate cause was exact finite cancellation under RTN: Axeyum forced
`+0`, while SMT-LIB/IEEE semantics require `-0` for round-toward-negative.

The initial cancellation defect is repaired in both add and FMA, and the two
preserved full queries now return `unsat`. A broader source audit then found
several independent semantic hazards. The current working tree contains repairs
for the high-risk carrier, overflow, congruence, and Float128 paths, together
with focused unit, parser, trust-ledger, and end-to-end tests.

This work stream is not a claim that FP is at parity. The previous “already near
parity” wording was removed from the P2.8 plan. Broad operator availability is
real; complete SMT-LIB semantics, proof assurance, all-mode oracle coverage, and
full-corpus performance remain separate obligations.

## Preserved incident

The original artifacts are under:

- `bench-results/smtcomp-full-library-20260722/soundness-fp-wrong-sat/`
- `corpus/regression/qf_fp/unsat_rtn_exact_cancellation_sign.smt2`

The preserved full cases are:

- `qf_abvfp_query.26.smt2`
- `qf_bvfp_query.26.smt2`

Root cause: exact nonzero cancellation in `fp.add RTN` selected the wrong signed
zero. FMA carried the same latent convention. This was a genuine soundness bug,
not a timeout, parser error, or questionable benchmark status.

## Implemented repairs

### 1. Trust containment

All floating-point-to-BV reduction (`Fpa2Bv`) trust steps are emitted with
`certified: false`. Local satisfiability replay is not an independent proof that
the whole SMT-LIB FP reduction is faithful; certification stays disabled until
a complete reduction checker covers quotient semantics, core equality,
congruence, arrays, quantifiers, rounding modes, and underspecified operations.

Primary files:

- `crates/axeyum-smtlib/src/parse.rs`
- `crates/axeyum-solver/tests/fpa2bv_trust_step.rs`

### 2. Single-NaN Float quotient

SMT-LIB has one NaN value per floating-point format, although IEEE interchange
formats contain many sign/payload encodings. Float values are now canonicalized
to one positive quiet-NaN encoding at IR evaluation, scalar/full-value storage,
symbol and application lowering, generic arrays, UF arguments/results, and
finite quantifier enumeration. Core equality and congruence therefore see the
theory value rather than distinguishable raw payloads.

Primary files:

- `crates/axeyum-ir/src/value.rs`
- `crates/axeyum-ir/src/eval.rs`
- `crates/axeyum-bv/src/lib.rs`

End-to-end regressions cover distinct constant NaN encodings and a QF_UFFP
predicate applied to two free NaNs.

### 3. True five-element RoundingMode sort

`RoundingMode` is now a first-class sort rather than an exposed unconstrained
BV3. Its lowering uses a three-bit carrier with unused codes 5, 6, and 7
canonicalized to the fifth value. Parser, writer, evaluator, model/value,
planning, rewriting, finite-domain, scenario, evidence, and Z3-backend matches
were updated. Quantifier cardinality is five.

Primary files:

- `crates/axeyum-ir/src/sort.rs`
- `crates/axeyum-ir/src/term.rs`
- `crates/axeyum-ir/src/arena.rs`
- `crates/axeyum-bv/src/lib.rs`
- `crates/axeyum-smtlib/src/parse.rs`
- `crates/axeyum-smtlib/src/write.rs`
- `crates/axeyum-solver/src/ufbv_finite.rs`
- `crates/axeyum-solver/src/z3_backend.rs`

The last missed pure-Rust bit-blaster admission check was found by the new
quantified end-to-end regression and has been repaired.

### 4. Directed overflow and exact-zero signs

The shared packer now chooses infinity versus maximum finite according to both
rounding mode and result sign. Exact cancellation in add and FMA uses the
rounding-mode-sensitive signed-zero rule. Focused tests cover add, multiply,
divide, and FMA overflow behavior, both signs, and the five rounding modes at
the unit level; the SMT-LIB front door has a directed-overflow matrix.

Primary file: `crates/axeyum-fp/src/lib.rs`.

### 5. Congruent underspecified operations

Underspecified does not mean occurrence-local or syntax-keyed. FP-to-BV
out-of-domain results now use internal total functions keyed by operation,
format, width, and rounding mode and applied to the semantic Float operand.
The opposite-sign-zero choices of `fp.min` and `fp.max` now use deterministic
internal semantic selectors per operation/format/orientation. Equal argument
tuples must share a choice, while SMT-LIB-permitted freedom is retained.

Primary files:

- `crates/axeyum-ir/src/arena.rs`
- `crates/axeyum-smtlib/src/parse.rs`
- `crates/axeyum-fp/src/lib.rs`

End-to-end tests cover NaN FP-to-BV congruence and syntactically different but
semantically equal opposite-zero `fp.min` calls.

### 6. Float128 and wide-value hardening

- FP-to-BV constant conversion no longer decodes Float128 through `f64`; it
  performs exact IEEE integer rounding from the original bits.
- Float128 constant remainder uses exact pure-Rust `num-bigint` dyadic
  arithmetic, including the nearest-integer/ties-to-even quotient rule.
- Non-dyadic Real-to-FP constants use the existing exact rational conversion
  path instead of a dyadic-only parser helper.
- Wide special constants are constructed with `WideUint`, checked addition,
  and the repository width cap rather than panic-prone `u128` shifts.
- Symbolic `fp.to_real` now builds an exact finite-value expression and uses a
  congruent internal Real-valued function for NaN/infinity.

Primary files:

- `crates/axeyum-fp/Cargo.toml`
- `crates/axeyum-fp/src/lib.rs`
- `crates/axeyum-smtlib/src/parse.rs`

The direct dependency is `num-bigint`, which is pure Rust and was already part
of the workspace graph. This work does not introduce GMP, MPFR, C, C++, or
`unsafe` code.

### 7. Unrelated full-feature compile repair

Full solver tests initially could not compile because the Lean expression enum
had gained `ExprNode::Proj`, while the quantifier reconstruction structural
substitution omitted that case. The repair recursively substitutes inside the
projection structure and reconstructs the same projection. It is a mechanical,
semantics-preserving exhaustiveness fix in:

- `crates/axeyum-solver/src/reconstruct/quantifier.rs`

## Validation completed at this handoff

The following focused results were observed in the audit worktree:

- `cargo test -p axeyum-fp --lib --quiet`: 60 passed.
- `cargo test -p axeyum-smtlib --test smtlib --quiet`: 206 passed.
- `cargo test -p axeyum-solver --features full --test smtlib`: 79 passed.
- `cargo test -p axeyum-solver --features full --test fpa2bv_trust_step`: 8
  passed.
- New end-to-end cases already passed individually or in the 79-test run:
  single-NaN core equality, UF NaN congruence, unspecified FP-to-BV
  congruence, opposite-zero `fp.min` congruence, directed overflow, exact
  Float128 conversion/remainder, and the five-value RoundingMode quantifier.
- The original QF_BVFP and QF_ABVFP wrong-`sat` reproducers returned `unsat`
  after the exact-cancellation repair.
- Earlier in this stream, a deterministic 600-script all-rounding-mode cvc5
  differential run recorded 267 `sat`, 333 `unsat`, and zero disagreements.
- `cargo check --workspace --all-features`: passed.
- `cargo clippy --workspace --all-targets --all-features -- -D warnings`:
  passed.
- `cargo test -p axeyum-solver --all-features --lib`: 895 passed.
- `cargo test -p axeyum-fp --test fpa2bv_faithfulness`: 11 passed.
- A workspace all-feature test run passed every suite reached before an old
  evidence integration assertion demanded certified FP-reduction evidence. The
  policy test was replaced with a fast fail-closed text-boundary check and both
  affected focused tests pass. The complete workspace command was stopped after
  the known failure because a separate array-evidence case remained CPU-bound;
  rerun it on integrated main for the final repository-wide test claim.

Do not translate these focused results into a repository-wide green claim until
the resume gates below have completed on the integrated `main` commit.

## Known open work and limits

These items are deliberately not hidden by the implemented repair:

1. Re-run the complete selected QF_FP, QF_BVFP, and QF_ABVFP full-library
   slices. The two original files are fixed, but the P0 exit gate is the whole
   affected selection at `DISAGREE = 0`.
2. Extend the existing `rustc_apfloat::ieee::Quad` add/mul/div/FMA oracle tests
   from predominantly RNE to all five rounding modes. The implementation paths
   support the modes; the wide oracle matrix is still incomplete.
3. Update `fp_differential_fuzz.rs` commentary and generation: its old
   domain-alignment note says core `=`/`distinct` are excluded because NaNs were
   raw payloads. The implementation no longer has that limitation, so add
   quotient-sensitive atoms and rerun the Z3/cvc5 differential gate.
4. Symbolic Float128 remainder is still not bit-blasted. Constant Float128
   remainder is exact; a general symbolic algorithm or an explicit,
   well-documented decline remains to be designed and measured.
5. `fp.to_real` is no longer rejected syntactically for symbolic/exceptional
   inputs, but the general Real carrier is still `i128`-bounded. Extreme finite
   Float64/Float128 exact values can therefore overflow or decline during mixed
   arithmetic/replay. This is a completeness boundary, not permission to round.
6. Wide floating-point special constants parse without shift panics, but FP
   arithmetic/classification above the current 128-bit `FloatFormat` boundary
   remains unsupported. Keep the distinction between safe parsing and general
   wide-FP solving explicit.
7. Add an ADR that records the quotient-domain representation, five-value
   RoundingMode carrier, and congruent internal-function policy before further
   public FP surface is added. Reconcile it with ADR-0026's raw-bit identity
   wording and update the foundational dependency DAG/research-question entry.
8. Internal helper functions are namespace-disjoint inside `TermArena`; audit
   writer/model naming if internal functions ever become serialized as public
   declarations.

## Arbitrary-precision direction

The audit does not justify building an Axeyum clone of GMP or MPFR. The needed
primitive is exact integer/rational arithmetic plus an explicit binary-FP
decode/round/pack layer. `num-bigint` and `num-rational` already provide the
pure-Rust integer/rational substrate, and `WideUint` serves fixed-width circuit
construction. The Float128 remainder repair demonstrates that this composition
works without native dependencies.

The likely next architectural step is a small reusable exact-binary-FP module
over `BigInt`/`BigUint`, shared by constant conversion, remainder, `to_real`,
and oracle helpers. Do not start a general MPFR-compatible transcendental
library unless a later measured fragment requires correctly rounded
transcendentals and no suitable pure-Rust component meets the trust/dependency
constraints. If the global Real value carrier is widened from `i128`, make that
a separate ADR and migration; do not smuggle a representation change through
FP cleanup.

## Ownership and dirty-tree boundaries

At the handoff point, the audit worktree also contained unrelated concurrent
artifacts. Do not include, delete, format, reset, or stash these as part of the
FP commit:

- `bench-results/frontier/*.json`
- `corpus/glaurung-qfbv/`
- `docs/reviews/multiagent-20260717/`

The existing `main` worktree is
`/nas4/data/workspace-infosec/claude-axeyum-cas-work`. During wrap-up it had
active CAS edits (`crates/axeyum-cas/src/lib.rs` and
`crates/axeyum-cas/examples/probe_gaps.rs`). Never reset or overwrite that
worktree. Integrate the FP commits only when those tracked edits are committed
or otherwise owned by their agent, and re-read `main` immediately before the
integration operation.

## Exact resume sequence

Run from `/home/mjbommar/projects/personal/axeyum` unless a step explicitly
names the main worktree.

1. Confirm branch and ownership before touching files:

   ```sh
   git branch --show-current
   git status --short
   git worktree list --porcelain
   ```

2. Re-run the focused semantic front door:

   ```sh
   cargo test -p axeyum-solver --features full --test smtlib
   cargo test -p axeyum-solver --features full --test fpa2bv_trust_step
   cargo test -p axeyum-fp --lib
   cargo test -p axeyum-smtlib --test smtlib
   ```

3. Run formatting only against owned files first. A workspace-wide
   `cargo fmt --all --check` currently also reports formatting drift in
   concurrent CAS work, so do not mass-format unrelated files.

4. Run the FP differential and oracle gates:

   ```sh
   cargo test -p axeyum-solver --features z3 --test fp_differential_fuzz
   cargo test -p axeyum-fp --lib
   ```

5. Complete the all-mode Float128 oracle expansion and quotient-sensitive fuzz
   update described above, then repeat step 4.

6. Run repository gates in increasing scope:

   ```sh
   cargo check --workspace --all-features
   cargo clippy --workspace --all-targets --all-features -- -D warnings
   cargo test --workspace --all-features
   RUSTDOCFLAGS="-D warnings" cargo doc --workspace --all-features --no-deps
   just foundational-resources
   ./scripts/check-links.sh
   just check
   ```

7. Re-run both preserved reproducers, then the complete affected full-library
   selections. Record command, solver revisions, timeouts, counts, and raw logs
   under a dated `bench-results/` directory. Only restore the broad soundness
   statement when all three affected selections have `DISAGREE = 0`.

8. Commit only the FP-owned paths plus this handoff, P2.8 documentation, and
   the small projection exhaustiveness repair. Re-check the active main
   worktree, integrate without switching this shared worktree, run the full
   gates on the resulting main commit, and verify local `main`, `origin/main`,
   and the remote head agree before reporting completion.

## Success criteria for closing this stream

This handoff can be marked complete when all of the following are true:

- every `Fpa2Bv` trust step remains uncertified or has a genuinely complete
  independent checker;
- Float and RoundingMode quotient/domain tests pass across core equality, UF,
  arrays, quantifiers, model projection, and writer round trips;
- directed overflow and exact-zero behavior agree with independent oracles in
  all five modes, including Float128;
- underspecified operations are congruent for semantically equal inputs;
- Float128 conversions/remainder never narrow through `f64`;
- wide special constants fail gracefully rather than panic;
- full QF_FP/QF_BVFP/QF_ABVFP selected slices have zero disagreements;
- the foundational decision is recorded in an ADR;
- `just check` and the full workspace feature matrix pass on integrated main;
- the integrated main commit is pushed and local/tracking/remote heads match.

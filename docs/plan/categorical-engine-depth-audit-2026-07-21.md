# Z3-class categorical-engine depth audit — 2026-07-21

Status: **source- and test-backed roadmap correction; no broad parity claim**

The live roadmap described interpolation, CHC/Horn, and synthesis/abduction as
new or categorically absent. That classification is stale. All three areas have
working direct Rust surfaces, although only abduction—not general SyGuS—is
implemented in the synthesis group. The honest gap is now production depth,
textual compatibility, certifying coverage, and representative measurement.

This note distinguishes five states that must not be collapsed:

1. **absent** — no callable implementation;
2. **seeded** — a bounded, fail-closed implementation with focused tests;
3. **decides** — complete for a stated fragment;
4. **measured** — compared on a committed representative corpus; and
5. **production** — broad protocol/API compatibility, robustness, performance,
   diagnostics, and stable artifacts.

## Frozen audit protocol

The audit inspected the public exports, implementation boundaries, explicit
declines, SMT-LIB parser, focused tests, and committed benchmark tree. It then
ran the exact relevant test binaries sequentially under a hard 4 GiB memory cap:

```text
MEM_LIMIT_GB=4 CARGO_BUILD_JOBS=2 scripts/mem-run.sh timeout 180s \
  cargo test -p axeyum-solver --features full \
  --test horn --test abduct \
  --test interpolant --test interpolant_fuzz --test interpolant_robustness \
  --test bv_interpolant --test euf_interpolant \
  --test lia_interpolant --test lia_interpolant_cnf \
  --test lra_interpolant_cnf \
  --test uflia_interpolant --test uflra_interpolant \
  -- --test-threads=1
```

Result: **125 / 125 passed**. The interpolation group contributed 94 tests,
Horn 22, and abduction nine. Horn dominated the run at 132.77 seconds; the
remaining binaries completed in roughly 19 seconds combined after compilation.
This is focused implementation evidence, not a public-corpus performance result.

## Measured classification

| Area | Implemented boundary | Assurance boundary | Current rung | Actual parity gap |
|---|---|---|---|---|
| Craig interpolation | Public full-profile namespace for QF_BV, QF_UF, LIA, LRA, UFLIA, and UFLRA; conjunctive and selected Boolean-structured variants; certificate-bearing entry points | Every returned interpolant is verify-before-return; certified variants retain the two side obligations where supported; unsupported proof shapes decline | **decides selected direct-API fragments; focused-tested, not corpus-measured** | No SMT-LIB `get-interpolant`; incomplete mixed-theory/proof-shape coverage; no representative Z3/cvc5 corpus, PAR-2, or complete Lean/export denominator |
| CHC/Horn | Public `HornSystem`/`HornClause`/`solve_horn`; Real and Bool/BV state; stratified multi-predicate systems; compatible mutually recursive SCCs; lower-stratum nonlinear-body folding; PDR then IMC dispatch | Candidate safe models are rechecked against every original clause; unsafe outcomes carry replay-checked reachability depth; all caps and unsupported shapes return `Unknown` | **seeded, substantial direct API** | No SMT-LIB `declare-rel`/`rule`/`query`; Int, arrays, mixed state, incompatible SCC signatures, and genuine nonlinear recursion decline; no serialized `CertifiedChcSafe` bundle or representative Spacer comparison |
| Abduction | Public full-profile `abduct`; deterministic shared-vocabulary atom collection; synthesized equalities/arithmetic comparisons; one- and two-literal candidates; 4,096-candidate and synthesized-atom caps | Every returned hypothesis is rechecked for consistency, sufficiency, and shared vocabulary; budget/out-of-grammar cases return `None` | **seeded direct API** | No SMT-LIB `get-abduct`; no weakest/minimality guarantee; no user grammar, general CEGIS, larger formula language, corpus, or performance comparison |
| General SyGuS | Quantified witness synthesis and abduction reuse synthesis ideas, but there is no `synth-fun` grammar IR/front door or general function-synthesis loop | No general result surface exists, so no unverified function escapes | **absent** | Parse SyGuS-IF, model grammars, implement verify-guarded CEGIS/single-invocation paths, and measure a committed slice |

## Source findings

### Interpolation is not a missing engine

`axeyum_solver::interpolation` publicly namespaces six implemented families.
The implementation is spread across 5,044 source lines in the audited
interpolant modules, plus the propositional interpolant in `axeyum-cnf`. The 94
focused tests exercise vocabulary exclusion, satisfiable declines, randomized
soundness, mixed-sort robustness, certified obligations, and tamper rejection.

The missing boundary is visible in the parser: the repository's public-corpus
curator still excludes `get-interpolant`, and `axeyum-smtlib` has no command
handler for it. P3.8's task T3.8.5 must therefore distinguish the completed Rust
facade from the open textual surface. Calling the whole engine TODO reverses the
evidence; calling it production parity would be equally wrong.

### Horn is more than a single-predicate sketch

The 2,449-line `horn.rs` accepts multiple predicates, condenses their dependency
graph into SCCs, folds already-solved lower strata, merges sort-compatible
mutually recursive SCCs through a tagged predicate, and dispatches Real systems
to LRA PDR/IMC and Bool/BV systems to finite PDR/IMC. Its verify-before-return
gate checks a candidate interpretation against every untouched source clause.

The boundary is explicit rather than inferred: `Int`, arrays, mixed state,
incompatible SCC signatures, bodies retaining two or more recursive atoms, and
resource-cap exhaustion decline. The direct API is therefore a substantial seed,
not Spacer parity. The absence of `declare-rel`, `rule`, and `query` parsing and
of any committed CHC-vs-Spacer corpus is now more urgent than another Horn seed.

### Abduction exists; general synthesis does not

The 690-line abduction engine is publicly exported in the full profile. It can
synthesize shared equalities and arithmetic comparisons not already present in
the input, then tries bounded one- and two-literal hypotheses. Nine focused tests
cover LRA/EUF, synthesized atoms, inconsistent premises, missing vocabulary,
budget/out-of-grammar decline, and deterministic soundness fuzzing.

It does not implement the full goal written in P4.7: there is no `synth-fun`
parser, grammar datatype, general CEGIS loop, minimal/weakest abduct guarantee,
or textual `get-abduct`. “Synthesis/abduction is absent” hides working code;
“synthesis is implemented” hides the real SyGuS gap. Report them separately.

## Planning consequence

Do not allocate work to “add interpolation,” “add Horn,” or “add abduction.” The
next increments should climb the maturity ladder:

1. **Textual conformance first:** add explicit, fail-closed SMT-LIB capability
   rows and conformance fixtures for `get-interpolant`, `declare-rel`/`rule`/
   `query`, and `get-abduct`. Keep full SyGuS a separate decision.
2. **Representative corpora before more mechanisms:** freeze independent
   interpolation, CHC, and abduction slices with Z3/cvc5/Spacer comparison,
   outcome taxonomy, wall/RSS, and exact source provenance.
3. **Horn depth from residual prevalence:** measure Int, arrays, incompatible
   SCCs, and genuine nonlinear recursion before choosing which implementation
   to deepen. The existing LIA PDR engine does not imply Horn Int dispatch.
4. **Certification as its own axis:** count verify-before-return, serialized
   certificate, independent recheck, Lean reconstruction, and external-Lean
   acceptance separately. Do not label runtime reverification as a portable
   proof artifact.
5. **SyGuS only on admitted demand:** general grammar/CEGIS work is the sole
   absent engine here, but it should not outrank the measured solver/proof gaps
   without a committed consumer or corpus.

The strategic correction is narrow but important: Axeyum already has breadth of
verified seeds. Its distance from Z3 is dominated by depth, protocol surface,
measurement, and production hardening—not three unstarted categorical engines.

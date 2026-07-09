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
| [0048](adr-0048-chc-pdr-verify-guarded-invariant-discovery.md) | CHC/PDR engine — verify-guarded inductive-invariant discovery: single-predicate IC3/PDR over `TransitionSystem` (QF_BV), `Safe` admitted only when the *discovered* invariant passes the 3 implication checks, `Reachable` only when BMC-confirmed; MBP and the online LRA solver deferred (MBP = next prerequisite) | accepted |
| [0049](adr-0049-abduction-verify-guarded.md) | Abduction (`get-abduct`) as a verify-guarded generator — bounded enumeration of shared-vocabulary atoms, each candidate returned only when `check_auto` confirms consistency (`Sat`) + sufficiency (`Unsat`) + shared vocabulary; the 3rd of the three categorically-missing engines, no new trusted code | accepted |
| [0050](adr-0050-route-trace-decline-telemetry.md) | Route-trace / decline telemetry (`check_auto_explained`) as a purely-additive, verdict-invariant layer — one dispatch path with an `Option<&mut RouteTrace>` recorder that never gates a branch, `DeclineReason` reusing `UnknownKind`; guarded by a 400-query verdict-invariance differential (0 mismatches) + determinism; the observability prerequisite for the lazy-CDCL(T) dispatch push | accepted |
| [0051](adr-0051-first-class-seq-string-sort.md) | First-class `Sort::Seq(ArraySortKey)` in `axeyum-ir` (`String` = `Seq(BitVec(18))`, Unicode code points) — strings become ordinary interned terms; the bounded `(len, content)` encoder retained as the fast pre-check; the P2.7 Phase A enabling refactor, sliced A.1a–c to keep the workspace green | accepted |
| [0052](adr-0052-string-len-lia-link-and-bounded-unsat-gate.md) | The string `len`↔LIA link (P2.7 A.2) + the bounded-string `unsat` gate — `bv2nat`-linear→BV equivalence blast; parser-built unbounded length abstraction (`len(x++y)=len(x)+len(y)`, atom→`B ∧ fact` relaxation); every front-door `unsat` on a bounded-string script is confirmed bound-independent (abstraction refutes / bite detector / content-only relax) or downgraded to honest `unknown` — closes Gap 10 AND repairs the measured ADR-0029 wrong-unsat classes (`len(s)=9`, cross-width `prefixof`) | accepted |
| [0053](adr-0053-axeyum-strings-word-equation-core.md) | `axeyum-strings` crate + the P2.7 Phase-B word-equation core (CAV-2014 normal forms/arrangements) — depends only on `axeyum-ir`; bridge mode: one-shot behind `check_auto` after the bounded pre-check; `sat` only via ground-evaluator replay, word-level `unsat` declined until derivations are checkable (T-B.7); deadline honored from day one; automata substrate deferred to a Phase-C ADR | accepted |
| [0054](adr-0054-regex-symbolic-derivatives-substrate.md) | Phase-C regex via symbolic Boolean derivatives (PLDI 2021; native `R{n,m}`, LPAR 2024) — built from scratch in `axeyum-strings/src/regex/` over interval-set code-point predicates; NO external automata dependency (`regex-automata`/`aws-smt-strings`/`smt-str` are references only); `sat` replays through an independent reference matcher, regex `unsat` declines until a derivative-emptiness checker lands; the bounded byte-oriented `regex.rs` untouched. Demand: 15/35 census unknowns are regex-blocked | accepted |
| [0055](adr-0055-online-cdclt-dispatch.md) | Dispatch policy for the online CDCL(T) routes — QF_S online route default-on at the front door (ratifies the landed second-chance ordering; measured 52→58 with dual-oracle DISAGREE=0 and the 5707563b termination/expansion/polarity gate paid); **2026-07-09 update:** QF_UF criterion (2) fired, so the existing `euf-online` front-door route is now the generic replay-checked `CdclT` path, config-timeout aware, with offline EUF retained as fallback; new theories arrive online-first behind the same discipline | accepted |
| [0056](adr-0056-verified-systems-track.md) | The verified-systems trajectory (IR reflection) is a first-class track — reflect post-borrowck MIR + post-optimization LLVM IR into the typed IR and prove properties/equivalences over them; explicit boundaries (no seL4-parity claims, no ghost-code deductive language, no source-level Rust semantics) | accepted |
| [0057](adr-0057-reflect-module-boundary.md) | The IR reflectors are an `axeyum-verify::reflect` module, not a new crate (yet) — promote the per-test reflector scaffolding to a real library module (`reflect::mir`/`reflect::llvm`) with one consumer today; the crate split waits for a second proven consumer (ADR-0001 minimal-split discipline) | accepted |
| [0058](adr-0058-funded-nra-cad-nlsat-engine-arc.md) | The funded QF_NRA CAD/nlsat engine arc — **Phase B OBE (10th review): its DPLL→CAD edge (`5ede57f4`) + bignum coefficient path (#43 `4d74b288`) already landed** (~+2 rows); remaining arc = Phase C (ICP/transcendental, δ-sat⇒unknown) + D (projection/cell scaling) for the ~6 genuine-engine residue rows, per-cell certs → kernel-checked Lean `False`, pure Rust, dual-oracle DISAGREE=0. Pivot re-opened: Phase C/D DE-PRIORITIZED below strings breadth (the dominant measured gap post-arithmetic); stays proposed, NOT ratified | proposed |
| [0059](adr-0059-bv-inprocessing-vivify-default-on.md) | Enable CNF inprocessing + vivification by default, PAIRED — the built-but-off levers measured net-positive on public p4dfa (task #56: OFF→ALL-ON 4→7 @20s, 3→5 @3s, DISAGREE=0). Pairing is load-bearing (inprocessing-alone regresses at a tight budget; vivify recovers). Code flip gated on a broader QF_BV re-measure. Verdict: p4dfa is search-bound (CNF already smaller than Z3's) → the real lever is SAT-core modernization P1.3; this banks the cheap pre-pass win. Corrects the stale "Z3 113/113 ≤1s" (measured 8–9/113 @20s) | proposed |
| [0060](adr-0060-arith-online-cdclt-default-dispatch.md) | Default dispatch for arithmetic online CDCL(T). Ratifies QF_UFLIA/QF_UFLRA online-first ordering and the 16M-step no-deadline belt. **2026-07-09 update:** pure QF_LIA/QF_LRA now lead with generic `CdclT`; LIA retains a remaining-budget fallback, LRA budget/resource exhaustion is terminal while non-budget declines fall through. LRA deadlines cover construction/FM/model work, with a deterministic 1,024-atom cap. Curated 5s A/B preserves decided counts and zero disagreements/replay failures; the two QF_LRA unknown rows improve 5.250s/11.853s → 4.838s/5.031s. Combined arithmetic/BV migration remains open | accepted |
| [0061](adr-0061-string-evidence-certification-boundary.md) | Evidence certification for non-arena theories (strings/regex) lives at the **text** front door, not the arena one — the word/regex/length cores are not representable in the term IR (arena view is empty/bounded, which produced two wrong `checked=true` verdicts, #62/#63). `produce_evidence_smtlib` delegates the decision to `solve_smtlib` and wraps the sound verdict; a certified string `unsat` is a **self-contained** variant (`UnsatRegexEmptiness`) whose `check()` re-derives from the parse-tree `Membership`, ignoring `(arena, assertions)`; uncertified classes stay a correct bare `Unsat(None)`. Soundness trap: `Unsat(None).check()` is a vacuous `Ok(true)` → consumers gate crediting on `is_certified()`. Extensible pattern for #58b word-clash + future non-arena theories | accepted |
| [0063](adr-0063-word-unsat-residue-nielsen-keystone.md) | The remaining string word-level `unsat` residue reduces to the **Nielsen-arrangement** class, DEFERRED as a soundness-critical keystone (#82, needs a completeness-of-splits witness). Word-unsat is ALREADY live (refute.rs slices 1–3 clash/cycle/congruence + StringGate length projection → decides str001–str005). The two search-free sub-classes are NOT pursued: Rank #2 (ε→length bridge) is redundant (str004/005 already decide) + crate-boundary-infeasible; Rank #1 (two-ended constant clash) is sound but 0 corpus ROI (quad rows have variable ends). `arrange.rs` SearchOutcome stays Unsat-free by construction. Non-word rows (ctn-repl/open-pf/issue2958/artemis) belong to other arcs. Tasks #80/#81/#82 | accepted |
| [0062](adr-0062-bounded-string-completeness-unsat-route.md) | A bounded packed-BV string `unsat` (ADR-0029) is upgraded to a real `unsat` only when a conservative syntactic test C1∧C2∧C3 proves the query **bounded-complete** — no free `Int` (C1), every free `String` length-capped ≤ MAX_LEN (C2), every `Int` provably `< 2³¹` (C3); the analyzer declines on anything unrecognised. Run as the final escalator `apply_bounded_completeness_unsat` in `solve_smtlib`, keyed on the `"no model within the bounded integer width"` Unknown. KEY: the string-length axis is a **second** incompleteness source, so "no free Int" alone is a wrong-unsat trap (`(> (str.len s) 100)` is real-sat with no Int). Corollary #76 fix: `str.at s k` for constant `k ≥ cap` on a symbolic string routed through the Int mux (sound `unknown`) instead of a hard `""` (was an exact wrong-unsat). cvc5 whole-corpus DISAGREE=0; decides both `update-ex2` targets. Broadening has 0 measured ROI (measure-don't-seed). Tasks #74/#75/#76/#77 | accepted |
| [0064](adr-0064-integer-algebraic-identity-refutation.md) | An integer-aware, **UNSAT-only** polynomial-identity refutation (`integer_algebraic_refutation`, `nra_real_root.rs`) decides a genuinely **integer-specific** `QF_NIA` unsat class the real CAD cannot see (its relaxation is SAT — e.g. `nl-eq-infer`: `i−n=3/2` satisfies over ℝ). Collects `Int` polynomial atoms, injects integer tight-bounds (`g≥0 ∧ −g≥0 ⊢ g=0`), substitutes asserted equalities (incl. `MultiPoly::solve_for_var`, a standalone-linear isolate that yields *rational* defs like `s=(i²−i)/2`) into asserted disequalities; a `p≠0` reduced to the **zero polynomial** is `0≠0` ⇒ UNSAT. KEY soundness: **emits only Unsat, never a model** — so the rational def carries NO wrong-sat risk (this sidesteps the `a946f925`-class integer/rational trap that reverted the naive "extend `decompose_multivariate`" attempt, which was also 0-ROI since `QF_NIA` never reaches the `Sort::Real` CAD). The strict→non-strict tightening is the only ℤ-specific step, gated by `Int`-only collectors. Wired as an additive `Unknown`-fallback in `check_auto`/`_explained` (route `integer-algebraic-refutation`). Decides `nl-eq-infer`; `nia_differential_fuzz` DISAGREE=0 + 3 wrong-sat-negatives. Task #88 | accepted |
| [0065](adr-0065-finite-domain-disjunction-split.md) | A NARROW finite-domain disjunction case-split (`try_finite_domain_split`, `auto.rs`) fired only as an `Unknown`-fallback: splits only conjuncts `(or (= …) … (= …))` whose every disjunct is an EQUALITY (each is unconditional in its branch, so branch preprocessing propagates it — a region/inequality disjunct would not), bounded to ≤64 branches. `D₁∧…∧Dₘ∧rest` sat iff some choice of one equality per `Dᵢ` + `rest` is sat: all branches unsat ⇒ unsat, any branch sat ⇒ sat, else decline. Decides `rewriting-sums` (`x∈{5,7,9}`, `y∈{x+1,x+2}`, `z∈{y+5,y+10}`, `z²>10⁹` ⇒ z≤21 ⇒ unsat) which the online loop stalls on because the conditional equalities can't be globally propagated into the nonlinear atom. KEY: the earlier BROAD split (all disjunctions incl. regions) was reverted for doubling PAR-2; the equality-only + Unknown-fallback narrowing is what makes it pay without regressing (frontier_nia_unsat held). cvc5-regress QF_NIA unsat 16→17; nia+nra fuzz DISAGREE=0 (emits both sat+unsat). Task #87 | accepted |

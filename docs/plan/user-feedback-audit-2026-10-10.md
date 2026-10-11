# User feedback audit and implementation map — 2026-10-10

This is a dated research record and implementation specification. Scheduling is
owned by [PLAN.md](../../PLAN.md), generated from the
[global queue](global/20-next-actions.md). No feature below was implemented by
this audit. Proposed API and evidence changes need an ADR before implementation;
this document does not accept those decisions.

## Evidence boundary

Source inspection used HEAD `03ae4a3c9`. Six isolated Python subprocess probes
used the existing `.venv/bin/python`, `timeout_ms=1500`, and an independent
8-second process limit. All completed; these are diagnostics against an installed
extension, **not fresh-build results for HEAD**. The loaded binary was
`python/axeyum/_native.abi3.so`, SHA-256
`48669da25d56e77d319ec536b6af2c7a8d294578a73c4730db30a433f076c32b`.
Implementation lanes must rebuild against their own source commit and retain
binary identity, actual nonzero test counts, and outputs.

| Report | Source finding / diagnostic | Work |
|---|---|---|
| CAS per-step certified rewrite log | Existing certificates often witness whole results; no general step-log API found in `CasExpr` normalization or Python expression bindings. | LIB-5: [trace plan](cas-certified-trace-plan-2026-10-10.md). |
| Python SAT trace / LRAT export | Already has DIMACS, DRAT, optional LRAT, byte exports and recheck methods. A search-event stream and universal LRAT availability are different requirements. | EVD-5: route census and examples; reuse EVD-4 for RAT elaboration. |
| Boolean+LIA and Boolean UNSAT Alethe | Rust front door tries BV, ABV/EUF, LRA and LIA emitters; that does not establish arbitrary Boolean/theory composition. Two tiny diagnostic UNSAT cases returned `None`. | EVD-6: source-bound Boolean resolution and theory lemmas. |
| `(* (- 1.0) x)` proof | Tiny contradictory positive-product example solves UNSAT but diagnostic proof is `None`; cause not yet bisected. | EVD-6: normalization versus leaf-emitter regression. |
| `-1` literal | Generic atom parser accepts digit-only numerals; signed parsing in helper routes does not establish front-door support. Diagnostic raises `unknown identifier -1`. | CON-6: deliberate convenience syntax, canonical output and route consistency. |
| `abs` and `distinct` | Generic parser arms exist; diagnostic `(distinct (abs (- 1)) 1)` is UNSAT. Existing distinct coercion tests exist. | Correct any current unsupported claims; broaden semantic regression coverage. |
| Rationals beyond `i128` | Rust `Rational` already supports promoted arbitrary-precision values, including CAS constants. Python construction/getters and some CAS conversion paths remain `i128`-bounded; internal big normalization and `ZeroTest::CertifiedBig` already exist. | LIB-6: extend input/result transport and selected operations. |
| π | `enclose_constant("pi", ...)` and `StepHead::Pi` exist; `CasExpr` has no distinguished π constructor. | LIB-6: symbolic constant with existing enclosure evidence. |
| Negative powers / text parser | Python `Expr.pow` takes `u32`; expression module explicitly has no text parser. Division already exists. | LIB-6: reciprocal lowering with domain obligations; bounded parser. |
| `maximize` silently ignored | Parser stores objectives; Rust has separate boxed and lexicographic optimizer APIs, absent from Python SMT registration. Diagnostic maximize/get-value returns `x=0` for `[0,10]`. | CON-5: objective handling, budgets and optimality evidence. |
| Date API and real statute template | Seven example packs and validators exist; dates are encoded integers. Core sort enum has no Date variant; no dedicated Python rules module found. | CON-7: typed Date facade, evidence-preserving lowering and sourced pack. |

## Reproducers

Each string below was passed to `axeyum.smt.solve(q, timeout_ms=1500)`;
proof cases also used `get_proof(q, timeout_ms=1500)`.

```smt2
; negative_literal: SmtLibParseError, unknown identifier `-1`
(set-logic QF_LIA)
(declare-const x Int)
(assert (= x -1))
(check-sat)

; abs_distinct: unsat
(set-logic QF_LIA)
(assert (distinct (abs (- 1)) 1))
(check-sat)

; maximize: sat; get_value(q) returns [0], optimum should be 10
(set-logic QF_LIA)
(declare-const x Int)
(assert (and (>= x 0) (<= x 10)))
(maximize x)
(check-sat)
(get-value (x))

; boolean_unsat: unsat; get_proof returns None
(set-logic QF_UF)
(declare-const p Bool)
(assert p)
(assert (not p))
(check-sat)

; boolean_lia: unsat; get_proof returns None
(set-logic QF_LIA)
(declare-const p Bool)
(declare-const x Int)
(assert (or p (>= x 1)))
(assert (not p))
(assert (<= x 0))
(check-sat)

; negative_real_product: unsat; get_proof returns None
(set-logic QF_LRA)
(declare-const x Real)
(assert (> x 0.0))
(assert (> (* (- 1.0) x) 0.0))
(check-sat)
```

`None` is missing proof coverage, not a wrong SAT/UNSAT verdict. A satisfiable
model under an optimization objective is not an optimality certificate.

## Source anchors and corrections

- [SAT Python certificates](../../crates/axeyum-py/src/solver/proofs.rs):
  `PyUnsatProof::{lrat,lrat_bytes,recheck,recheck_lrat}`; accompanying
  [Python solver tests](../../python/tests/test_solver.py) already exercise
  absence of LRAT. [EVD-4](global/20-next-actions.md) owns remaining RAT work.
- [SMT source routes](../../crates/axeyum-solver/src/smtlib.rs):
  `solve_smtlib_get_proof`, `optimize_smtlib`,
  `optimize_smtlib_lexicographic`, `optimize_one`. Both text optimizers currently
  execute `let _ = config`; `optimize_one` calls default-config engines.
- [Integer optimizer](../../crates/axeyum-solver/src/optimize.rs):
  `MAX_DOUBLINGS` and checked-overflow exits return `Unbounded`; treat this as a
  separate correctness audit, not mathematical evidence of an unbounded ray.
- [Parser](../../crates/axeyum-smtlib/src/parse.rs): generic numeral branch is
  digit-only; `abs`, `distinct`, and objective collection are implemented.
  [Distinct regression](../../crates/axeyum-smtlib/tests/distinct_numeral_coercion.rs)
  already checks numeral coercion. Bare `-1` should be described as compatibility
  syntax: [SMT-LIB Ints](https://smt-lib.org/theories-Ints.shtml) represents
  negative values using unary subtraction.
- [CAS core](../../crates/axeyum-cas/src/lib.rs): `CasExpr`, `ZeroTest`,
  `normalize_rational_big_within`, `check_zero_test`; the carrier already supports promoted values. Audit each route for narrow
  `numerator()`/`denominator()` access, which panics on promoted values; use
  checked access or big accessors before claiming wide-input support.
- [CAS Python expression API](../../crates/axeyum-py/src/cas/expr.rs) and
  [rational conversion](../../crates/axeyum-py/src/cas/rational.rs) identify the
  public parser, exponent and input-width limits.
- [Enclosure engine](../../crates/axeyum-cas/src/enclosure.rs): π support is a
  checked enclosure route, not a general symbolic constant API.
- [Rules roadmap](../rules-as-code/ROADMAP.md),
  [schema](../../artifacts/ontology/rules-core.schema.json), and
  [proof fixtures](../../crates/axeyum-solver/tests/rules_as_code_examples.rs)
  are the reuse points for CON-7.

The user referred to `notes/80`; no matching CAS/parser feedback note was found
in tracked paths. `docs/plan/archive/80-gates.md` is a different gate record.
Do not edit a guessed historical file. This audit records the `abs`/`distinct`
correction; update the original note if its exact path becomes available.

## Execution and dependencies

CON-5 begins with fresh reproduction and explicit unsupported-objective
handling; confirmed incorrect optimization claims invoke the existing P0 rule.
EVD-5 is a small public-route inventory, not a new proof engine. EVD-6 closes
its three small regressions before broader composition. LIB-5 starts with
rational/polynomial identities and can use current bounded coefficients;
LIB-6 wider coefficients must retain equivalent trace checking. CON-6 can
proceed independently. CON-7 uses existing Bool/LIA evidence and does not wait
for full CAS breadth or general Alethe portability.

The detailed milestones are in the [CAS plan](cas-certified-trace-plan-2026-10-10.md)
and [proof/API/consumer plan](proof-api-consumer-plan-2026-10-10.md). Track IDs
and project-wide order live only in the global queue. Each implementing lane
opens its own status file and records completion in its own evidence artifact.

## Fresh implementation replay of the six diagnostics

The original findings above remain a historical installed-extension snapshot.
All six audit queries were rerun in isolated subprocesses against the sealed
fresh implementation extension, preserving assertion order and `set-logic`.
Native source is `3f2411431`, SHA-256
`99af1a4ceb22c36626b6d011dc0e6dc6cfe35b4737c15fc128a1b7b1325b09b7`;
later Rust changes relocate a helper and correct documentation. Actual output,
query hashes, saved proofs and checker outputs are retained in
`/data0/axeyum/artifacts/python/final-original-reproducers-nj938gsc/receipt.json`.
Corrected helper v2 exits zero with all six completed; v1 stopped after two
because its test assumed generic OMT would return unknown instead of the
implemented explicit unsupported-objective error. No failed v1 pass is credited.

| Audit query | Current public outcome | Evidence boundary |
|---|---|---|
| `negative_literal` | SAT, `x=-1` | Original model replay succeeds. |
| `abs_distinct` | UNSAT | Parser/verdict regression only; this probe makes no proof claim. |
| `maximize` | Generic solve/get-value explicitly reject optimization objectives | Typed `smt.optimize(..., mode="lex")` returns10 with model `x=10`, successful replay and two discharged model/strict-better certificate obligations; gold eligible for this audited slice. |
| `boolean_unsat` | UNSAT, deterministic closed Alethe without holes | In-tree checked export and external pinned, guard-patched Carcara verdict `valid`; no kernel claim. |
| `boolean_lia` | UNSAT, deterministic closed proof with `lia_generic` | In-tree integer/Boolean checking; internal-only artifact, no external or kernel credit. |
| `negative_real_product` | UNSAT, deterministic closed Alethe without holes | In-tree checked arithmetic export and external pinned, guard-patched Carcara verdict `valid`; no kernel claim. |

The external checker SHA-256 is
`32422f249b9bb18022f50b2cf15031e23ad50a0ab2c4435c5c818a5e5fa34505`;
its patch provenance and rejection controls are in the
[completion audit](user-feedback-completion-audit-2026-10-11.md). These six
results close the exact diagnostic replay population, not the final aggregate
gates or main integration.

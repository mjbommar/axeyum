# User feedback completion audit — 2026-10-11

This is an evidence audit, not a scheduling authority. The original scope is
[CAS T0–T3/X0–X2](cas-certified-trace-plan-2026-10-10.md) and
[proof/API EVD-5/A0–A3/O0–O2/R0–R1](proof-api-consumer-plan-2026-10-10.md).
[PLAN.md](../../PLAN.md) owns the queue. Completion remains unproven.

Audited checkout: `feat/nested-conditional-cas-trace-20261011`, source ancestry
through `629903932`. Main contains the research plans, not this implementation
chain. A passing ancestor test does not qualify subsequently changed source.
Earlier lane files contain historical running handles and superseded failures;
use actual terminal output before changing any item to complete.

| Requirement | Current implementation/evidence anchor | Remaining completion evidence |
|---|---|---|
| T0 rule/route inventory | [Kernel route inventory](notes/cas-trace-kernel.md), rewrite and guarded trace modules | Nested route inventory reconciled through0b829e980; final public-surface review remains. |
| T1 source-bound ordered certified steps | [Conditional trace](../../crates/axeyum-cas/src/conditional_trace.rs), six focused Rust tests pass | Private congruence guard completed:6baseline ->5pass/one intended failure, restored bytewise. Full CAS2154pass/11ignored; remaining lint/final broad gates. |
| T2 Python serialized replay without production | [Conditional Python tests](../../python/tests/test_cas_conditional_trace.py), ordinary and guarded replay suites | Fresh native34trace tests and25file consumer1166pass/1checker skip; generated stubs committed, drift/type/runtime44 pass0skip; final-source rerun of recorded narrow/wide cost examples (parent native7437a1356 measurements now recorded in lane notes). |
| T3 kernel admission and measured empty footprint | [Kernel lane](status/19-cas-trace-kernel.md), bounded ring step reconstruction | Revalidate final-source generated identity and hostile assumption/endpoint controls; keep conditional/wide declines explicit. |
| X0 wide exact rational transport/amortization | [Wide rational tests](../../python/tests/test_cas_wide_rationals.py), wide trace/guarded suites | Fresh final native regression and independent Fraction result; std/checked Rational operations remain bounded—do not claim all arithmetic routes widened. |
| X1 negative integer powers/domains | Existing signed-power implementation and zero/nonzero controls in ancestry | Final constructor/parser/serialized replay checks; preserve partial division domains and unsupported bridge declines. |
| X2 distinguished pi/enclosures/native parser | [Pi certificate tests](../../python/tests/test_cas_pi_certificate.py), [text parser tests](../../python/tests/test_cas_text_parser.py) | Final native and Rust suites, malformed/oversized input and enclosure corruption controls; constructor/parse/print agreement. |
| EVD-5 SAT export census/independent checking/source binding | Six clausal routes plus two reference fixtures; parent focused Python49/census15/existing consumers1154 pass; [miter source tests](../../crates/axeyum-solver/tests/source_bound_miter_replay.rs) | Both private source-correspondence controls complete:7baseline ->6pass/one intended failure each, original bytes independently verified. Current branch runtime/stubs pass production; final typed checks44pass0skip include configured external export checks; Py lint passes. Retain optional LRAT and guarded external checker provenance. |
| A0 fresh mandatory proof regressions | Three reported formulas and paired controls implemented in ancestry | Final-source evidence must distinguish solving, emission, local checking, external checking and kernel reconstruction. |
| A1 pure Boolean Alethe | [Boolean front-door tests](../../crates/axeyum-solver/tests/boolean_alethe_front_door.rs) | Final mandatory source-bound/no-hole proof run and altered-query/premise controls; pinned Carcara patch identity must stay explicit. |
| A2 negative real multiplication | [Negative-real tests](../../crates/axeyum-solver/tests/negative_real_alethe.rs) | Final coefficient/operand-order/nested-negation and omitted-bridge controls; external checker results. |
| A3 Boolean+LIA composition | [Boolean/LIA tests](../../crates/axeyum-solver/tests/boolean_lia_alethe.rs), internal integer-only evidence | Final supported Boolean/theory proofs and bad-cut/branch/premise controls; integer-only local artifact remains separately labelled until portable. |
| O0 objectives never silently disappear | Explicit objective intake/optimization result routes in ancestry | Final Python/session/CLI/Rust bounded maximize/minimize comparisons and unsupported-route outcomes. |
| O1 shared budgets/honest unboundedness | Intake, parsing, optimization and replay deadline repairs; quantifier polling controls | Final deterministic exhaustion/overflow checks. Resource ceilings cannot certify unboundedness; unsupported ray production must decline. |
| O2 evidence-bearing Python gold answers | Box/lex results, source-bound model and strict-better UNSAT certificates | Final feasible/optimality replay, tampered value/model/order controls and objective-mode documentation; fresh OMT tests. |
| CON-6 signed literal convenience/corrections | Signed integer compatibility parser; abs/distinct capability correction in audit | Final wide/quoted/declaration-precedence/roundtrip controls and all required parser frontdoors. Exact `notes/80` path remains unidentified; do not guess a historical file. |
| R0 typed Date and existing-pack API | [Date tests](../../python/tests/test_rules_dates.py), [pack tests](../../python/tests/test_rules_packs.py) | Final lifting/leap/invalid/boundary controls and all existing-pack reuse; Python Date facade is explicit, native Date sort is a separate decision. |
| R1 real-statute computation-of-time template | [Statute tests](../../python/tests/test_rules_statute_deadline.py), pinned official-text identity and source validator in ancestry | Current validator20 tests,7packs/4source snapshots pass; one exported certificate replays against preserved native7437a1356. Final native validation, independent bounded reference agreement and deadline/minimality checks remain. Applicability is an explicit assumption; retrieval date does not establish effective dates. |

## Shared closing gates

Run the final-source workspace library suite, full-feature solver suite, full
CAS suite, warning-denied affected-crate Clippy, generated Python stub gates and
fresh native consumer tests. Parser changes require corpus regression and the
four specified string frontdoors; arithmetic/dispatch changes require their
AGENTS.md differential/progress gates. Confirm nonzero populations. Preserve
fact-ledger/trust-registry checks, default Wasm and MSRV compatibility evidence,
regenerate plan/index documents, and check links and merge hygiene.

Before integration, reconcile this implementation chain with main's research
correction `a7df59e83`, preserve unrelated checkout files, and archive completed
lane snapshots with their evidence. Integration and final verification are still
required; an isolated local commit is not a main landing. No item in this audit
is marked complete solely because its implementation exists.

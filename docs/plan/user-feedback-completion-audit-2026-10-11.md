# User feedback completion audit — 2026-10-11

This is an evidence audit, not a scheduling authority. The original scope is
[CAS T0–T3/X0–X2](cas-certified-trace-plan-2026-10-10.md) and
[proof/API EVD-5/A0–A3/O0–O2/R0–R1](proof-api-consumer-plan-2026-10-10.md).
[PLAN.md](../../PLAN.md) owns the queue. Completion remains unproven.

Audited checkout: `feat/nested-conditional-cas-trace-20261011`, source ancestry
through `84a3e1960` (Rust cc65885a3; sealed native source3f2411431). Main contains the research plans, not this implementation
chain. A passing ancestor test does not qualify subsequently changed source.
Earlier lane files contain historical running handles and superseded failures;
use actual terminal output before changing any item to complete.

| Requirement | Current implementation/evidence anchor | Remaining completion evidence |
|---|---|---|
| T0 rule/route inventory | [Kernel route inventory](notes/cas-trace-kernel.md), rewrite and guarded trace modules | Final surface review covers Rust envelopes/entry points, Python registration/re-export and generated stubs throughcc65885a3/6c11a0008. Source/context/version/limits and producer-vs-checker/admission boundaries are explicit; shared closing gates and integration remain. |
| T1 source-bound ordered certified steps | [Conditional trace](../../crates/axeyum-cas/src/conditional_trace.rs), six focused Rust tests pass | Private congruence guard completed:6baseline ->5pass/one intended failure, restored bytewise. Full CAS2154pass/11ignored; remaining lint/final broad gates. |
| T2 Python serialized replay without production | [Conditional Python tests](../../python/tests/test_cas_conditional_trace.py), ordinary and guarded replay suites | Fresh native34trace tests and25file consumer1166pass/1checker skip; generated stubs committed, drift/type/runtime44 pass0skip; both cost examples now rerun on sealed native99af1a4c with independent exact checks, source-bound replay and deterministic export; aggregate closing gates remain. |
| T3 kernel admission and measured empty footprint | [Kernel lane](status/19-cas-trace-kernel.md), bounded ring step reconstruction | Release controls3pass/0fail/0ignore72.62s; current bridge byte-identical to tested97e700533. Final workspace11433 also passes all3 controls (generated admission/empty footprint, added-assumption rejection, unsupported translation decline); the whole gate remains running. ADR6700 accepted; integration remains. Conditional/wide reconstruction declines stay explicit. |
| X0 wide exact rational transport/amortization | [Wide rational tests](../../python/tests/test_cas_wide_rationals.py), wide trace/guarded suites | Final native wide-rational/trace/eval tests included in1166pass consumer population; amortization cost example independently checks Fraction equality on99af1a4c. Aggregate gates remain; std/checked Rational operations retain explicit bounds. |
| X1 negative integer powers/domains | Existing signed-power implementation and zero/nonzero controls in ancestry | Final constructor/parser/serialized replay checks; preserve partial division domains and unsupported bridge declines. |
| X2 distinguished pi/enclosures/native parser | [Pi certificate tests](../../python/tests/test_cas_pi_certificate.py), [text parser tests](../../python/tests/test_cas_text_parser.py) | Final native and Rust suites, malformed/oversized input and enclosure corruption controls; constructor/parse/print agreement. |
| EVD-5 SAT export census/independent checking/source binding | Six clausal routes plus two reference fixtures; parent focused Python49/census15/existing consumers1154 pass; [miter source tests](../../crates/axeyum-solver/tests/source_bound_miter_replay.rs) | Both private source-correspondence controls complete:7baseline ->6pass/one intended failure each, original bytes independently verified. Current branch runtime/stubs pass production; final typed checks44pass0skip include configured external export checks; Py lint passes. Retain optional LRAT and guarded external checker provenance. |
| A0 fresh mandatory proof regressions | Three reported formulas and paired controls implemented in ancestry | Final-source evidence must distinguish solving, emission, local checking, external checking and kernel reconstruction. |
| A1 pure Boolean Alethe | [Boolean front-door tests](../../crates/axeyum-solver/tests/boolean_alethe_front_door.rs) | Final sealed native emits all13 authoritative Boolean cases; patched pinned Carcara accepts13/13 valid/no holes. Changed-source external control rejects; altered-premise/pivot controls remain in Rust integration suites. Final workspace/aggregate gates remain; checker patch provenance explicit. |
| A2 negative real multiplication | [Negative-real tests](../../crates/axeyum-solver/tests/negative_real_alethe.rs) | Final native emits all5 authoritative negative-real cases (both operand orders, unary minus, nested negation, fractional coefficient); patched Carcara accepts5/5 valid/no holes, source-sign guard rejects. Omitted-bridge and variable-scalar controls remain in Rust integration suites; final broad gates open. |
| A3 Boolean+LIA composition | [Boolean/LIA tests](../../crates/axeyum-solver/tests/boolean_lia_alethe.rs), internal integer-only evidence | Final supported Boolean/theory proofs and bad-cut/branch/premise controls; integer-only local artifact remains separately labelled until portable. |
| O0 objectives never silently disappear | Explicit objective intake/optimization result routes in ancestry | Final Python/session/CLI/Rust bounded maximize/minimize comparisons and unsupported-route outcomes. |
| O1 shared budgets/honest unboundedness | Intake, parsing, optimization and replay deadline repairs; quantifier polling controls | Final deterministic exhaustion/overflow checks. Resource ceilings cannot certify unboundedness; unsupported ray production must decline. |
| O2 evidence-bearing Python gold answers | Box/lex results, source-bound model and strict-better UNSAT certificates | Final native OMT/certificate tests are in1166pass consumer population; shipped example now checks4models/4portable certificates (lex10/0,box10/3), goldTrue for audited slice. CLI closure and shared gates remain; unsupported integer-cut/BV proof credit stays false. |
| CON-6 signed literal convenience/corrections | Signed integer compatibility parser; abs/distinct capability correction in audit | Final wide/quoted/declaration-precedence/roundtrip controls and all required parser frontdoors. Exact `notes/80` path remains unidentified; do not guess a historical file. |
| R0 typed Date and existing-pack API | [Date tests](../../python/tests/test_rules_dates.py), [pack tests](../../python/tests/test_rules_packs.py) | Final native Date/pack/metadata controls included in1166pass population; bounded contracts accepted inADR3200/3300. Aggregate gates remain; Python Date facade is explicit, native Date sort is a separate decision. |
| R1 real-statute computation-of-time template | [Statute tests](../../python/tests/test_rules_statute_deadline.py), pinned official-text identity and source validator in ancestry | Current validator20 tests,7packs/4source snapshots pass; one exported certificate now replays on final sealed native99af1a4c. Deadline/reference/minimality controls are included in1166pass native population. Aggregate gates and integration remain. Applicability is an explicit assumption; retrieval date does not establish effective dates. |

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

## Final-native receipt update

Sealed native SHA-256 `99af1a4ceb22c36626b6d011dc0e6dc6cfe35b4737c15fc128a1b7b1325b09b7`
was reused without rebuilding for the two committed trace-cost examples and
`validate-rules-as-code.py --statute-certificates`. Both examples exit zero:
small polynomial workloads have 2/3/4 steps and 2549/3856/5597 JSON bytes;
closed-rational and 360-payment workloads retain exact independent Fraction
checks and byte replay. Timings remain host diagnostics, not performance parity.
The statute validator exits zero with 7 packs, 1 template, 4 source snapshots
and 1 replayed conditional certificate. Date/statute ADR adoption does not
remove caller-supplied applicability/calendar assumptions.

Final workspace session11433 remains live and uncredited. All-targets22417
is queued after it; complete Clippy12036 is queued after the verified all-targets
watcher3180124 and requires its recorded zero exit before launching. A temporary
cargo shim wraps the script's heavy Clippy call with cargo-serialized while
leaving read-only metadata direct; the wrapper's memory/admission limits remain.
Read-only complete-format gate88573 passes:2294 Rust files checked. None of the pending gates
is counted as a pass.

## Final-native Alethe external replay

Derived the population from the two mandatory Rust integration-test arrays:
13 Boolean bodies and 5 real products. The sealed99af1a4c native solves each
UNSAT, emits deterministic proof text with an empty final clause and no holes,
and exports exact original queries. Guard-patched Carcara checks all18 as
`valid` with zero exit status. The repository source-binding control accepts
the honest negative coefficient and rejects the changed original coefficient.
Receipt and all exported bytes are retained in
`/data0/axeyum/artifacts/proofs/final-native-alethe-419vke_m/`.
Checker base6624ea80cf1985ada473c0705869c78353e4282d; patch SHA-256
21c57d11fbe0db7c025ab58cde9613c706e07520a6e9308407fb5e09b9015166;
checker binary SHA-25632422f249b9bb18022f50b2cf15031e23ad50a0ab2c4435c5c818a5e5fa34505.
These are patched-reference results, not unmodified-Carcara or kernel claims.
Boolean+LIA `lia_generic` remains internal-only and is not included in this
external population.

Older datatype workspace87947 is terminal143 (terminated), not a pass; it
cannot qualify the final child. Current final workspace11433 and parent18900
were independently polled and remain live. No terminated job was restarted.

## Explicit CLI closing gate

Final CLI evidence is still missing: older Python SMT runs skipped the
CLI-dependent population. Watcher43772 is queued after verified-live complete
Clippy3325630 and requires its zero terminal receipt. It builds current named
`axeyum` and `smtcomp_cli` binaries, checks bounded maximize/minimize scripts
explicitly decline through the generic session CLI without printing ordinary
SAT, and runs all `test_smt.py` cases against final sealed native plus the fresh
competition CLI (including signed literals and corpus comparisons). Actual
exit/counts and binary digests remain pending; this queue entry supplies no
completion credit.

## Shipped example verification

All five selected shipped examples exit zero against final sealed99af1a4c:
`cas_amortization.py`, `cas_step_trace.py`, `smt_optimization.py`, the statute
template's `example.py`, and `sat_certificate_export.py --census` with the
pinned guarded LRAT checker configured. Artifact
`/data0/axeyum/artifacts/python/final-user-examples-351ik7ir/` retains source/native
identity, commands, outputs and exported bytes. The OMT example discharges
all counted original-model and no-better obligations for four lex/box outputs.
The CAS example checks four ordinary steps, guarded cancellation and a wide
guarded coefficient, and rejects changed context. SAT export checks two LRAT
artifacts with two external rejection controls each; its six-route census
checks every available clausal artifact externally and replays every SAT model.
Its two reference-miter cases bind original Boolean/BV queries and reject
source/miter substitution. Raw-CNF LRAT remains absent; general-theory mapping
export remains explicitly unsupported.

The statute example reports `validated` agreement, not certified UNSAT, for
its native minimality/uniqueness obligations. Its independently replayed finite
conditional certificate is separate evidence. No applicability or calendar
authenticity claim follows from this demonstration. Shared closing gates
and actual integration remain open.

## Superseded run cancellation

Parent workspace18900 was deliberately cancelled after confirming its owned
process2347214, source directory and resource scope. It exits143 and supplies
no completion credit. The current workspace11433 covers the parent libraries
and later CAS/Python additions, so removing this duplicate compilation reduces
I/O contention without removing any required final test population. The
current run and all queued final gates remain required.

## Required frontier rerun

The original frontier gate has an authoritative failure:11 passed/1 NRA timing
failure (39.4ms calibrated versus23.0ms ceiling) in the retained
`/var/tmp/axeyum-omt-gates-7pwuny00/frontier.log`. This is unresolved; library
passes do not close it. Final-source session54766 is queued after verified CLI
completion, requiring all12 source-derived tests and retaining timing frames.
It writes only to a separate absolute artifact directory. No baseline or timing
threshold was relaxed. Integration remains pending that gate as well.

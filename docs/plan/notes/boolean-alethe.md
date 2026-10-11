# Boolean and arithmetic Alethe implementation evidence

EVD-6 remains incomplete. Parent source is a7df59e83; branch
fix/boolean-alethe-20261010. Fresh diagnostic binary identity and the positive
BV control are recorded in the CAS trace branch notes at cd5287f84. This branch
has no fresh Python build yet.

The adapter preserves assertions as source-form unit assumptions and only
converts pure Boolean trees. Existing BV Tseitin/proof replay code is reused;
SAT proof search receives an absolute deadline, including the retry with
constant pins. A returned proof must pass check_alethe. Other callers keep
None deadline behavior. Conversion and emitted-command limits decline without
proof. LRAT elaboration/checking preemptibility is not yet established.

First fresh test build is runner 23970 with target
/home/mjbommar/projects/personal/axeyum/target/boolean-alethe. Three tests require
proofs for seven UNSAT examples, decline four SAT examples, and reject corrupted
resolution premises. No terminal result is recorded yet. Required implication,
ite, external checking, mutation, full gates and kernel reconstruction remain.

## Arithmetic investigation while the first build runs

`alethe_lra.rs::fold_real_mul` only admits a product if one operand satisfies
`is_constant_term`, which recognizes a RealConst leaf alone. Parsing the carried
Alethe unary `(- 1/1)` builds RealNeg(RealConst), so the checker declines the
multiplication even though it is a closed scalar. This identifies a candidate
first loss for the negative-real report; a fresh targeted route probe is still
required before declaring the cause verified. Repair must use checked closed
scalar arithmetic and preserve the original source term; arbitrary/model-based
evaluation must not classify variables or partial operations as constants.

Carcara reference exists in the main checkout at
references/carcara, commit 6624ea80cf1985ada473c0705869c78353e4282d,
binary reports 1.1.0. Its tautology.rs specifies true/false, implies and ite
clauses. These rules are listed in the in-tree rule inventory but true/false,
implies and ite are absent from check_structural_rule dispatch. Listing a rule
is not checker support. No external acceptance claim has been made.

## First terminal results and constant repair

Runner 23970 failed 3 pass/1 fail: mandatory proof generation failed on false
(the first five nonconstant UNSAT examples passed before that assertion).
Implemented premise-free singleton true and not-false checker rules matching
Carcara's contract. Added genuine constant contradictions and two forged pin
controls. Removed the unused SAT import and added test crate documentation.
Runner 97684 ended exit 0: three CNF constant tests and four solver proof tests
passed. Latest test additions (quoted symbols and zero budget) and external
export are runner 18459, still live at this record. Artifacts:
/var/tmp/axeyum-boolean-proof-external-ei6ugsj2. No external pass claim yet.

## Serialized replay and source folding repair

Run 18459 failed 5 pass/1 fail: the quoted-name proof was valid in memory but
parse_alethe could not read a quoted symbol containing spaces. Added proper
quoted-atom tokenization, including delimiters/comments within quotes and
malformed quote/backslash rejection. CNF run 90077 passed four tests; solver
run 52007 passed six tests.

External checking of those exports accepted cases 0–5 but rejected case 6:
IR folded `(not true)` to false, and the proof assumed false rather than the
original premise. The source adapter now uses the existing SMT S-expression
reader after typed validation, retains literal source forms, and declines
unimplemented macro/incremental shapes. Run 10821 passed six solver tests.
Latest addition rejects declarations of reserved true/false symbols; this
small guard postdates that test build. Focused clippy 92400 is running.

Carcara at the pinned commit accepted all seven repaired exports (`valid`,
exit 0). Changed original query and omitted resolution premises both returned
`invalid`, exit 1. Artifacts remain under
/var/tmp/axeyum-boolean-proof-external-ei6ugsj2. No allowed-rule/hole flags were
used. These results are for the narrow current connective set, not full A1.

Mutation 99670 ended exit 0 (harness): private snapshot
/data0/axeyum/scratch/snap-boolean-alethe-8c9e30c5a, baseline three pass; removing
the false-constant content guard gave two pass/one fail, exit 101. Sole failing
test: a_forged_false_pin_cannot_refute_a_true_assumption. Active tree untouched.
The snapshot predates quoted-symbol/source-adapter edits; the tested false guard
is unchanged by them. No mutation credit is assigned to unimplemented rules.

## Current final-source verification

Run 13102 ended exit 0: six solver integration tests pass after the reserved
constant declaration guard. Clippy 92400 failed identical if branches and a
single-variant wildcard; corrected the private symbol conversion condition and
made the SExpr Atom decline explicit. Retry 33080 is live. CNF library run
20771 is live (initially waiting for the same target lock). These are not green
gates yet; retain the handles and poll rather than restarting on empty output.

The source adapter currently declines scoped commands, macros and annotations;
implication/ite remain required. The goal includes all planned proof/API/CAS
features, not just this adapter. Full solver/workspace/front-door gates, fresh
Python proof API runs, kernel reconstruction and integration are still pending.

## Terminal verification of the current slice

Clippy retry 33080 failed only the two test match wildcards; made their opposite
Alethe command variants explicit. Final focused clippy ended exit 0, -D warnings.
Final source test 48780 ended exit 0: six solver integration tests passed.
CNF library run 20771 ended exit 0: 645 passed, zero failed/ignored, 64.02s.
No full solver/workspace gate, Python extension or kernel admission credit is
claimed. Current private collector also needs incremental/macro reconstruction;
checking/elaboration deadline preemption remains open. These terminal records
supersede earlier live job entries; do not restart those finished handles.

## Implication and Boolean ite extension

Implemented the three implication and four ite source-form clausification rows,
matching the pinned Carcara tautology rules. The checker validates exact gate,
arity, premise absence, operand identities and polarities; no trusted rewrite
is inserted. Typed/source adapters and shared Tseitin tail admit these heads.

Initial 10899 compilation failed on a missing new enum match arm; corrected
before the next build. Run 71823 passed six solver tests, including 13 mandatory
UNSAT examples. Two conditional-rule tests pass, covering all seven valid rows
and changed operands/polarities. Pinned Carcara accepted all 13 exports, valid
with exit 0 and no hole flags. Same artifact directory as the earlier seven
cases. Focused clippy 92608 failed a semicolon and complex tuple type; corrected
with a local row alias. Latest solver run 51076 is live, adding five SAT controls
and requiring all nine SAT models to replay. New-rule mutation and final lint
are pending; no full solver/workspace credit is claimed.

## Conditional extension terminal results

Run 51076 passed six tests, including nine replayed SAT controls and thirteen
mandatory UNSAT examples. Focused clippy 69655 passed. Mutation 2120 ended
exit 0: snapshot snap-boolean-alethe-47c9471a0, baseline two pass; removing
conditional operand/polarity comparison gave one pass/one fail, exit 101,
sole failure conditional_clausification_rejects_changed_operands.

## Negative real multiplication and explicit normalization

Baseline 20451: one pass/two failures. The actual text proof was absent, and
independently checking the direct negative-scalar la_generic step returned
StepNotEntailed. Replaced leaf-only coefficient recognition with bounded checked
closed arithmetic; closed checked quotients materialize only with nonzero
representable denominators, while others remain opaque. Canonical coefficient
rendering now also uses checked wide-carrier accessors.

First repair 22403 passed three tests; expanded run 36129 passed four, including
five negative/unary/commuted/nested/fractional cases, three replayed SAT controls,
and variable/nonlinear/zero-division coefficient rejection. External replay
accepted four cases but rejected nested negation in la_generic. Added explicit
double-negation equality, congruence and Boolean-resolution bridges, retaining
original assumptions. Run 20005 passed four tests; pinned Carcara now accepts
all five exact exports, valid/exit 0, with allow-int-real-subtyping and no holes.
Two CNF double-negation tests pass; wrong operand is rejected. Latest 18918
adds mandatory omitted-bridge rejection and focused lint; running at this record.
ADR-2700 proposed. New scalar/normalization mutations and full gates remain.

## External checker source-binding failure (P0 validation finding)

The changed-coefficient source control unexpectedly returned valid/exit 0 from
pinned Carcara 6624ea80: real-0.alethe was accepted against a SAT problem with
positive coefficient 1.0. Consequently the five positive external runs are
acceptance observations, not adequate source-binding validation. Do not credit
A2 completion from them.

Source investigation identifies Polyeq's singleton left-associative comparison
as treating unary subtraction `(- a)` like identity `a` before its signed-number
comparison. Sub is marked LeftAssoc. This makes the negative coefficient match
positive 1.0 in premise checking. A fresh isolated upstream clone is pinned at
96c00843eb157cb475796483b2ed30a51fb82852; source inspection shows the same guard.
The shared reference checkout is untouched. A separate pinned 6624 clone and
reviewable guard patch are being prepared, with the failing changed-source case
as mandatory validation. No upstream message or remote change was sent.

Local latest arithmetic run 18918 passed five tests including omitted-bridge
rejection, and focused clippy passed. Double-negation mutation 10688: baseline
2 pass; mutant 1 pass/1 fail, sole wrong-operand test. Scalar whitelist mutation
24688 is still live in the private snapshot, after restoring its own prior
CNF mutation; no mixed-mutant baseline is used.

## Guard-patched external replay and scalar mutation terminal results

New reviewable patch excludes Sub from Carcara's singleton identity shortcut;
base 6624ea80cf1985ada473c0705869c78353e4282d remains pinned. Patch SHA-256:
21c57d11fbe0db7c025ab58cde9613c706e07520a6e9308407fb5e09b9015166.
Separate clone references/carcara-source-bound-20261010 was built by runner
96043 (release, exit 0), leaving shared references/carcara untouched. New binary:
/home/mjbommar/projects/personal/axeyum/target/carcara-source-bound/release/carcara;
SHA-256 32422f249b9bb18022f50b2cf15031e23ad50a0ab2c4435c5c818a5e5fa34505.

The new discriminating script check-carcara-source-binding.py fails against
original Carcara: positive accepted, changed coefficient falsely accepted.
It passes against the guard-patched binary: positive accepted; changed-source
negative rejected specifically at original-premise binding. All thirteen Boolean
and five real exports also pass the patched checker, valid/exit 0, with no holes.
This is patched-reference evidence, never an official unmodified-Carcara claim.
Fixtures and patch/build guidance are committed alongside the script.

Scalar mutation baseline 24688 passed five tests, then the harness stopped
before modifying its source because an overly broad selector matched twice.
Corrected selector in 99594 removed only the closed-scalar default rejection;
mutant four pass/one fail, exit 101, sole failure
 a_variable_coefficient_cannot_be_treated_as_a_scalar. The earlier CNF mutation
had been restored before this baseline. Active source stayed untouched.
Double-negation mutation baseline two pass/mutant one pass/one fail is separately
recorded above. Complete solver/workspace/differential gates remain pending.

## Fresh public Python and arithmetic gates

At source 61a7c4819, the extension build exited 0. An isolated package at
`/var/tmp/axeyum-proof-python-_6iiqsj0` loaded native SHA-256
`318f4fe6ddbc193e9c4a6b6c6b7500a56dd94edb7b73641ff645dfdaab564d48`.
`python/tests/test_smt_proof_regressions.py` collected and passed five tests:
mandatory deterministic closed proof text for Boolean, implication, negative-real
and nested-negation contradictions, plus a replayed satisfiable control with no
refutation. These test the public binding; external checking is separate evidence.

The five required differential suites ran with `--features full,z3` against
61a7c4819 and passed: QF_LRA 8, simplex fallback 1, QF_UFLRA 2, difference
logic 4, QF_LIA 5 (20 total, no failures). Logs reside at
`/var/tmp/axeyum-proof-arithmetic-gates-ci2gxh9w/`. CNF library validation after
the conditional and double-negation additions is running; historical 645-test
results alone do not cover those additions. Full integration remains unverified.

## Integer composition in progress

Post-conditional/double-negation CNF library validation (handle 40558) finished:
645 passed, zero failed/ignored, 75.77 seconds.

ADR-2800 proposes a bounded source-preserving Boolean/LIA adapter. It abstracts
at most eight integer atoms, produces checked integer blocking clauses, and feeds
them to the existing propositional refutation tail as derived steps. Integer
lemmas use existing `lia_generic`; this is internal-only evidence, with portable
integer elaboration and kernel reconstruction still outstanding. Initial four
tests passed, including the reported disjunction and integer-only Boolean cases.
The subsequent quoted-name test found a serialization mismatch; repair and fresh
validation are in progress. No completion or external portability is claimed.

The quoted-name defect is repaired by canonical quoting of source symbols and
mandatory serialized replay before return. The S-expression reader canonicalizes
`|simple_name|` to `simple_name` (SMT-LIB-identical names); unsafe names such as
`|x space|` retain required quotes. The collision test compares those canonical
source assumptions and checks the closed proof. Final targeted Rust run: six
Boolean, five Boolean/LIA and five negative-real tests all pass (16 total).
The integer suite includes four required UNSAT examples, three replayed SAT
controls, corrupted integer lemmas, missing premises, zero budget and quoted
source names. Focused lint and a fresh Python build are pending. The earlier
20 differential tests and 645 CNF tests predate the new composition helper; they
do not establish its broad gates.

Final focused clippy passed after the quoted-source repair. Fresh extension build
85958 exited 0. At commit 446aae38b, isolated package
`/var/tmp/axeyum-boolean-lia-python-dtc_7ivp` loaded native SHA-256
`2ce96af247a1d9997f0326122e24227f9e59c467f3f1e6413ea6eaddfa8b4cda`.
All seven public Python regressions passed (seven collected), including Boolean
composition with an integer-only contradiction. This does not establish portable
integer proofs. Full-gate runner 84285 is live against 446aae38b; logs at
`/var/tmp/axeyum-boolean-lia-full-gates-hxdug1ce/`: five front-door suites, full
solver library, then workspace library, each with retained counts/exit status.
No terminal aggregate result yet. Existing OMT workspace runner is still live.

Full-feature gate results at pinned source 446aae38b12fc039783b21eb37ec20af118efc16:
corpus_regression 2 pass, online_string_front_door 48 pass,
word_first_fallback 13 pass, qf_slia_fixed_splice 82 pass,
stoi_len_abstraction 13 pass (158 total, zero failures). Full solver library:
2007 pass, zero failures/ignored, 2332.69 seconds. Counts verified directly from
retained logs. This includes the previously failing OMT-branch EUF timeout test;
it does not establish that the OMT branch passes. Workspace process 3297276 and
runner 3060160 remain live, observed advancing through CAS tests; no restart or
terminal workspace/aggregate result claimed. Portable integer elaboration,
source scopes/macros, proof budget propagation, kernel admission and integration
remain open after these full solver gates.

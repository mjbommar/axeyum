# Wide Real intake and datatype source export — 2026-10-11

Scope: LIB-6 X0 narrow-access panics and EVD-5 representative source exports.
Implementation is isolated; this is not an integration or whole-goal receipt.

## Confirmed evidence

- `efe4cc76f`: promoted Real constants use big numerator/denominator accessors;
  private original-source regression fails on the narrowing accessor, while
  four positive/negative numerator/denominator cases round-trip after repair.
- `69c3e0d7d`: ADR7300 exact decimal intake, 4096 digit cap, wide rational
  constant folds, explicit FP decline, and wide NRA sign comparisons.
  Six round-trip controls and two solver front-door controls pass. Earlier
  SMT/FP broad run:486 passes,0 failures/ignores. Narrow bridges are explicit;
  this does not establish general wide arithmetic decision coverage.
- Private snapshot69c3e0d7d: syntax baseline6, NRA baseline12; removing the
  decimal cap, FP representation guard, or NRA sign guard each kills exactly
  one intended control. Source restored bytewise.
- `470936b97` / `b8b237c65`: writer emits reachable datatype declarations,
  constructor/selector names, indexed testers and bare nullary constructors.
  Field dependencies close through recursive datatypes, arrays and UF sorts;
  declarations form one deterministic group. Six new reparsing controls pass.
  Post-refactor full SMT suite396 passes,0 failures/ignores. Clippy-D passes2.00s.
- Fresh native build atb8b237c65:1m15s, SHA256
  `c7f03e70144ae150b9859a9a73c644e996a27ca0038dbc82d21c602edddf7145`.
  Sealed package recorded in`/var/tmp/axeyum-datatype-writer-native-package.txt`.
  SAT/proof/OMT28 tests pass0 skips; CAS/Rules/OMT/SAT/proof1133 tests pass
  0 skips86.90s. All six public exporter fixtures reparse, check LRAT and
  replay SAT controls. Z3 independently reports UNSAT on all six exported sources.
- External checker identity matters: original DRAT-trim checker
  SHA256`13108f32c74cdd9cff6280e0763670a7c273e7ab24db242d024ed0fe90079810`
  accepted the deliberately satisfiable replacement CNF (27 passes,1 failure).
  Guarded checker SHA256
  `19863c56cd7ee5e5e69f85a6134e6de13262bb9062b08b89ae83cd5580f33daf`
  passes both rejection controls. No unmodified-upstream LRAT check is credited.
- CAS inventory gate initially rejected two unrecorded genuine Pi enclosure
  evidence functions. Source audit confirms source-bound replay and producer
  self-checking. Generated ratchet adds only those two functions and their
  two vocabulary types:153 certified,114 checker,1040 uncertified; gate passes.
  Trace logging does not raise that floor; inventory is not a kernel admission.
- WebAssembly default solver build passes32.66s with37 existing default-profile
  warnings. This is build evidence, not a full-feature solver test result.
- Generated plan/ADR/link gates pass. No broad workspace or integration pass yet.

- Private original-writer snapshot3e4d96ad0: all six datatype regressions fail
  (0 passed,6 failed,0 ignored; exit101). Final source passes all six.
- Parser front doors on finalb8b237c65 source:2+48+13+82+13=158 passes,
  0 failures/ignores across the five mandatory suites.
- MSRV1.88.0 workspace check passes1m41s; this is compilation evidence.
- Fact validation exits0; kernel footprint checks and fact populations remain
  distinct from novel-theorem production credit.

## Running / remaining

Full solver74254 on wide-decimal/NRA source69c3e0d7d completed:
2033 passed,0 failed/ignored,909.38s. It predates datatype writer and Python
source-binding commits; it is not a claim that those newer sources ran that
same full gate. Workspace87947 on datatype sourceb8b237c65 remains running. Prior parser-parent
workspace81069 and guard-parent workspace58007 are terminal143/-15, not passes.

Source-to-CNF mapping export/independent translation evidence remains absent.
These source serialization and independent verdict checks do not certify that
translation. General integer Alethe portability/kernel reconstruction, wider
conditional trace composition and final integration remain separate open work.


## Python source-bound SAT replay

Child30a4e434e (ADR8000) exposes the existing Rust
`UnsatProof::recheck_for_bool_terms` and a frozen saved-text constructor. The
constructor caps transport at8 MiB/component and16 MiB total; construction
supplies no accepted verdict. Original term roots must deterministically encode
into the exact certificate DIMACS before clausal checking. This reuses the
trusted compiler and creates no independent translation/kernel admission claim.

Fresh native build1m16s, SHA256
`10021c3dfa772267b520db5c9744fd96c602717043a5e4da3edd97eaf57b84cc`.
SAT/proof/OMT37 tests pass0 skips0.68s, including nine source-binding controls.
Two child processes restore/check text with all exporter APIs disabled.
Valid proof against substituted satisfiable terms rejects; optional LRAT,
invalid hints, missing empty clause, unsupported sorts, foreign handles, malformed
text and both byte caps have discriminating controls. Py warning-denied Clippy
passes2m13s (including build-lock wait).

Private snapshot30a4e434e guard baseline9 passes; mutation95810 still live.
Stub generator91359 passed1m40s,27 modules/661 items. Runtime drift and type
ratchets pass (1829 parameters,1744 typed,131 allowed Any,46 Any returns95.4%).
Combined proof/stub tests:34 pass,1 stubtest failure; mypy blocks checking on
three CAS annotation errors where Expr.int shadows unqualified int. No stubtest
pass credited. Generator-only metadata qualification now maps bare integer and
Optional integer annotations inside classes with an int method to builtins.int.
It does not rewrite generated text or silence mypy. Generator48361 still live.
Both live Cargo processes were observed blocked in filesystem I/O after work;
observation is not terminal and neither was restarted. Documentation adds
actual caller-supplied arena terms; the Python Script arena remains distinct.
The older independent-reference miter route does exist in Rust, but its saved
`EndToEndUnsatOutcome::recheck` checks the two text refutations without rebuilding
the subject miter. Its source-bound portable replay therefore needs an explicit
subject/miter correspondence checker before a Python wrapper can claim that
boundary closed. This is the next SAT evidence increment after this API.


Source guard95810 completed: baseline9 passes; removing exact DIMACS comparison
leaves8 passes and exactly1 intended failure
`test_source_binding_rejects_a_satisfiable_substitute`. Both runs collect9 tests;
source restored bytewise (SHA595286d9000fbda9d23c2868704e8748023911107cb6ae0a2e91094cef5260a4).

Final structured stub generation qualifies exactly5 integer annotations;
27 modules/661 items. Drift passes27 modules/1876 symbols/5 aliases/319 synthetic
dunders; type ratchet passes1829 parameters/1744 typed/131 allowed Any/46 Any
returns95.4%. Repeated proof/stub tests35 pass0 skips2.17s, including actual
mypy runtime comparison. Initial generator Clippy found assigning-clones;
changed metadata assignment to clone_into and the warning-denied rerun passes.
Current export/census exits0 with two source-bound Boolean/BV examples and six
independent Z3 UNSAT source verdicts. Current fixture/certifier scope remains
explicit in the route census; no independent translation or kernel credit.


Reference-miter source replay committed9fd9721d0; Python composite API committed
7437a1356. New core controls7 and existing miter producer fixtures9 pass with
no failures/ignores; solver Clippy-D passes37.72s. Fresh Python native build
completed4m16s, sealed package
`/data0/axeyum/artifacts/python/reference-miter-replay-rqkla299/package`, native
SHA256 `dab497034b3f4b733d3fc70c49d89ba702f14946e9b6882deeb76b6595451356`.
Focused Python end-to-end/source/SAT/proof/OMT suites collect49 and pass49 with
no skips7.03s. Two child processes disable producer APIs before restoring and
checking certificates. Incorrect source/miter substitutions reject even when
both clausal refutations independently check. Corrected private guard controls
and current full solver/older datatype workspace remain live as observed;
no completion credit yet. Generated Python stubs are being refreshed.

Reference-miter census now derives a separate public certifier population from
the registered API, alongside the six clausal exporters. Boolean/BV fixtures
restore source certificates, reject source substitution and unrelated valid
miter refutations, and export both CNF/DRAT pairs plus optional final LRAT.
Census assertions preserve absent miter LRAT and no kernel-admission claim.
Focused census/end-to-end session98367, stub generation41978, Python Clippy82361
are live; observed pytest and stub generator in kernel filesystem I/O wait.
No pass credited or duplicate jobs launched. Corrected guard script also live.

Current full-feature solver77505 terminal0:2033 pass0 failures/ignores826.10s
on source9fd9721d0, including source-bound reference-miter core changes.
Focused census/end-to-end98367 terminal0:15 pass0 skips18.64s. Updated export
CLI exits0 with six clausal/two reference fixtures; artifact
`/data0/axeyum/artifacts/python/reference-miter-census-39dd_n61/export`.
Private guard script, stub generation, PyClippy and older workspace remain
pending; current full-source workspace still required before integration.

Current-source workspace library gate started session18900 atf2df12236, log
`/var/tmp/axeyum-reference-miter-workspace.log`, serialized target
`/data0/axeyum/target/omt-ingest-deadline`. Older datatype workspace is retained
as its own older-source receipt; it cannot qualify reference-miter changes.
Stub generator41978 advanced to compiling axeyum-py; Clippy82361 waits on its
build lock. Private guard script remains live. No terminal result assumed.
Inspected guarded_trace and rewrite_trace: conditional cancellation is currently
source/context-bound at the quotient root; unconditional polynomial steps bind
full surrounding expressions and paths. Nested conditional composition remains
an explicit open item requiring a versioned public contract and checker controls.

Nested conditional composition child worktree
`/data0/axeyum/worktrees/nested-conditional-cas-trace`, base04f5337fd.
ADR8400 selects full-context guarded cancellation steps under partial rational
semantics, without claiming outer expressions total. Source/context/path
continuity and aggregate limits are explicit; polynomial witness scope remains
checked. Implement separately while parent source gates finish.

Nested Rust conditional_trace producer/replay implemented with full before/after
trees, ordered predecessor/location/context, checked guarded-v2 witnesses,
syntax/aggregate witness-work/byte bounds. Five unit controls cover two nested
steps, deterministic bytes, exact rational evaluations, surrounding subtree
corruption, source/path/order/witness/context changes, zero and resource corners.
Cargo check32748 live; no build/test result credited. Python exposure and private
surrounding-expression guard mutation remain required.

Nested Rust implementation committed1a8eab81d, verified six-file stat. Python
conditional_trace module adds one frozen structured outcome and explicit
producer/replay functions; symbolic quotient transport preserves original syntax.
Nine Python controls written, including producer-disabled child replay and
path/order/deletion/premise/context/source/zero/work/step rejection. Python
syntax passes; Rust/Python compile gates remain pending (Py42846).
Added existing workspace serde_json dependency for complete evidence transport.
No native/runtime/checker completion credit yet.

Python binding commit6c4077ab9 verified five-file stat. Source review added
early conditional fanout/context count validation before allocation or producer
work, with controls in the existing resource test. At edit time all three nested
Cargo wrappers were still in host admission sleep loops, with no cargo children;
no pre-edit compile pass is credited. Generator41978 and private miter guard
remain live on parent source; generated-stub helper90059 waits for generator.

User guide now explains nested conditional production/saved replay, the exact
external nonzero-context interpretation and partial definedness through outer
quotients. It distinguishes aggregate declared witness-work units from total
wall time or every validation operation, shared arithmetic from independent
checking, and trace validity from kernel admission. Current compile/test jobs
remain live/pending; no additional pass credited.

Private congruence guard snapshot8818 requested atd7d0a8d3e using lane-snapshot,
owner nested-conditional-congruence. Helper73515 waits for completed snapshot
then requires baseline5 pass and mutant4 pass/one exact surrounding-subtree test
failure, restores source bytewise in finally, and refuses all weaker outcomes.
Logs `/var/tmp/axeyum-nested-conditional-congruence-mutation.log` and
`/var/tmp/axeyum-nested-conditional-guard-{baseline,mutant}.log`. No result yet.
Parent Rust workers2343744/2348469 confirmed filesystem folio wait; live jobs
retained. All new nested checks remain host-admission queued, not passes.

Added sixth current-source Rust control for congruence through multiplication,
power and outer division, including an unchanged zero outer denominator: checked
local rewriting preserves partial domains and never claims a total endpoint.
Independent evaluations compare exact values or undefinedness at nonzero
assignments. New-source checks remain host-admission queued at edit time.
Private snapshotd7d0a8d3e is complete and keeps its original five-test population;
its exact-one congruence guard helper therefore still requires5->4/1.

Nested-source documentation26054 terminal0: gen-plan --check (25 lanes),
gen-adr-index --check (1035 rows; historical0166/0167 duplicates unchanged),
check-links all links okay. Current six-test source is f701e8cbf; private
five-test guard snapshot remains d7d0a8d3e. Compile32748/Python42846/private
guard73515 handles re-polled live, no results credited. Next verification
requires actual six-test execution, fresh native nine-test Python run,
warning-denied lint, generated stubs, exact-one mutation and final broad gates.

Preserved reference-miter native7437a1356 compatibility20585 terminal0:
24 existing CAS/Rules/OMT/proof/SAT files collect1154 and pass1154, zero skips,
170.80s. Population manifest
`/var/tmp/axeyum-reference-miter-existing-consumer-population.json`, results
`/var/tmp/axeyum-reference-miter-existing-consumers.log`. Native identity
`/data0/axeyum/artifacts/python/reference-miter-replay-rqkla299/identity.json`
binds7437a1356 and SHA dab497034b3f4b733d3fc70c49d89ba702f14946e9b6882deeb76b6595451356.
This qualifies existing consumer compatibility after reference-miter changes,
not new nested conditional Rust/Python code absent from that binary. Nested
compile/runtime/private mutations and parent stub/lint/full workspace remain
pending. No duplicate jobs started on observation timeout.

Nested-source CAS trust registry30467 terminal0:1310 public functions,
153 certified (floor153 all held),116 checker,1041 uncertified;136 certificate
vocabulary types. No ratchet changes or new certified-function credit for
composition logging. Raw result `/var/tmp/axeyum-nested-conditional-trust-registry.log`.
Compiler workers remain live with filesystem/block-device wait; older datatype
workspace continues advancing through kernel tests. Nested compile/runtime and
private guard outputs remain pending; a running checker is not a pass.

Investigated stalled parent builds: cargo/rustc roots2296727/2323567 were
explicitly idle I/O class under sustained disk pressure. Changed only these
owned process trees (7 processes/37 threads) to lowest best-effort I/O priority7,
verified both roots with ionice. No restarts; CPU niceness, memory caps and host
serialization retained. Forty-five-second follow-up confirms jobs still live;
no terminal result or test pass inferred from this scheduling adjustment.

Nested compile32748/test42993/Python42846 terminal101 before compilation:
Py manifest incorrectly inherited serde_json from an absent workspace entry.
No tests ran. Corrected to serde_json="1" matching existing crates; offline
Cargo metadata confirms the actual dependency. The first --no-deps metadata
run did not change Cargo.lock; lane-commit correctly refused that unchanged
path. Full offline metadata now resolves the graph and updates the lockfile.
Private congruence helper73515 terminal1 on the same baseline manifest failure,
source restored bytewise and no mutation credit. Fresh fixed-source snapshot
needs current six-test population and mutant5/one exact intended failure.

Manifest fix e0a90431b verified three-file stat; full offline metadata succeeds
and lockfile diff only adds existing serde_json to Py dependencies. New Rust
six-test29625 and Python check12773 launched against fixed source, with v2 logs.
Fresh private snapshot37464 requested ate0a90431b; v2 helper72923 requires6
baseline passes and mutant5/one exact surrounding-subtree failure, restores
bytewise. Original failed baseline and logs preserved. Lane rewritten compactly
because the pre-write3000-byte guard rejected incremental status growth.

Corrected nested Rust29625 terminal0:6 pass0 failures/ignores,2159 filtered,
0.00s actual execution; compile/test log
`/var/tmp/axeyum-nested-conditional-tests-v2.log`. Private fixed baseline6 passes;
mutant still live, no exact-one result credited. Parent miter baseline7 passes.
Parent stub generator41978 terminal0:27 modules/664 items/5 qualified integer
annotations. Fresh sealed typed package
`/data0/axeyum/artifacts/python/reference-miter-typed-ec2k4wco/package`;
runtime drift27 modules/1883 symbols/5 aliases/319 synthetic dunders passes,
type gate passes; combined runtime stub tests remain live. Python nested check
12773 still compiling, no pass yet.

Nested Py-check12773 terminal0,1m13s. Fresh native54673 builds source3f2411431
with existing CPU nice10 and best-effort I/O7; serialized memory/admission caps
remain in effect. Helper72160 waits on confirmed builder2790914, requires
completed build, seals native identity and runs new nine conditional controls
plus existing polynomial/root-guarded suites. CAS warning-denied Clippy launched.
Parent generated-stub helper90059 terminal0: runtime/type/name checks pass;
combined stub/reference-miter tests31 pass0 skips27.18s. Type gate1837 params,
1752 typed,131 allowed Any,46 Any returns95.4%; drift27/1883/5 aliases.
Parent generated proof-stub commit46874 still live at this observation.

## Continuation: full CAS verification and parent stub commit

Authoritative parent HEAD is d826846b9, the generated reference-miter proof stub commit; git show confirms exactly one file, 56 insertions. Current nested child remains clean at 5459911cc. Native Cargo2790977 and both private mutation helper processes were confirmed live; their results remain uncredited. Started full CAS library suite session6544 using serialized admission, CPU nice10 and best-effort I/O7, target nested-conditional-cas, log /var/tmp/axeyum-nested-conditional-full-cas.log. This expands verification beyond the six conditional tests; no broad pass assumed.

## Wide nested Python transport regression

Added a tenth conditional Python control: a surrounding rational with 201-bit numerator and 182-bit denominator must survive cancellation, typed endpoint reconstruction and serialized source-bound replay; a changed coefficient must reject without evidence. Python syntax compilation passes. Native runtime remains pending; no pass credited. No Rust source changed while native compilation runs.

## Carry parent generated proof stubs into the active child

Copied the exact generated proof stub bytes from verified parent d826846b9 into this child. This carries the two end-to-end classes and certifier signatures already checked against the preserved parent native binary. Nested conditional CAS stubs still require regeneration against the new binary; parent checks do not qualify those absent signatures. No Rust changes.

## Small polynomial trace cost evidence

Companion executable example python/examples/cas_polynomial_trace_cost.py completed exit0 against preserved reference-miter native source7437a1356, SHA dab497034b3f4b733d3fc70c49d89ba702f14946e9b6882deeb76b6595451356. Three workloads each assert nonempty produced traces, equal ordinary/traced normal forms and source-bound serialized replay. Five trials of ten calls record separate median ordinary/trace timings and JSON byte sizes. Full machine output /var/tmp/axeyum-small-cas-trace-cost.json. This is host-sensitive narrow polynomial evidence, not new nested-route qualification or a performance parity claim.

- rational_polynomial: 2 steps, 2549 JSON bytes; median ns/call {'ordinary_ns': 12501.9, 'trace_ns': 174665.9}.
- power_expansion: 3 steps, 3856 JSON bytes; median ns/call {'ordinary_ns': 20056.6, 'trace_ns': 266479.0}.
- two_variables: 4 steps, 5597 JSON bytes; median ns/call {'ordinary_ns': 25257.5, 'trace_ns': 405342.7}.

The original cas_trace_cost.py already includes wide amortization and byte-replay measurements. Its exact previous bytes were restored after detecting replacement during commit review; the new polynomial workload is retained in a separate companion.

## Preserved wide cost experiment terminal evidence

Original cas_trace_cost.py ran exit0 against native7437a1356/SHA dab497034b3f4b733d3fc70c49d89ba702f14946e9b6882deeb76b6595451356. Seven timing samples each verify exact results, deterministic exported bytes and source-bound replay. Closed rational:2steps/1354bytes; median untraced normalization10627ns, production144612ns, replay58391ns. Independent Fraction amortization-360:6steps/34998bytes; median exact evaluation10089231ns, production837558751ns, replay358788138ns. Ordinary wide polynomial normalization is explicitly absent, not equated with exact evaluation. Machine output /var/tmp/axeyum-wide-cas-trace-cost.json. Current nested-route runtime and final broad gates remain pending. Original example bytes match its pre-replacement version exactly.

## Current rules/source validation and preserved-native certificate replay

Current child cb7338abd: unittest discover for test_validate_rules_as_code.py exits0 with20tests/0failures in0.110s. Default validator exits0:7existing packs,1statute template,4normalized source snapshots;0certificate replay is explicitly the default, not replay credit. Optional --statute-certificates exits0 against preserved7437a1356 native/SHA dab497034b3f4b733d3fc70c49d89ba702f14946e9b6882deeb76b6595451356:1conditional certificate replayed, same7packs/4snapshots validated. Logs /var/tmp/axeyum-final-feedback-{rules-validator,rules-validator-tests,statute-certificates}.log. New nested binary is still compiling; this is current Python validator/source evidence and ancestor-native certificate evidence, not current nested-native qualification.

## Conditional unsupported/partial-evidence controls

Added three Python controls requiring unsupported pi/sin surrounding expressions and a later uncancellable quotient to return unsupported with a reason, zero completed steps and no JSON/typed result. The latter exercises all-or-nothing production after an earlier honest cancellation. Syntax compilation passes; native runtime is pending. Total conditional Python population13, not10. No Rust edit while native links.

## Full CAS, private congruence and repaired Python lint terminal results

Full CAS6544 exits0:2154passed/0failed/11ignored/0filtered67.12s against frozen nested Rust source. Private helper72923 exits0:6baseline; removing surrounding-expression guard gives exactly5passed/1failed, sole contextual_replacement_rejects_changed_surrounding_subtree; bytewise restoration confirmed. Parent Python lint88148 exits0 with -Dwarnings13.37s after c1328e0ee documentation correction; not a new nested Python lint pass. Nested CAS lint59232 exits101, exactly one items_after_statements diagnostic for locations helper at conditional_trace.rs192. Relocate helper before statements after native54673 terminates; source remains frozen meanwhile. Logs retain exact populations and intended negative assertion.

## Fresh nested native, lint correction and fixed-source gates

Native54673 exits0; preserved /data0/axeyum/artifacts/python/nested-conditional-2d5ngjhf/package, SHA99af1a4ceb22c36626b6d011dc0e6dc6cfe35b4737c15fc128a1b7b1325b09b7, source3f2411431 (later pre-build-terminal commits changed docs/Python tests/stubs only). Sealed runtime72160 exits0:34collected/34passed/0skips0.32s, three trace suites including13conditional cases. Queued lint fix73152 verifies commit0b829e980 exactly2files, resumes held generator2909193 and passes CAS lint v2 -Dwarnings11.75s. Native predates helper relocation and Python comment backticks; runtime behavior unchanged but final-source full CAS and child Python lint are newly started. Stub generator9262 now runs against fixed source; not yet a generated/type gate pass.

## Expanded fresh-native population and final workspace admission

At6051bcad0 (Rust0b829e980), started consumer71291 using sealed nested native99af1a4c:25files derived from current test_cas/test_rules/test_sat glob authority plus OMT/proof suites. Manifest /var/tmp/axeyum-nested-existing-consumer-population.json retains complete paths, exact test HEAD and binary identity; log /var/tmp/axeyum-nested-existing-consumers.log. This adds nested tests to parent24file population; no terminal count/pass assumed. Final current-child workspace library suite11433 started via serialized admission, nice10/I/O7, nested-conditional-cas target, --test-threads=1; log /var/tmp/axeyum-nested-final-workspace.log. Fixed-source full CAS37290, child Py lint61730 and stubgen9262 also remain pending. An older parent workspace pass cannot qualify this new child source.

## Fresh consumer population and generated nested stubs

Consumer71291 exits0:1167collected,1166passed/1skipped65.53s. Sole skip is external LRAT checker unconfigured (test_sat_certificate_export.py skipif); do not claim zero skips. Stubgen9262 exits0:27modules/667items/5qualified integer annotations2m35s. Generated diff onlyCASstub50newlines plus three proof-doc backtick corrections. Started52388 sealed typed-package drift/type/runtime checks against preserved99af1a4c native, with pinned guarded LRAT checker configured so external export tests execute. Stub generation is not itself drift/type verification. Full CASv2/workspace/Py lint and second miter guard remain pending.

## Fixed-source full CAS and route inventory reconciliation

Full CASv2 session37290 exits0 at Rust0b829e980:2154passed/0failed/11ignored/0filtered85.25s. Original result67.12s remains earlier-source evidence. Added nested conditional composition to authoritative route inventory notes/cas-trace-kernel.md with producer, independent-from-search replay, caller-bound context, partial-domain semantics and explicit absent kernel admission. Shared arithmetic and aggregate declared witness-work limits are stated precisely. Current type/lint/workspace and second miter mutation remain pending.

## Final Python doc lint, regenerated stub and hygiene

Child Py lint61730 exits101 on one doc_markdown identifier, resource_limited. Fixed comment cc65885a3 after confirming no active native compiler. Regenerator62778 and Py lint49809 both exit0; final logs /var/tmp/axeyum-nested-conditional-{stubgen-v2,python-clippy-v2}.log. Generated CAS stub reflects the one documentation correction. Merge hygiene36970 exits0, log /var/tmp/axeyum-nested-final-merge-hygiene.log. Current CAS registry6894 and doc gates45795 exit0 (1310functions/153certified/116checker/1041uncertified; links pass). Facts60449 and isolated typed-package checker52388 are still live; no pass credited.

## Source-bound final and miter mutation controls completed

Private v2 helper2296726 is terminal. Seven baseline passes; final-source removal gives6pass/1fail solely changed_original_query_and_unrelated_final_refutation_reject; miter-source removal gives6pass/1fail solely unrelated_valid_refutation_cannot_replace_expected_miter. Both logs inspected, both private source files compared bytewise with git-show9fd9721d0 independently of the helper restoration message. Restored exact bytes. This closes both individual guard controls; original overbroad three-death experiment remains superseded, not credited. Refreshed lane to current passing/pending gates. Merge hygiene explicitly omits shape duplicate/projection population checks despite exit0. Main merge-tree preview exits0/no conflicts, tree52900d6a; queued all-target check22417 follows confirmed live final-workspace Cargo3092650 and does not infer its success.

## Final typed/native export validation terminal results

Checker52388 exits0. Sealed typed package /data0/axeyum/artifacts/python/nested-conditional-typed-pkiqdk79/package preserves99af1a4c native and generated stubs. Drift27modules/1888symbols/5aliases/319syntheticdunders; type1847params/1762typed/131allowlistedAny/46Anyreturns95.4%; runtime44collected/44passed/0skipped22.84s. Tests include actual native stub/type controls, nested13, source-bound end-to-end and certificate export with pinned guarded LRAT checker configured. The previously skipped external checker case executed here; the larger1166pass/1skip run is retained as its actual result. Kernel generated-step identity is an ordinary unignored workspace library test, so final workspace11433 must supply its current-source admission/axiom evidence rather than borrowing a narrow ancestor result.

## Current fact ledger terminal evidence

Facts60449 exits0:2971checked/0errors; DEPENDS_DERIVED kernel_facts2586/named2408/graph3092/missing_edges0. Log /var/tmp/axeyum-nested-final-facts.log. No facts or theorem counts changed by trace logging. Current workspace11433 and sequential all-target check22417 remain pending; main integration still waits for green.

## ADR contract reconciliation begins

Branch adds32ADRs, all initially proposed. ADR3100 is now superseded by6800/6900: source _cas_parser.py public parse calls Expr._parse_text; old character/builder-only parser is a private reference, not runtime fallback. Added explicit replacement/Pi links without claiming final acceptance of replacement ADRs. Remaining decision statuses require per-contract review before final integration.

## Bounded CAS trace contract adoption

Reviewed ADR2500/6400/6500/6600 plus8400 against actual source, existing private context/identity/zero/version/bit/domain controls, current2154CAS passes and fresh native replay suites. Adopted those five bounded architecture contracts. Status explicitly does not claim main integration, broad kernel coverage or universal arithmetic support; final workspace/all-target gates remain open. ADR3100 remains superseded. Other26new ADRs still need individual contract review.

## Exact expression/transport/parser contract adoption

Reviewed ADR2900/3000/6000/6100/6200/6800/6900 against current implementations and consumer controls. In particular signed powers have a seeded256case Fraction fuzz with guaranteed0^-1/0^-10/0^0/undefined-base classes; Pi guard controls are recorded in cas-pi notes and Pi-certificate lane, and native parser uses byte/final-AST caps. Adopted these seven bounded contracts; all broad/kernel/transport restrictions remain explicit. Nineteen new ADRs still require contract review; final integration gates remain open.

## OMT/source-binding/deadline contract adoption

Reviewed ADR2300/6300/6301/6302/7000/7100 against optimize ray checking, typed report/model pins, portable Farkas source binding and deadline intake/quantifier controls. Fresh-native consumer OMT suites pass; solver full2033 source includes these modules. Adopted six bounded contracts, including2300 curated Index-status so generated status is consistent. Existing historical follow-up lists now forward-reference the later composed contracts; unsupported integer-cut/BV gold remains false. Thirteen new ADRs remain for review. Final workspace/all-target integration still pending.

## Parser and proof/source-correspondence contract adoption

Reviewed ADR2400/2600/2700/2800/7300/8000/8300 against current signatures, source adapters, scalar rules, signed/wide literal policies, restored text caps, deterministic CNF/reference-miter reconstruction and terminal guard results. Adopted seven bounded contracts. Integer-only Alethe remains internal, unmodified Carcara/DRAT-trim checks receive no credit, and general theory/kernel coverage remains separate. Six new ADRs remain for review. Final workspace/all-target gates are still live/pending.

### Date / rules / statute contract adoption — 2026-10-11

Reviewed ADR3200/3300/3400/3500/7200 against current Python source, consumer
coverage and validator receipts; accepted their bounded contracts. Reran
`python3 -m unittest discover -s scripts/tests -p test_validate_rules_as_code.py -v`:20 tests passed,0 failures. Native population remains1166pass/1 unrelated
SAT checker skip, separately covered by44pass/0skip configured runtime suite.
The statute validator receipt records7packs/1template/4snapshots and1conditional
certificate replay. No effective-date or legal-applicability inference is added.
ADR6700 kernel reconstruction remains under review pending current workspace
evidence. Final workspace Cargo3092650 was independently confirmed live;
all-targets watcher remains dependent on its termination, not inferred success.

### Final-native example and statute receipts

Sealed typed package nested-conditional-typed-pkiqdk79 preserves99af1a4c native.
Both committed cost examples exit0: `/var/tmp/axeyum-nested-final-small-cas-trace-cost.json`
and `/var/tmp/axeyum-nested-final-wide-cas-trace-cost.json`, each records full
native SHA/path, deterministic checked output and independent correctness.
`/var/tmp/axeyum-nested-final-statute-certificates.log`:7packs/1template/4snapshots/
1conditional replay,exit0. This replaces parent-native-only receipts for these
closing requirements without widening their assumptions or comparison scope.
Queued aggregateClippy12036 after live watcher3180124; it requires all-targets
exit0. Its temporary PATHshim restores originalPATH before serialized heavy
Clippy, avoiding recursion and retaining per-job resource caps. Fullformat88573
runs read-only. Workspace3092650 independently confirmed live again.

Complete-format88573 exits0:2294 Rust files checked. Final native wide example
records closed-rational2steps/1354bytes and amortization6steps/34998bytes.

### Kernel reconstruction contract adoption

Recovered terminal release13258 receipt:3pass/0fail/0ignore72.62s. Independently
compared current cas_bridge_tests.rs with97e700533:exact bytes. AcceptedADR6700
bounded design; final workspace still uncredited. Generated admission and kernel
empty-footprint evidence are distinct from ordinary checked-trace production.
All32 new contracts now reviewed:31 bounded accepted,3100 superseded by native
grammar6800/6900. Architecture acceptance does not mark full feedback complete.

### Final-native external proof population

Helper7626 exits0:18 exports derived from the authoritative Rust arrays,
13Boolean+5negativeReal, each deterministic native proof, UNSAT, emptyfinalclause,
noholes; patchedCarcara exactvalid/exit0 for every case. Also reruns committed
sourcebindingchecker positive/changed-coefficient negative; both expectations
pass. Artifact `/data0/axeyum/artifacts/proofs/final-native-alethe-419vke_m/`
includes18query/proofpairs and identity-boundreceipt.json. Native99af1a4c;
checker32422f24, base6624ea80 plus recorded unary-minusguardpatch. No unmodified
checker, internalLIA portability, or kernel admission claim.
Older datatype87947 is terminal143, notpass; finalworkspace11433 andparent18900
remain live after independent polling. Finalchild replaces, not credits, oldrun.

### Explicit final CLI coverage queued

Completion review found final CLI-dependent tests still missing: earlier Python
SMT suites skipped34 comparisons. Queued43772 waits on independently live
completeClippy watcher3325630 and requires its terminal zero receipt before
building current axeyum/smtcomp_cli targets with serialized resource caps. It
then probes bounded maximize/minimize through the session binary, requiring
explicit optimization/objective decline and forbidding a bare SAT answer, and
runs the complete test_smt.py against sealed native99af1a4c with the freshly
built competition CLI configured. Build/native identities and actual pytest
counts must be collected; queued work is not a pass. Logs
`/var/tmp/axeyum-nested-final-cli-{after-clippy,build,python}.log`; final receipt
`/var/tmp/axeyum-nested-final-cli-receipt.json`. Source remains frozen.

### Shipped examples qualified on final native

Helper1369 terminal0:5 examples run against sealed99af1a4c, artifact
`/data0/axeyum/artifacts/python/final-user-examples-351ik7ir/` contains every
stdout log, exported trace/proof files and source/nativeidentity receipt.
Amortization2859/2849bits agrees with Fraction; zero-rate2500/3. CASstep example
4unconditionalsteps, context corruption rejected atstep0,3guardedsteps and
201bitwideguarded coefficients/2912bytes checked. OMTexample verifies4models
and4portablecertificates:lex10/0 andbox10/3, each goldTrue for audited slice.
Statute example computesJuly6 fromJuly3+1day, skippingJuly4/5, reportsvalidated
native agreement (feasibilitySATverified, minimality/uniquenessUNSATnothing-to-check);
no UNSATproofcredit added. Separate conditionalcertificate replay receipt holds.
SATexport example retains guardedchecker19863c56 identity:2LRATexports verify
with2rejectioncontrols each;6clausalroutes externally verify and SATmodelsreplay;
2reference-miter cases reject substitutedsource/unrelatedvalidmiter. RawCNF
LRATabsent; generaltheory source-mapping export remains explicitly absent.

### Superseded workspace resource cleanup

Parent workspace18900 remained live after2h22m. Independently verified its
Cargo2347214 cwd, arguments and exact scope `run-p2347214-i6531304.scope`;
current Cargo3092650 belongs to distinct `run-p3092650-i7266132.scope`. Source
diff9fd9721d0..HEAD touches only CAS conditional additions and Python bindings;
the final workspace covers every parent library plus these changes. With
measured host I/O pressure and duplicate compilation, deliberately stopped
only the owned older scope. Session18900 is terminal143 (cancelled), notpass.
No result is credited or retried; the retained final full workspace must
succeed. Datatype87947 was already terminal143 and remains uncredited.
Current full-run source remains frozen; queued targets/Clippy/CLI unchanged.

### User-requested old build-cache cleanup

Removed21 obsolete lane caches under main checkout target after verifying
no tracked files, active process cwd/exe/fd/mappings or CARGO_TARGET_DIR references.
Allocated space removed:231.68GiB; filesystem
free-space gain:231.68GiB. Main target now683MiB;
root filesystem379GiB available,57%used. Retained release and
carcara-source-bound; patched checker32422f24 verified unchanged. Installed
native, source, sealed runtime packages, logs, private sources and active
/data0 targets untouched. Audit:/var/tmp/axeyum-target-cleanup-audit.json.
Current workspace3092650 independently remains live after cleanup.

### Final workspace compilation completed; tests live

Workspace11433 compiled successfully in80m06s, unoptimized+debuginfo.
Per-crate terminal populations:AIG12pass,arith87pass,BV34pass,each0fail/
0ignore/0filtered. CAS starts2165 tests (includes11 normally ignored).
Whole workspace remains live/uncredited; later kernel/solver populations
have not run yet. Collect the actual final exit before giving broad credit.

### Current workspace CAS result

Final workspace session11433 completed the CAS suite:2154 passed,0 failed,11 ignored,0 filtered in462.73s. Alongside AIG12/arith87/BV34, this is2287 passing tests across four completed crates. Remaining crates are running; the whole workspace gate remains uncredited. Log:`/var/tmp/axeyum-nested-final-workspace.log`. Rust source remains frozen atcc65885a3.

### Workspace reaches kernel suite

Final workspace11433 now has3297 passing tests across ten completed crates,15 ignored and0 failures. Completed populations:AIG12,arith87,BV34,CAS2154/11ignored,CNF645,egraph39,EVM4,FP69,IR107,Lean importer146/4ignored. Kernel2658 tests are executing; remaining whole-workspace/targets/lint/CLI gates are uncredited. The aggregate log supplies actual terminal suite results; Cargo3092650 remains live.

### Final workspace kernel trace controls

Current workspace11433 reports `ok` for all three CAS bridge controls:generated_step_trace_composes_kernel_proofs_with_empty_footprint,trace_kernel_intake_rejects_added_assumptions_before_reconstruction,trace_ring_translation_declines_fractional_wide_and_domain_sensitive_input. This directly rechecks bounded admission and negative controls on the final workspace binary; it is not a whole-kernel or whole-workspace pass. Final roadmap link gate99987 exits0/all links ok. Workspace feature tree explicitly enables axeyum-solver full; receipt:`/var/tmp/axeyum-nested-workspace-solver-features.log`. Latest read-only main merge preview exits0/conflict-free, treefbb081eb3c4f05d82ef4b5c6c1e29d97f61e0e18. Asked asynchronously for the missing notes/80 path; no dependent historical correction is guessed.

### T0 final public surface review

Reviewed polynomial/guarded/nested envelopes and all nested Rust/Python producer/replay entry points, native registration, Python re-export and generated stubs. Updated route inventory and T0 audit with source/context/version/resource/outcome boundaries. No new code or evidence claims; current full workspace remains live. Missing-path read attempts were corrected using rg file discovery, not treated as absence evidence.

### Required frontier gate reopened from authoritative failure

Audited original validation obligations and retained output. `/var/tmp/axeyum-omt-gates-7pwuny00/frontier.log` is terminal failure:11pass/1fail, NRA degree40 retained but calibrated pinned time39.4ms exceeds unchanged23.0ms ceiling. No subsequent passing frontier receipt found. Queued final-source session54766 after independently confirmed live CLI watcher3404801; it requires FINAL_CLI_PASS before serialized execution. Script:`/var/tmp/axeyum-nested-final-frontier-after-cli.py`; gate log:`/var/tmp/axeyum-nested-final-progress-frontier.log`. Source authority contains12 tests, all required unfiltered. Artifact override uses `/data0/axeyum/artifacts/gates/nested-final-progress-frontier`; committed benchmark files remain untouched. No queued pass credited.

Directly inspected all five actual arithmetic differential logs at `/var/tmp/axeyum-proof-arithmetic-gates-ci2gxh9w/` and `/var/tmp/axeyum-omt-gold-required-_volk68z/`:each population8/1/2/4/5 has0 failures/ignored,20pass total. `lra.rs` is unchanged from f829f2a92. Five required parser fronts on b8b237c65 already passed158; all SMT parser/writer source files are byte-unchanged since that revision. Current final workspace includes full solver feature, but frontier has its own unresolved timing requirement and cannot inherit library-pass credit.

### Six original audit queries replayed on fresh native

Helper53719 v1 terminal1 after2 successful queries: test assumed generic OMT Unknown, actual native raises explicit AxeyumError requiring optimizer API. Corrected v2 session18525 terminal0/all6 complete, retaining assertions/set-logic. Original negative literal modelx=-1 replays; abs/distinctUNSAT; generic maximize/get-value both explicitly reject; typed optimizer returns10/modelx10/replayTrue/goldTrue and2certificate obligations discharged. All3proofqueries emit deterministic closed/no-hole text; exact Boolean and negative-real source/proof pairs externally valid with guard-patched Carcara32422f24. Exact Boolean+LIA containslia_generic and remains internally checked only. Artifact:`/data0/axeyum/artifacts/python/final-original-reproducers-nj938gsc/receipt.json`; log:`/var/tmp/axeyum-final-original-reproducers-v2.log`. Research audit now preserves old diagnostics and adds explicit fresh outcomes. No whole-gate or kernel SMT credit.

### T3 public handoff audit and P0 gate sequencing

Trace-to-kernel code exists only in private complex/cas_bridge_tests.rs; public Ring/Rat helpers are mostly crate-private, and no CAS dispatch manifest exists. Do not treat successful bounded admission controls as the public producer/discovery handoff. Added an implementation plan; source remains frozen until an isolated continuation is created.

Reordered only idle queued watchers after verifying each owned PID/command, empty child list and zero-length gate log. Stopped leaf-first3930154/3404801/3325630/3180124; sessions54766/43772/12036/22417 authoritatively terminal143, no gate attempted. Cargo3092650 remains live/untouched. New chain: frontier87172/PID88026 waits workspace; targets99970/PID92130 waits confirmed frontier success; Clippy54143/PID94141 waits target success; CLI97027/PID96536 waits Clippy success. All scripts/logs have v2 names under /var/tmp; original empty watcher logs retained. This gives the old unresolved timing regression a quiet slot before builds. Parent baseline source remains cc65885a3; future public-source additions cannot inherit whole-gate credit.


## User-requested pause and publication checkpoint — 2026-10-11

Implementation branch: `feat/nested-conditional-cas-trace-20261011`; pre-checkpoint
HEAD `d1d20daf5`, Rust baseline `cc65885a3`. Main has not been integrated.
The user requested documentation, commit and branch push, and paused further work.
Stopped only the owned workspace scope and four verified idle downstream watchers.
Workspace completed ten crates (3297 passed, zero failed, 15 ignored); the kernel
suite was interrupted, so the aggregate gate is **not passed**. Frontier, all-targets,
complete Clippy and refreshed CLI gates were cancelled before starting. The retained
frontier timing failure remains unresolved. Earlier individual receipts keep their
original source boundaries; no cancellation earns pass credit.

The public CAS producer/discovery handoff is still required and planned in
[the handoff plan](../cas-trace-public-handoff-plan-2026-10-11.md). The existing intake
is private test code and the CAS bridge manifest is absent. Resume with that work,
fresh required gates, the completion audit, then main integration. Cleanup removed
231.68 GiB of inactive main-checkout build caches; source, active caches, checker
binaries and evidence were preserved. No further cleanup is pending in this checkpoint.


### Checkpoint publication blocked by the solver gate

Commit `1670f8736` passed all L0 checks, workspace/all-target compilation,
formatting and complete Clippy (939/939 workspace targets, 27/27 crates, zero
error diagnostics). Corpus regression passed 2 tests; the external SAT referee
passed 4 tests and 524 comparisons. Publication then failed the solver unit sweep:
1712 passed, 1 failed, zero ignored, 320 reconstruction tests filtered, 602.00s.
`euf_egraph::tests::check_qf_uf_with_config_is_bounded_by_timeout` returned
`Unknown(Other: boolean skeleton undecided)` rather than `Unsat` under its
600-second generous budget (`euf_egraph.rs:4196`). This is a failed gate, not a
completed push. No gate threshold or expected verdict was changed or bypassed.

Retained evidence: `/var/tmp/axeyum-pause-checkpoint-push-final.log`, raw Clippy
`/var/tmp/axeyum-pause-push-clippy.jsonl`, and hook execution trace
`/tmp/axeyum-prepush-trace.1569135.1791737982` (contains the full test failure
omitted from the hook's human output). No remote branch was created. Resume
requires resolving/revalidating this failure and completing the normal push hook,
in addition to the already open feature and aggregate/frontier work. The user
requested a pause, so no solver performance changes were started.

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

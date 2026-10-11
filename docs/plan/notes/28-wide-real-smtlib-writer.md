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

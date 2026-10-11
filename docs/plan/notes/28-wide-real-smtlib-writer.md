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

Full solver parent74254 and workspace87947 remain uncredited until terminal
outputs are inspected. Prior parser-parent
workspace81069 and guard-parent workspace58007 are terminal143/-15, not passes.

Source-to-CNF mapping export/independent translation evidence remains absent.
These source serialization and independent verdict checks do not certify that
translation. General integer Alethe portability/kernel reconstruction, wider
conditional trace composition and final integration remain separate open work.

# Lean U2 TL0.6.4 M2.1 plan — exact header-import declarations

Status: **preregistered; no M2.1 corpus or control process is authorized until
the implementation checkpoint is tested, committed, pushed, and ref-equal**

Date: 2026-07-23

Target: Lean `v4.30.0` at
`d024af099ca4bf2c86f649261ebf59565dc8c622`.

Parents:
[M2 program](lean-u2-native-surface-classification-tl0.6.4-m2-plan-2026-07-23.md),
[accepted M2.0 result](lean-u2-native-surface-classification-tl0.6.4-m2.0-result-2026-07-23.md),
[M2.0 authority](lean-u2-native-dependency-v1.json), and
[M1 content authority](lean-u2-native-surface-content-v1.json).

## 1. Objective and boundary

M2.1 will retain the exact direct header declarations produced by the pinned
released Lean binary's `--deps-json` fast parser for every tracked U2 Lean
source, then compare those rows with the pinned full Lean header parser. It
will preserve import order, duplicates, implicit `Init`, module mode, and the
`public`, `meta`, and `all` modifiers.

This milestone may create only `declared-static` `header-import` evidence.
It does not resolve a module name to a source or `.olean`, compute transitive
imports, observe an extra module use, configure a generated wrapper, query
Lake, build or execute a test, load a plugin/library, reach FFI, send an editor
request, or establish native support. Declared module-name targets remain
`lean-module` stubs with null package/source/artifact identities and
`resolution_state = declared-only`; M2.2 must replace them with bound
source/artifact nodes before any dependency closure can be complete.

M2.1 does not bind the 111 official workflow providers. It binds one local
released-toolchain observation route to source-level header evidence while all
official variants remain `provider_state = unbound`. No case, population,
axis, gate, pair, performance, or parity credit can increase.

## 2. Frozen source semantics

The implementation is governed by these exact pinned source files:

| Source | SHA-256 | Relevant rule |
|---|---|---|
| `src/Lean/Elab/ParseImportsFast.lean` | `119ddfbd5e6b7dbe1847bfe5094c87c65e330669966b3a76de02dc12087abcb3` | `parseImports'` and `printImportsJson`; one positional result per input; errors retained in-band |
| `src/Lean/Shell.lean` | `0de8cdbadedf418ccfb051ec8cb2c7bcd3bb6fef524c16962c72e4acfbf64d54` | `--deps-json --stdin` reads newline-delimited filenames and exits after `printImportsJson` |
| `src/Lean/Setup.lean` | `452c19cab80687c56fbf90c3b9ee2627d66c40a49c15bab710d507dd4453df5a` | JSON identities for `Import` and `ModuleHeader` |

The fast parser:

- preserves direct import order and duplicates;
- emits `module`, `importAll`, `isExported`, and `isMeta` for every import;
- inserts two implicit `Init` rows, ordinary and meta, when `prelude` is absent;
- inserts no implicit `Init` row when `prelude` is explicit;
- distinguishes module mode, where imports are private unless `public`, from
  legacy non-module mode, where imports are exported;
- rejects tabs in header whitespace and invalid module-only modifiers;
- catches file/read/parse exceptions per input into the positional JSON row;
  and
- does not search for a source/`.olean`, import a module, elaborate a command,
  or execute the test.

The full-parser comparator uses pinned `Lean.Elab.parseImports` from
`src/Lean/Elab/Import.lean`. It must emit the same ordered import values and
module-mode value for every successfully parsed source, while retaining its
message log and terminal header position. A fast/full mismatch is not resolved
by choosing the more convenient parser.

## 3. Exact input denominator

Inputs are the ordered M1 `file_rows` whose `media_class` is `lean`:

| Input fact | Frozen value |
|---|---:|
| rows | 4,092 |
| mode `100644` | 4,084 |
| mode `100755` | 8 |
| total source bytes | 9,697,571 |
| maximum UTF-8 path bytes | 69 |
| newline/CR-bearing paths | 0 |
| first path | `doc/examples/Certora2022/ex1.lean` |
| last path | `tests/simpperf/simp500.lean` |

Before execution, every row must reproduce its M1 path, mode, Git blob, byte
count, and SHA-256 from the clean pinned checkout. The ordered source-list seal
must bind all of those fields, not only path names. Missing, extra, reordered,
changed, symlink-substituted, unreadable, or non-regular inputs stop before the
first process.

The fast-parser corpus is partitioned into 32 deterministic contiguous batches
of at most 128 rows: 31 batches of 128 and one batch of 124. Batch identity is
the domain-separated digest of its ordinal plus exact ordered input records.
No adaptive split or retry is permitted after a process starts.

## 4. Provider and platform identity

The planned local route is:

- released binary:
  `/tmp/axeyum-codex-lean-20260722/elan-home/toolchains/leanprover--lean4---v4.30.0/bin/lean`;
- binary bytes/identity: 9,024 bytes, mode `0755`, SHA-256
  `3e0d0d3d801675359f2d4cf9815bfdb417b20b92fdd9d48b3b14c95bbae28bbf`;
- binary-reported version/commit required at preflight: Lean `4.30.0`,
  `d024af099ca4bf2c86f649261ebf59565dc8c622`;
- clean source root:
  `/tmp/axeyum-lean430-classify.MnJt9E/lean4` at the same commit;
- platform profile: Linux `x86_64`, glibc `2.43`; the kernel release is
  diagnostic identity rather than source semantics; and
- direct toolchain libraries: `libInit_shared.so` 6,232 bytes at
  `6ce912e300ad305bb38a362404544602e2229d072b78d75b1dd71c637e453c2c`,
  `libleanshared.so` 144,109,624 bytes at
  `86c5222603b164cd1c0dee1aeea9624a1ece9ce724ee2ed36e427a4259f8834b`,
  and the 6,232-byte `_1`/`_2` split stubs at the same
  `6ce912e300ad305bb38a362404544602e2229d072b78d75b1dd71c637e453c2c`
  digest.

The implementation must rediscover and bind the executable realpath, version,
commit, ELF needed-library/runpath declarations, direct toolchain libraries,
system loader/libc identities, platform, source checkout, environment, and
resource limits before the process checkpoint. Any mismatch requires a new
preregistered attempt; this plan's counts cannot be rebound silently.

## 5. Frozen control matrix

The implementation will commit exact control bytes before execution. The
minimum ordered matrix is:

1. legacy file with no `prelude`: implicit ordinary/meta `Init` plus one
   exported import;
2. explicit `prelude`: no implicit `Init`;
3. module file with a default private import;
4. module file with `public import`;
5. module file with `meta import`;
6. module file with `import all`;
7. ordered mixed modifiers that are valid under the pinned grammar;
8. duplicate identical imports, which must remain duplicated;
9. escaped and dotted module identifiers;
10. nested/line comments around a valid header;
11. invalid module-only modifier in legacy mode;
12. tab in header whitespace;
13. unterminated block comment; and
14. nonexistent input path.

Each control freezes expected fast/full success or error, `isModule`, ordered
imports, modifiers, duplicate multiplicity, and error class. The fast parser
and full parser must agree on every admitted import row. Expected negative
controls remain negative evidence and cannot become corpus declines or support.

## 6. Process program

The implementation checkpoint must publish and test:

- `scripts/lean_u2_native_dependency_m2_1.py` — preflight, immutable evidence
  writer, offline validator, authority builder, and generated report;
- `scripts/lean_u2_header_full_parser.lean` — pinned full-parser comparator;
- `scripts/tests/test_lean_u2_native_dependency_m2_1.py` — contract, parser,
  evidence, mutation, and zero-credit tests; and
- committed exact control fixtures or an equivalently sealed control manifest.

Only after that checkpoint is pushed and local/tracking/remote refs are equal
may attempt 001 create
`docs/plan/evidence/lean-u2-native-header-m2.1-attempt-001/`.
The root must not exist at preflight and becomes append-only after creation.
Completion is written last; an absent completion means the attempt is
incomplete regardless of intermediate output.

The exact attempt process budget is 39, sequential with no retry. Four
identity/preflight observations are retained separately from the 35 parser
processes and cannot earn header-edge credit:

| Processes | Command surface | Inputs |
|---:|---|---|
| 1 | absolute `/usr/bin/git rev-parse HEAD` | pinned source checkout |
| 1 | absolute `/usr/bin/git status --porcelain=v1 --untracked-files=all` | pinned source checkout; stdout must be empty |
| 1 | absolute `/usr/bin/readelf -d` | pinned released Lean binary |
| 1 | absolute `lean --version` | no corpus input; exact version/commit control |
| 32 | absolute `lean -j1 --deps-json --stdin` | one frozen corpus batch each |
| 1 | absolute `lean -j1 --deps-json --stdin` | frozen control paths |
| 1 | absolute `lean -j1 --run /home/mjbommar/projects/personal/axeyum-lean-parity/scripts/lean_u2_header_full_parser.lean` | all 4,092 corpus paths via stdin |
| 1 | same absolute full-parser helper | frozen control paths via stdin |

The working directory is the pinned source root. The environment is an exact
allowlist with `LC_ALL=C`, `LANG=C`, and no proxy, package, or network
variables; the absolute binary and ELF runpath remove PATH/toolchain discovery
from the child. Each fast batch receives its exact newline-delimited list on
stdin. The runner records command, cwd, environment, stdin bytes/hash,
start/end state, exit/signal/timeout, stdout/stderr bytes/hash, duration,
resource use, and artifact inventory.

The implementation checkpoint binds the physical hashes of `/usr/bin/git`,
`/usr/bin/readelf`, and the absolute full-parser helper. The local lane's
HEAD/tracking/remote equality is a separate publication/authorization gate and
is not misreported as a corpus observation. No `git ls-remote` or other network
process runs inside the evidence attempt.

Per-process limits are preregistered as one thread, 4 GiB address space,
60 CPU seconds, 120 wall seconds, 16 MiB stdout, 2 MiB stderr, and 256 MiB
file-size ceiling. The two all-corpus full-parser helpers receive 300 wall
seconds and 64 MiB stdout; all other limits stay fixed. A limit change,
parallel execution, adaptive batch, retry, or extra diagnostic process requires
a new plan and attempt root.

The user must explicitly authorize the one-shot process command after the
implementation commit. Running unit tests, rendering commands, validating
fixtures, or checking a missing evidence root is not execution authorization.

## 7. Evidence normalization

For each corpus source, the authority retains:

- M1 file record identity and ordered corpus/batch location;
- fast raw batch/output indexes and exact raw-record digest;
- full-parser raw output index, terminal header position, messages, and digest;
- `isModule`, implicit-prelude state, ordered imports, duplicate occurrences,
  all three modifiers, and occurrence index;
- source-header/M1 import-token references where present;
- fast/full comparison state;
- exact parse/read error rows without laundering them into an empty header;
- declared source-node and declared-only module-stub identities;
- `header-import` edge rows in `declared-static` state only;
- case/support ownership projections without promoting shared support to every
  case; and
- zero native outcome, execution, pair, performance, population, axis, gate,
  and parity fields.

Implicit `Init` rows are tagged `implicit-default-prelude` and have no invented
source span. Explicit rows reference the corresponding active M1
`lean.import-command` occurrence and raw parser record. Count disagreement,
ambiguous occurrence mapping, or an import emitted without an exact origin
remains `unresolved` and blocks M2.1 completion.

The planned committed authority family is:

- `docs/plan/lean-u2-native-header-dependency-m2.1-v1.json`;
- `docs/plan/generated/lean-u2-native-header-dependency-m2.1.json` and `.md`;
- the immutable attempt-001 evidence root; and
- a bounded M2.1 result document with exact physical/logical seals.

M2.0 remains an immutable parent. M2.1 does not rewrite its accepted empty
authority or claim that declared-only stubs satisfy M2.2-M2.7.

## 8. Fail-closed tests

Focused tests must reject at least:

- drift in M1, M2.0, the M2/M2.1 plans, validators, pinned parser sources,
  executable/toolchain libraries, target, platform, checkout, or environment;
- a missing, extra, reordered, duplicated, changed, newline-bearing, symlinked,
  unreadable, or non-regular corpus input;
- batch-boundary, input-order, command, cwd, stdin, limit, process-count,
  retry, completion-order, or evidence-inventory drift;
- missing/extra/reordered JSON result rows, malformed JSON, stdout/stderr
  truncation, nonzero exit, signal, timeout, or absent completion;
- dropped/reordered/merged imports or duplicates;
- implicit `Init`, `prelude`, module mode, public/private, meta, or all drift;
- a fast/full parser disagreement or error row rewritten as an empty success;
- a header declaration promoted to resolved source/`.olean`, transitive,
  configured, runtime-observed, support, or native evidence;
- a declared module stub with invented package/source/artifact identity;
- shared-support or control-fixture imports promoted to case reachability;
- an unbound official variant presented as a bound provider;
- any unauthorized process, network edge, source-tree mutation, mutable result,
  post-completion append, or missing raw evidence pointer; and
- any native outcome, pair, performance, complete population/axis/gate, or
  parity credit.

Mutations reseal their row, containing list, evidence projection, aggregate,
and top-level record so semantic invariants—not only stale digests—have teeth.

## 9. Acceptance and stop conditions

M2.1 is accepted only if:

1. plan, implementation, and authority/result checkpoints are separately
   committed and pushed in source-first order;
2. all 4,092 exact inputs have one retained fast and one retained full-parser
   row, or an exact paired error classification, with no missing evidence;
3. every emitted import preserves order, multiplicity, module mode, implicit
   origin, and modifiers and has an exact raw record pointer;
4. every M2.1 edge remains `declared-static`, every module target remains
   declared-only, and all source/artifact/transitive/native fields remain
   incomplete or zero;
5. all focused, aggregate, complete-parity, parity-doc, link, Python/Lean,
   shell, whitespace, and relevant CI gates pass, with unrelated failures
   named exactly; and
6. local HEAD, tracking ref, and remote head are equal after publication.

Stop before the first process if refs differ, the lane or pinned source tree is
dirty, the evidence root exists, any identity/input/control/limit is unclear,
or implementation tests fail. Stop the attempt without retry if any process
fails, times out, truncates, exceeds its inventory, or cannot write completion.
Stop without promotion if fast/full results disagree, a raw record cannot be
mapped exactly, or any edge would require source/artifact resolution.

## 10. Handoff

After accepted M2.1, M2.2 may use the exact ordered module-name declarations as
inputs to pinned `--deps`/`--src-deps` and a sealed search-path/module universe.
It must bind source and `.olean` identities and transitive closure separately;
M2.1's declared-only module stubs are neither resolutions nor evidence that an
artifact exists. M2.3-M2.7 and M3 remain unchanged and mandatory.

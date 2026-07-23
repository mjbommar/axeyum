# Lean U2 TL0.6.4 M2.5 plan — compiler, runtime, and FFI closure

Status: **preregistered semantics only; no M2.5 input authority, process
budget, evidence root, compiler/interpreter/link/runtime attempt, native
outcome, pair, performance row, or parity credit exists**

Date: 2026-07-23

Target: Lean `v4.30.0` at
`d024af099ca4bf2c86f649261ebf59565dc8c622`.

Parents:
[M2 program](lean-u2-native-surface-classification-tl0.6.4-m2-plan-2026-07-23.md),
[accepted M2.0 result](lean-u2-native-surface-classification-tl0.6.4-m2.0-result-2026-07-23.md),
[M2.1 pre-execution result](lean-u2-native-dependency-tl0.6.4-m2.1-pre-execution-2026-07-23.md),
[M2.2 effective-import correction](lean-u2-native-dependency-tl0.6.4-m2.2-effective-import-r1-plan-2026-07-23.md),
[M2.3 runner plan](lean-u2-native-dependency-tl0.6.4-m2.3-runner-generated-plan-2026-07-23.md),
and [M2.4 Lake/project plan](lean-u2-native-dependency-tl0.6.4-m2.4-lake-project-plan-2026-07-23.md).

## 1. Decision boundary

M2.5 must close every compiler, interpreter, generated-code, native-toolchain,
linker, loader, runtime, and FFI edge transferred by accepted M2.3/M2.4
evidence. It cannot equate a source token, generated C path, successful
frontend, linked executable, or matching text output with that closure.

The singular rule is:

> One executable behavior belongs to one exact frontend environment, compiler
> route and options, lowered declaration/IR closure, generated artifacts,
> native toolchain and libraries, ABI/platform, initialization sequence,
> loader state, runtime configuration, arguments/effects, and terminal
> observation. Compiled and interpreted routes remain separate evidence.

M2.5 owns:

- post-elaboration compilation, LCNF/IR passes, C and LLVM emission;
- Lean's IR interpreter, `lean --run`, `#eval`/`run_cmd`, and other `evalConst`
  execution boundaries;
- `leanc`, recursive C/C++/LLVM tools, archives, objects, linkers, loaders,
  executables, plugins, and dynamic libraries;
- `@[extern]`, `@[export]`, `@[implemented_by]`, initialization, ABI, ownership,
  symbol, and foreign-source closure; and
- runtime values, allocation/reference counting, tasks/threads, IO, exceptions,
  signals, stack/resource behavior, process descendants, and filesystem effects.

M2.5 does not absorb M2.2 module/artifact resolution, M2.3 shell reachability,
M2.4 target/job selection, M2.6 request/transcript semantics, or semantic
agreement and credit. It consumes accepted transfers from those owners and
returns exact runtime/artifact/process rows to M2.7/M3.

## 2. Pinned proof surface

The later M2.5.1 authority must revalidate at least these clean-checkout bytes
and transitively enumerate the implementation files actually used by each
bound executable:

| Pinned source | SHA-256 | Boundary |
|---|---|---|
| `src/Lean/Shell.lean` | `0de8cdbadedf418ccfb051ec8cb2c7bcd3bb6fef524c16962c72e4acfbf64d54` | frontend, `--run`, C/LLVM emission |
| `src/Lean/Elab/BuiltinEvalCommand.lean` | `2f6bdac9d72d21a4354a9821b69e4cc7a0658abb7639ba56e4b3db78b8bae0d6` | `#eval`, `#eval!`, `run_cmd`, monad and output selection |
| `src/Lean/Environment.lean` | `54f6ca1b7a49a52ff2d9fadb4ef544745584961d5e091ce6dd998228dbd2b253` | `evalConst` boundary |
| `src/Lean/Compiler/Main.lean` | `bf176e320b2e5af3adc6d294b4e68802b55ed8c6431e3c15356d21f510c54202` | compiler entry |
| `src/Lean/Compiler/LCNF/Main.lean` | `f31fad3354335693e352679441325133e9f9eae9bc9113d933a1f355263fb5e7` | LCNF pipeline and on-demand compilation |
| `src/Lean/Compiler/LCNF/Passes.lean` | `85b318f7c13779693766df463bc84a3b7ae937a34f95df4db02f5858152e47aa` | pass order and `implemented_by` replacement |
| `src/Lean/Compiler/LCNF/EmitC.lean` | `1ff65e941c5b2edf2c709927288482f2379b33cc06dfc495112a983860e56f13` | C, initializer, and executable emission |
| `src/Lean/Compiler/IR/EmitLLVM.lean` | `e03ec8797d19bde650e42ea5a1e3897d219d84647097df07eb24ff7755cf046b` | LLVM emission |
| `src/Lean/Compiler/IR/CompilerM.lean` | `fa67405b0bc83900ffd0a7c88bb7934e9fcd2255761a89400a73847a85cc3235` | imported/local IR and interpreter visibility |
| `src/library/ir_interpreter.cpp` | `45ff3db98a310a530fe4d149bb084af6538deb9317c2e618de22f4c421ec87b1` | `lean --run` and evaluator interpreter |
| `src/Lean/Compiler/ExternAttr.lean` | `09f0176a96ccd67bc38af62dfbaf3c41c267a6c043c479d188f7471e9599e327` | backend-specific extern selection |
| `src/Lean/Compiler/ImplementedByAttr.lean` | `fec5d936a52cdbac96173249c9ad2028c2be3a049d380fdc0c84da5b4116640f` | unchecked runtime implementation replacement |
| `src/Lean/Compiler/ExportAttr.lean` | `3de0bbe433d5933428777c0e8be582dfd266db3feb9d5e90fa6a7ac2d004c24d` | exported symbols |
| `src/Lean/Compiler/InitAttr.lean` | `517b0fd946ed2c033c92b456ccb6d07ef48275dcf6833f876ed3ddab17c6a5b1` | regular/builtin initialization |
| `src/Leanc.lean` | `4ba1b13a9a58b9a7917ca8aeae6a4929cd292411c771e1cca989a7d8a2fbf7bc` | installed `leanc` wrapper and `LEAN_CC` override |
| `src/bin/leanc.in` | `9affefef502c7a2c90d045cabe8a72b407ee943b6f8e08abf3945e26299551fa` | bootstrap wrapper |
| `src/CMakeLists.txt` | `3d5b383901e925cdb7e22a62e94eccf71f79af42dbcff3e1d56f5dfec3aa99c9` | configured compiler/link/runtime flags |
| `src/include/lean/lean.h` | `5a25125970f4f1dcf85a4c403463b387a8ff93535cd4a3054cafdee1759017d7` | public C ABI |
| `src/runtime/object.cpp` | `e8721cdd62f585f2c52aa0201c35f3d02bfb1845b28c8a7b0f28bbfdabdcbc6a` | object representation/reference operations |
| `src/runtime/thread.cpp` | `f486a3051c5b3c8a9b569b4b76a7624e72a6a30d8589d17200194188eb2b055c` | task/thread execution and `lean_run_main` |
| `src/runtime/io.cpp` | `506fb17f6d45d05cbef4a33d9eed6228956cb5536ab787422f657a3723fed7c1` | IO runtime |
| `src/runtime/exception.cpp` | `cbb244d3b7d31ab73e75d437427cb540462552726ee01229adbe203df046ce21` | exception runtime |

Primary contextual documentation is the official
[interacting-with-Lean reference](https://lean-lang.org/doc/reference/latest/Interacting-with-Lean/),
[run-time-code reference](https://lean-lang.org/doc/reference/latest/Run-Time-Code/),
and [FFI reference](https://lean-lang.org/doc/reference/latest/Run-Time-Code/Foreign-Function-Interface/).
Those pages describe current behavior; pinned v4.30.0 source is authoritative
for this milestone.

## 3. Current read-only floor, not an execution denominator

The accepted M1 authority contains these provisional source surfaces:

| Surface | Direct cases | Closure cases |
|---|---:|---:|
| compiler/runtime | 841 | 860 |
| FFI | 24 | 24 |

The 841 compiler/runtime direct cases are 282 M0 harness-floor cases plus 559
content-observed cases. They span 12 families and 820 pile, nine inline-Lake,
and 12 directory cases. Exact content signals include 539 cases with 563
evaluation-command hits and 28 cases with one compiler-API hit each.

The 24 provisional FFI cases are 14 `elab`, four `elab_fail`, and six Lake
cases. They arise from 22 cases / 24 Lean `extern` or `implemented_by` signal
rows, three C-family files, and one TOML native-link field. The census also has
20 candidate native-link spans in 11 files. Signals are neither reachability
nor a promise that foreign code is linked or called.

Even the 60 compile-family cases are not 60 interchangeable executions. The
pinned runner's marker precedence yields 60 compiled routes but only 54
interpreter routes: `StackOverflow`, `StackOverflowTask`, `init`,
`initUnboxed`, `lazylist`, and `map_big` have `.no_interpret` markers. Each
compiled route itself contains frontend-to-C, `leanc`, and executable child
steps. Accepted M2.3/M2.4 evidence must derive the actual route denominator,
including hooks, environment, marker state, Lake jobs, failures, and dynamic
children, before M2.5.1 can freeze inputs.

## 4. Compiler and evaluator route identity

Each transferred route must distinguish:

- frontend-only elaboration from post-hoc/on-demand compilation;
- `#reduce` kernel reduction from `#eval` compiled evaluation;
- `#eval` versus `#eval!`, including sorry rejection/override, synthesized
  `MonadEval`, `ToExpr`/`Repr`/`ToString`, derived instances, isolated streams,
  and server/meta-check options;
- `lean --run`, which calls the pinned IR interpreter, from a separately built
  native executable;
- C emission, LLVM bitcode emission, object/archive/shared-library generation,
  link, load, plugin, and executable invocation; and
- local, imported meta, imported all, private, server, and `.ir` declaration
  availability inherited from M2.2.

The authority retains exact declaration roots, compiler options/pass sequence,
implemented-by substitutions, specialization/inlining/erasure/boxing/borrow/
reference-count decisions, emitted symbol and initializer maps, warnings and
errors, and all intermediate content identities. A matching final output does
not erase different compiler or runtime routes.

## 5. Native toolchain and artifact closure

For every native child retain executable and recursive dynamic identity for
`lean`, `leanc`, its selected `LEAN_CC` or configured compiler, assembler,
archiver, linker, loader, sanitizer/runtime helpers, and invoked utilities.
Bind argv order, response files, cwd, environment, sysroot, include/library
search order, target triple, CPU/features, ABI, build type, optimization/debug/
sanitizer/PIC/LTO/thread flags, static/shared choice, and resource limits.

Every C/C++/LLVM/object/archive/export-map/shared-library/executable artifact
gets logical role, producer, complete ordered inputs, path/mode/size/SHA-256,
format/target identity, and pre/post-tree relationship. Toolchain-generated
timestamps, build IDs, archive ordering, absolute paths, or random seeds are
normalized only under a registered mutation-tested rule. Executability or file
presence alone is not provenance.

`leanc --print-cflags`/`--print-ldflags` report a configured projection; they do
not prove which compiler or linker later executed. `LEAN_CC` discards internal
bundled-tool flags in the pinned wrapper and therefore creates a distinct
variant, not an alias.

## 6. FFI, ABI, symbols, and initialization

For every reachable foreign boundary retain:

- declaration, normalized Lean type, safety/relevance/borrow state, attribute
  source, backend-specific extern entry, selected foreign symbol, and any
  `implemented_by` or `csimp` relationship;
- exact Lean-to-C type lowering, boxed/unboxed representation, constructor/tag/
  scalar layout, ownership token, increment/decrement obligations, result and
  exception convention, calling convention, visibility, mangling, alignment,
  and platform width/endianness;
- foreign declaration/definition bytes, language/standard/compiler flags,
  object and library membership, export/import table, duplicate/undefined/
  weak symbol resolution, link order, loader path, and loaded image identity;
- `@[export]` symbol identity and reverse-FFI caller evidence; and
- runtime setup, `lean_setup_args`, runtime/Lean/module initializers, builtin
  flags, dependency order, idempotence/thread constraints, init effects,
  `lean_io_mark_end_initialization`, and teardown.

`@[implemented_by]` does not prove semantic equivalence: pinned Lean documents
that the replacement is compiler-only and unchecked, and can make native
decision procedures unsound. M2.5 records the replacement edge and observed
behavior; it never upgrades it to proof evidence. An extern declaration with
no reachable compiled call, or a linked symbol never loaded/called, remains a
conditional or unresolved edge rather than an FFI observation.

## 7. Runtime behavior and effects

Each run binds stdin/stdout/stderr/terminal mode, argv, cwd, environment,
locale/timezone, filesystem snapshot, clocks/randomness, network policy,
signals, stack/heap/address-space/file/process/thread limits, scheduling and
thread count, and platform/runtime-library identities. Retain descendants and
effects: files, links, permissions, processes, threads/tasks, pipes/sockets,
environment reads, dynamic loads, signals, exceptions/panics/assertions,
timeouts, OOMs, stack overflows, crashes, and cleanup.

Output comparison follows the registered case policy after raw streams and
normalization inputs are retained. Expected text, exit zero, or equal values
cannot prove absence of extra effects, leaks, races, undefined behavior, ABI
mismatch, or platform-specific failure. Instrumented sanitizer/tracer runs are
separate variants and do not replace the uninstrumented official route.

## 8. Required schema and ownership

M2.5.1 and later results must retain domain-separated rows for:

- accepted parent transfer, case/profile/provider/platform and route/step IDs;
- source/environment/compiler/IR declarations and pass events;
- native process specification, executable closure, raw streams, terminal
  state, descendant cleanup, and completion-last evidence;
- artifact producer/input/link/load graph and independent content identities;
- FFI declaration/type/ABI/symbol/ownership/initialization/call events;
- runtime values, effects, resources, normalization, and comparison inputs;
- downstream M2.6 transfers and M2.7 residual/equivalence owners; and
- zero native outcome, pair, performance, complete population/axis/gate, and
  parity credit until separately earned.

One case may have frontend-only, interpreter, compiled-C, LLVM, plugin,
shared/static, or platform variants. Preserve their union and intersection;
never collapse them because they share source, expected output, or exit class.

## 9. Fail-closed control families

M2.5.1 must freeze at least these independent controls:

1. frontend success with C failure, C success with native-compile failure,
   link failure, loader failure, init failure, and runtime failure;
2. compiled versus IR-interpreted equal and deliberately divergent results;
3. `#reduce`, `#eval`, `#eval!`, `run_cmd`, monadic/pure output selection, sorry
   rejection, and isolated-stream behavior;
4. raw/effective import or IR-part drift inherited from M2.2;
5. pass-option/order, implemented-by, erasure, boxing, borrowing, RC, and
   symbol-name mutations with containing rows resealed;
6. C versus LLVM emission, supported/unsupported LLVM build, target mismatch,
   and corrupt/truncated intermediate artifacts;
7. bundled compiler versus `LEAN_CC`, missing tool, symlink/PATH drift,
   response-file mutation, and recursive dynamic-dependency drift;
8. compile-only versus link, static versus shared, PIC/LTO/optimization/debug/
   sanitizer/thread variants, and link-order changes;
9. valid/invalid/missing/duplicate/weak/hidden extern and export symbols;
10. extern backend `all`/C++/LLVM/adhoc/inline/opaque selection;
11. scalar, boxed, borrowed, owned, irrelevant, constructor, string, array,
    exception, and unsupported compound ABI shapes;
12. correct, omitted, repeated, reordered, wrong-builtin, and concurrent module
    initialization plus process setup/end-initialization boundaries;
13. reverse FFI, plugin/dynamic load, loader path drift, wrong architecture,
    stale library, and post-link mutation;
14. args/stdin/environment/filesystem/locale/time/random/network changes and
    unexpected effect detection;
15. normal exit, declared nonzero, signal, panic/assert, stack overflow,
    timeout, OOM, descendant leak, and cleanup failure;
16. uninstrumented versus sanitizer/tracer variants and perturbation;
17. matching output with different effect, symbol, implementation, or route;
18. marker/hook/Lake transfer mutation and an unaccepted parent;
19. partial/truncated evidence, retry, existing root, post-completion mutation,
    and mismatched local/tracking/remote refs; and
20. any nonzero outcome/pair/performance/parity field or terminal promotion.

## 10. Source-first sequence and process gate

1. **M2.5.0 plan:** this document freezes semantics and read-only floors. It
   creates no authority and runs no compiler/runtime/FFI process.
2. **M2.5.1 input/static authority:** only after accepted M2.1-M2.4 results,
   bind exact transfers, route expansion, toolchain/platform/library/cache
   state, artifacts, effects, controls, process formula, limits, evidence root,
   and authorization digest. Observed and credit fields remain zero.
3. **M2.5.2 implementation:** implement offline validation, process/store
   capture, compiler/artifact/ABI joins, effect accounting, and mutation tests;
   commit and push before rendering authorization.
4. **M2.5.3 attempt:** only exact later user authorization may run the frozen
   program. Validate immutable completion-last evidence before offline
   promotion.

Stop before any process if refs differ, a root exists, an accepted parent is
absent, source/toolchain/runtime state is dirty or ambiguous, recursive tools
or libraries are unbound, network/effect policy is incomplete, limits are
provisional, or the route formula is not exact. No M2.1-M2.5 execution is
authorized by this plan.

## 11. Acceptance and nonclaims

This plan is accepted only when the pinned identities and quantitative floors
reproduce, route/ABI/artifact/effect semantics and controls are explicit,
current parity/status surfaces register M2.5 without changing credit, complete
documentation gates pass, and all M2.1-M2.5 evidence/process/credit fields
remain absent or zero.

It does not claim that any declaration compiled or evaluated, C/LLVM/object/
library/executable was produced, tool ran, symbol linked/loaded/called,
initializer or runtime behavior occurred, output matched, or Axeyum supports
the route. Complete Lean parity still requires accepted M2.1-M2.7, M3, every
U0-U9 population, every A0-A11 axis, and every G1-G10 gate at one published
revision.

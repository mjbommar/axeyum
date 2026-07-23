# Lean U2 TL0.6.4 M2.6 plan — editor, server, and RPC closure

Status: **preregistered semantics plus an explicit M1 correction overlay only;
no M2.6 input authority, process budget, evidence root, server/client attempt,
transcript, request outcome, pair, performance row, or parity credit exists**

Date: 2026-07-23

Target: Lean `v4.30.0` at
`d024af099ca4bf2c86f649261ebf59565dc8c622`.

Parents:
[M2 program](lean-u2-native-surface-classification-tl0.6.4-m2-plan-2026-07-23.md),
[accepted M2.0 result](lean-u2-native-surface-classification-tl0.6.4-m2.0-result-2026-07-23.md),
[M2.1 pre-execution result](lean-u2-native-dependency-tl0.6.4-m2.1-pre-execution-2026-07-23.md),
[M2.2 effective-import correction](lean-u2-native-dependency-tl0.6.4-m2.2-effective-import-r1-plan-2026-07-23.md),
[M2.3 runner plan](lean-u2-native-dependency-tl0.6.4-m2.3-runner-generated-plan-2026-07-23.md),
[M2.4 Lake/project plan](lean-u2-native-dependency-tl0.6.4-m2.4-lake-project-plan-2026-07-23.md),
and [M2.5 compiler/runtime/FFI plan](lean-u2-native-dependency-tl0.6.4-m2.5-compiler-runtime-ffi-plan-2026-07-23.md).

## 1. Decision boundary

M2.6 must close every client/server transport, lifecycle, document, request,
notification, watchdog, worker, snapshot, cancellation, diagnostics, progress,
Lean RPC, widget, and restart edge transferred by accepted M2.3-M2.5 evidence.
It cannot equate a source import, protocol-shaped JSON field, successful Lean
frontend, exit zero, expected-output match, or normalized response with that
closure.

The singular rule is:

> One editor observation belongs to one exact client and server build,
> transport, initialization/capability exchange, process topology, workspace
> and module state, document lifetime/version/content/edit schedule,
> request/notification/RPC identity, chosen snapshot, cancellation/restart
> schedule, raw bidirectional transcript, terminal state, and registered
> normalization. Equal visible text does not collapse different schedules.

M2.6 owns:

- JSON-RPC/LSP framing, lifecycle, capabilities, request IDs, messages, errors,
  server-to-client requests, and the complete raw bidirectional transcript;
- the watchdog and per-file worker topology, routing, open-document state,
  crash/restart behavior, worker-to-watchdog traffic, and cleanup;
- document URIs, versions, full/ranged changes, snapshots, `InfoTree`-backed
  queries, diagnostics/progress, stale suppression, and cancellation causes;
- Lean RPC connect/call/keep-alive/release sessions, reference identity and
  lifetime, widgets, interactive diagnostics, and extension methods; and
- transcript normalization, schedule variants, security controls, and exact
  transfer rows to M2.7/M3.

M2.6 does not absorb M2.2 module/artifact resolution, M2.3 shell reachability,
M2.4 workspace/`lake setup-file` state, M2.5 compiler/runtime ownership, or
M2.7 cross-variant merging and parity credit. It consumes accepted transfers
from those owners and returns exact protocol/process rows.

## 2. Frozen M1 correction overlay

The accepted M1 content authority is immutable evidence of what its v1
classifier produced. It provisionally marks 147 direct and 147 closure cases
as `editor-rpc`: 137 have an M0 harness floor, 22 have a content observation,
and their union is 147. Eighteen cases contain one exact `lean.server-api`
signal each. No case contains `json.rpc-method` or `text.rpc-candidate`.

M1's `json.document-version` matcher promoted any nested JSON key named
`version`, `textDocument`, `contentChanges`, or `cancel`. It projected eleven
generic Lake manifest/configuration `version` fields into these four cases:

| Rejected case | Non-protocol files responsible |
|---|---|
| `tests/lake/examples/deps/test.sh` | `tests/lake/examples/deps/bar/lake-manifest.expected.json` |
| `tests/lake/tests/manifest/test.sh` | `lake-manifest-latest.json`, `lake-manifest-v1.0.0.json`, `lake-manifest-v1.1.0.json`, `lake-manifest-v1.2.0.json`, and `lake-manifest-v4.json` through `lake-manifest-v7.json` under that case |
| `tests/lake/tests/reservoirConfig/test.sh` | `tests/lake/tests/reservoirConfig/expected.json` |
| `tests/lake/tests/toml/test.sh` | `tests/lake/tests/toml/tests/valid/inline-table/end-in-bool.json` |

Those four cases have no other editor/RPC signal and are not server harnesses.
M2.6 therefore rejects only their `editor-rpc` projection, leaving every M1
byte, hash, case row, other surface, and historical statement unchanged. The
qualified source-only M2.6 floor is **143**, partitioned as 132
`server_interactive`, five `elab`, four `server`, one `doc-examples`, and one
`misc_dir` case; 142 are pile cases and one is a directory case. The complete-
parity regression mechanically holds the 147 historical rows, four rejected
cases, eleven rejected projected hits, two genuine server JSON files with the
same raw signal, and 143-row corrected floor.

This is a downstream correction overlay, not a regenerated M1 authority or an
execution denominator. A future classifier schema may replace the broad
matcher only under a new versioned authority and explicit migration; it cannot
rewrite accepted M1 history.

## 3. Pinned implementation surface

The later M2.6.1 authority must revalidate at least these clean-checkout bytes
and transitively enumerate every implementation file actually reached by each
bound route:

| Pinned source | SHA-256 | Boundary |
|---|---|---|
| `src/Lean/Data/Lsp/Communication.lean` | `1cbb1edfd38179d71d1505965ec13abe8227782b9d983a20a86ad8eefff30f64` | JSON-RPC/LSP stream framing |
| `src/Lean/Data/Lsp/Ipc.lean` | `dc4c9027a709be1dc8fb4c630b3a0208e8d9a3fa8cdfc0261da83a37b6126cc1` | official test client, message filtering, waits, and child process |
| `src/Lean/Server.lean` | `df2521aa37785783247a6f64b6d4819463d6c232fafdb7798e355207e8672ff8` | server module root |
| `src/Lean/Server/README.md` | `afd3f700d54338c9d9cf62e8c39f49811a1126295fedcfa58322e5661f09c35b` | pinned architecture account |
| `src/Lean/Server/ProtocolOverview.lean` | `89da37e4e70a353f2c39e769560eb704159ea4e1e6bd5c7a2262e1de0c6d29db` | complete pinned protocol/API inventory |
| `src/Lean/Server/Watchdog.lean` | `9c02639a6aca6dd30a768ad6b25e686e160c089a6adb65cea728527512fb02c9` | lifecycle, routing, file state, workers, restart |
| `src/Lean/Server/FileWorker.lean` | `92979569762cfd22a221b36df241ea5cbbeb4fbc3a84409dec236f9087a350aa` | document processing, output ordering, pending requests and RPC sessions |
| `src/Lean/Server/FileWorker/RequestHandling.lean` | `56781ae9b1e21770e5c95172f20f382730b56910bd224ee667d08782d84ac6d2` | snapshot-backed request dispatch |
| `src/Lean/Server/FileWorker/SetupFile.lean` | `989c4b49dab0028051f638315d333df2fad977205cb05e3220e9f053a9c75fd1` | project setup transfer from M2.4 |
| `src/Lean/Server/Requests.lean` | `96abe50cddb0a2d5fefdc1da74929729cd2692c0164411b161850d1483173503` | request contexts, snapshot selection, task behavior |
| `src/Lean/Server/RequestCancellation.lean` | `1a88993d4b9fa4e1dc8bc56d6e4a6ccb1255efffdf059333ca819ebc4463cdd3` | explicit-cancel versus edit-cancel identity |
| `src/Lean/Server/Rpc/Basic.lean` | `a85d469073170db6949f5a0652aa7c363ef12233537949abc9c6e7c0bf614e1a` | RPC encoding, stores, references, and refcounts |
| `src/Lean/Server/Rpc/RequestHandling.lean` | `8ee6a6b6169f4544fc7377e0ccac6368de28a9e39b43a54556b0166ed4428dcc` | session-aware RPC dispatch |
| `src/Lean/Server/Snapshots.lean` | `acccb9b2d3da683d5881c353641451ee9b42e34d5a1012a5a3573bd4268f112c` | snapshot navigation |
| `src/Lean/Server/ServerTask.lean` | `bbb292f6b5d3f1733f25caca9018a771c04ad08bebd1e29ebc6518466b69c8fe` | asynchronous task and cancellation behavior |
| `src/Lean/Server/Test/Runner.lean` | `38cad0a3ec35ee59aae2cdaa250e49b47d3176bc8d4419c0a135605e9e1413e4` | interactive directive expansion and normalization |

The pinned `ProtocolOverview` declares 59 API rows: 37 LSP/Lean requests, 12
notifications, and ten Lean widget RPC methods. It is the candidate protocol
denominator, not proof that the current tests reach every row. The official
[Lean protocol overview](https://lean-lang.org/doc/api/Lean/Server/ProtocolOverview.html),
[Lean server API](https://lean-lang.org/doc/api/Lean/Server.html), and
[Language Server Protocol](https://microsoft.github.io/language-server-protocol/)
are contextual documentation. The current LSP page identifies 3.18 as latest;
pinned Lean v4.30.0 source, including its documented standard deviations, is
authoritative here.

## 4. Current read-only route floor

The corrected 143 cases split into two materially different groups:

| Route class | Cases | What source proves |
|---|---:|---|
| interactive server harness | 132 | tracked files run through `Lean.Server.Test.Runner` and `lean --server` |
| raw server harness | 4 | three server initialization/lifecycle routes and one diagnostics route, including direct `--worker` |
| Lake-backed project server harness | 1 | `lake build`, then the interactive runner through `lake serve` |
| server/RPC API source only | 6 | one documentation example and five elaborator cases import/use server APIs but do not thereby start an LSP process |

Thus 137 cases have a registered server-process harness and six have only a
content-level API signal. The latter remain conditional compile/elaboration
edges until accepted M2.3-M2.5 evidence proves more; they cannot inherit a
server transcript from their imports.

The 132 interactive sources contain 182 `didOpen`/`didClose` segments after
`-- RESET` expansion, 838 parsed directives across 33 directive names, 57
ranged edit directives, and 128 expected-output sidecars. Every case initializes
one server and shuts it down once; every segment opens version 1, advances edit
versions from 2, performs a final diagnostics wait, and closes the document.
The runner starts request IDs at 0 for initialization and 1 for the session.

These counts are only a source floor. Completion/code-action/RPC response
contents can trigger a data-dependent number of resolve, popup, trace-child,
or hierarchy requests. `readResponseAs` also discards intervening notifications
and server-to-client requests by design. M2.6.1 must derive the exact planned
outgoing floor and register dynamic event bounds; the attempt must retain the
full raw duplex stream before helper filtering or normalization. Neither 838
directives nor 59 API rows is an executable request denominator.

## 5. Process, workspace, and transport identity

Each route retains the outer CTest/wrapper process from M2.3, any `lean --run`
test client from M2.5, and every server child. Raw tests spawn `lean --server`
or `lean --worker`; interactive tests spawn `lean --server`; the project route
first builds and then spawns `lake serve -- -DstderrAsMessages=false
-Dexperimental.module=true`. Record the watchdog plus every per-file worker,
their executable and dynamic-library closures, argv, cwd, environment, stdio,
process group, parent/child identity, resource limits, signals, exit state,
files, sockets, and cleanup.

Bind the M2.4 workspace/configuration/manifest and exact `lake setup-file`
request/result used by a worker. Bind M2.2 effective imports/artifacts and M2.5
compiler/runtime routes used inside worker elaboration, metaprograms, `#eval`,
widgets, or generated clients. A watchdog exit does not prove worker cleanup;
a restarted worker is a distinct process epoch.

Retain the raw byte stream in each direction, all `Content-Length` headers,
JSON bytes, framing boundaries, parse results, send/receive sequence numbers,
monotonic timestamps, producer/consumer process epochs, and EOF/error state.
Canonical parsed JSON is a derived view and never replaces raw transport
evidence. Registration includes malformed length/encoding/JSON, duplicate and
unknown fields, duplicate/out-of-order IDs, partial frames, output pollution,
backpressure, early EOF, and oversized-message limits.

## 6. Lifecycle, documents, snapshots, and publication

For initialization retain the exact client identity, root/cwd behavior,
initialization options, all advertised capabilities, server capabilities,
dynamic registration requests and client responses, `initialized`, shutdown,
exit, pre-init/post-shutdown traffic, and terminal status. Lean's pinned
protocol overview says the server ignores most standard client capabilities,
uses server cwd rather than `rootUri`, and requires documents to be opened
before file messages; those deviations need positive and negative controls.

For each document epoch retain URI/path normalization, language, initial bytes,
version, every ordered full/ranged content change, UTF position interpretation,
save/watch events, close, reopen/reset, on-disk versus in-memory state, selected
workspace, dependency-build mode, and resulting worker epoch. Versions and
request IDs are scoped data, not generic JSON evidence.

For each response/notification retain the requested cursor/range and the exact
snapshot/`InfoTree`/environment version used, wait behavior, completeness,
diagnostics and progress sequence, references/module-index version, and whether
the result was current, partial, stale-suppressed, or rejected. Preserve raw
diagnostic order before the official test runner's range/message sort and raw
URIs, metavariable suffixes, reference URLs, RPC pointers, and trace children
before normalization.

Explicit `$/cancelRequest` and edit-triggered cancellation use separate tokens
in pinned Lean and must remain separate outcome causes. Register cancellation
before dispatch, during snapshot wait/handler/response emission, after
completion, duplicate/unknown cancellation, edits with pending requests, and
responses that race cancellation. Also bind stale-dependency notifications,
worker crashes, diagnostics clearing, restart-on-edit behavior, import refresh,
state replay, and requests spanning a worker epoch.

## 7. Requests, notifications, and Lean RPC

Every protocol event retains direction, method, request ID or notification
identity, raw and decoded parameters/result/error, document/version, selected
handler, response order, cancellation token/cause, process epoch, and any
server-to-client request plus its response. Notifications silently discarded
by a test helper remain transcript events. Missing, duplicate, late, wrong-ID,
wrong-method, wrong-shape, unsupported, and handler-error events are explicit
outcomes rather than harness noise.

For `$/lean/rpc/connect`, `$/lean/rpc/call`, `$/lean/rpc/keepAlive`, and
`$/lean/rpc/release`, retain the document/worker epoch, session ID, method,
position, negotiated wire format, object-store state, each server object/type,
stable object ID, client `RpcRef`, reference-count transition, keep-alive
deadline, release multiplicity, expiry, and failure. The runner's normalized
small integer RPC pointers are comparison artifacts only; raw identities and
lifetime transitions remain evidence. Worker restart, release after restart,
unknown/expired sessions, wrong reference type, reserved `__rpcref`, cyclic or
large values, lazy trace expansion, and widget source/hash/props are mandatory
controls.

Lean v4.30 also introduced experimental
[`idbg`](https://lean-lang.org/doc/reference/latest/releases/v4.30.0/#experimental-live-debugging-with-idbg),
which connects a running compiled program to the language server over TCP and
re-evaluates edited expressions. M2.5 owns the compiled program/runtime endpoint;
M2.6 owns server session, transport, edit/result scheduling, network policy,
authentication/exposure, disconnect/reconnect, and stale diagnostic behavior.
No current 143-case row receives `idbg` coverage by implication.

## 8. Required evidence schema

M2.6.1 and later results must retain domain-separated rows for:

- accepted parent transfer, correction-overlay decision, case/profile/provider/
  platform, route, process, document, session, worker, and attempt IDs;
- executable/dynamic closure, workspace/setup/import/runtime identities and
  process tree, resource envelope, effects, terminal state, and cleanup;
- raw transport chunks/frames plus decoded messages, ordering, timestamps,
  request/response joins, handler/snapshot selection, errors, and filtering;
- initialization/capabilities, document versions/content changes, diagnostics/
  progress/publication, cancellation, stale suppression, crash/restart, and
  dependency refresh;
- RPC sessions, methods, object/reference lifetimes, widget/interactive values,
  normalization inputs/outputs, and comparison policy;
- static candidate API coverage, source directive floor, planned/dynamic event
  accounting, observed method coverage, and explicit residuals; and
- zero native outcome, pair, performance, complete population/axis/gate, and
  parity credit until separately earned.

One case can have multiple clients, capabilities, workspaces, document/edit
schedules, worker epochs, protocol methods, snapshots, normalization policies,
or platforms. Preserve their union and intersection; never collapse them
because they share source, final output, or exit class.

## 9. Fail-closed control families

M2.6.1 must freeze at least these independent controls:

1. the four rejected Lake `version` cases, two genuine server JSON files, a
   string-valued RPC `method`, and unrelated nested JSON fields;
2. valid/invalid `Content-Length`, UTF encoding, JSON, batching, partial frames,
   duplicate headers, trailing bytes, stdout pollution, backpressure, and EOF;
3. initialize/initialized/shutdown/exit order, duplicate lifecycle messages,
   pre-init and post-shutdown requests, client capability variants, and cwd
   versus `rootUri`;
4. open/change/save/watch/close/reopen/reset, unopened/closed files, URI aliases,
   full/ranged/multibyte edits, version gaps/regressions/duplicates, and disk
   divergence;
5. request and notification direction, unique/duplicate/wrong/late IDs,
   malformed/unknown methods and parameters, server-to-client request handling,
   errors, and ignored messages;
6. snapshot before/at/after cursor, incomplete/partial/finished trees, reused
   snapshots and interactive identities, and deterministic selection;
7. raw versus normalized diagnostics, progress, URI, metavariable, URL, pointer,
   reference, order, and trace values, including normalization collisions;
8. explicit cancellation versus edit cancellation at every request phase,
   duplicate/unknown/late cancel, non-cooperative work, partial response, and
   cleanup;
9. stale diagnostics/results/references/module data, version races, save/import
   refresh, stale dependency, and cross-worker request races;
10. watchdog, worker, and test-client normal exit, nonzero exit, panic, signal,
    timeout, OOM, stack overflow, blocked pipe, crash/restart, leak, and orphan;
11. zero/one/multiple documents and workers, dependency chains, worker setup
    failure, `lake setup-file` drift, project/non-project routing, and restart
    state replay;
12. each of the 37 request, 12 notification, and ten RPC candidate API rows,
    with reached/unreached/unsupported accounting rather than inferred coverage;
13. completion/code-action resolve fan-out, recursive call/module hierarchy,
    popup and lazy-trace expansion, zero/one/many dynamic children, and cycles;
14. RPC connect/call/keepAlive/release order, unknown/expired/restarted sessions,
    duplicate/under/over-release, reference reuse/type mismatch, and expiry;
15. widget/interactive diagnostic identity, server object lifetime, wire-format
    capability variants, reserved fields, payload limits, and malformed values;
16. `idbg` disabled/enabled, wrong program/build/workspace, TCP bind/connect/
    disconnect/reconnect, concurrent sessions, edits, stale results, and network
    isolation;
17. equivalent visible response with different snapshot, worker, session,
    hidden notification, side effect, schedule, or normalization input;
18. marker/hook/provider/Lake/compiler transfer mutation and an unaccepted
    M2.1-M2.5 parent;
19. partial/truncated evidence, retry, existing root, post-completion mutation,
    and mismatched local/tracking/remote refs; and
20. any nonzero outcome/pair/performance/parity field or terminal promotion.

## 10. Source-first sequence and process gate

1. **M2.6.0 plan:** this document freezes semantics, the M1 correction overlay,
   and read-only floors. It creates no authority and starts no client, server,
   worker, Lake, compiler, runtime, RPC, debugger, or network process.
2. **M2.6.1 input/static authority:** only after accepted M2.1-M2.5 results,
   bind exact qualified cases, routes, API rows, workspaces, processes,
   documents, source directives, dynamic-event bounds, controls, process
   formula, limits, evidence root, and authorization digest. Observed and
   credit fields remain zero.
3. **M2.6.2 implementation:** implement offline validation, full-duplex capture,
   process/document/request/session joins, schedule accounting, normalization,
   mutation tests, and immutable completion-last storage; commit and push
   before rendering authorization.
4. **M2.6.3 attempt:** only exact later user authorization may run the frozen
   program. Validate complete raw and derived evidence before offline promotion.

Stop before any process if refs differ, a root exists, an accepted parent is
absent, the correction overlay drifts, source/workspace/toolchain state is dirty
or ambiguous, a protocol/process/API denominator is unfrozen, server-to-client
traffic can be lost, child cleanup is incomplete, network/resource limits are
provisional, or the route formula is not exact. No M2.1-M2.6 execution is
authorized by this plan.

## 11. Exit from M2.6

M2.6 can hand rows to M2.7 only when every accepted route has immutable
transport, process, workspace, document/snapshot, request/cancellation,
publication, RPC/session, normalization, terminal, and cleanup evidence; every
candidate API row and dynamic event is reached, rejected, or retained as an
explicit residual; all controls pass; and no provisional classification is
silently promoted.

Even then, M2.6 proves only exact editor/server/RPC dependency and observation
closure for the bound U2 variants. It does not complete U2, U5, A7, any matched
Axeyum pair, any terminal gate, or Lean parity. M2.7/M3 still own cross-variant
merging, residual review, outcome comparison, and credit.

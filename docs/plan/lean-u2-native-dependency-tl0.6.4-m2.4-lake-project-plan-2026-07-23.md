# Lean U2 TL0.6.4 M2.4 plan — Lake workspace and project closure

Status: **preregistered semantics only; no M2.4 input authority, helper,
process budget, evidence root, configured workspace, package/target/facet
edge, observation, or credit exists**

Date: 2026-07-23

Target: Lean `v4.30.0` at
`d024af099ca4bf2c86f649261ebf59565dc8c622`.

Parents:
[M2 program](lean-u2-native-surface-classification-tl0.6.4-m2-plan-2026-07-23.md),
[accepted M2.0 result](lean-u2-native-surface-classification-tl0.6.4-m2.0-result-2026-07-23.md),
[M2.1 pre-execution result](lean-u2-native-dependency-tl0.6.4-m2.1-pre-execution-2026-07-23.md),
[M2.2 source/artifact plan](lean-u2-native-dependency-tl0.6.4-m2.2-plan-2026-07-23.md),
[M2.2 effective-import correction](lean-u2-native-dependency-tl0.6.4-m2.2-effective-import-r1-plan-2026-07-23.md),
and [M2.3 runner/generated-artifact plan](lean-u2-native-dependency-tl0.6.4-m2.3-runner-generated-plan-2026-07-23.md).

## 1. Purpose and dependency boundary

M2.4 must close the Lake workspace, package, target, facet, configuration,
manifest, materialization, and cache graph reached from every accepted M2.3
boundary command. It cannot equate a `lake` token, a package configuration, a
manifest row, a query result, or a successful build with that complete graph.

The singular M2.4 rule is:

> A Lake edge belongs to one exact workspace state: configuration source and
> evaluation, manifest and ordered overrides, materialized package trees,
> toolchain/environment, target/facet request, build configuration, and
> pre/post store. No command name or output path may stand in for that state.

This plan freezes semantics before any M2.4 authority or implementation. It
does not invoke Lake, evaluate a configuration, create a workspace, update a
manifest, materialize a package, query or build a target, access a cache or
network endpoint, or add dependency/native/pair/parity credit.

M2.4 owns:

- workspace and configuration-file discovery;
- Lean/TOML configuration evaluation and its cached configuration artifacts;
- manifests, package overrides, dependency materialization, and package order;
- target-spec parsing, default targets, facets, custom targets, and build-job
  topology;
- Lake setup projections, build traces, local/remote cache metadata, and
  project-generated files; and
- the configured Lake boundary into compiler, linker, executable, server,
  external-tool, and network work.

It does not absorb:

- raw/effective Lean import and `.olean`-part semantics from M2.2;
- CTest, wrapper, shell, hook, marker, or child-command reachability from M2.3;
- actual compiler/linker/native-runtime/FFI/process behavior from M2.5;
- request, document, version, edit, cancellation, or transcript semantics from
  M2.6; or
- cross-provider merge and residual review from M2.7/M3.

An M2.4 configured target may point to an M2.5 or M2.6 child without closing
that child's owner. The exact M2.4 case/variant denominator remains downstream
of accepted M2.1-M2.3 evidence; the source audit below is only a floor.

## 2. Pinned proof surface and read-only research floor

The later M2.4.1 input authority must revalidate at least these exact target
files and transitively enumerate every implementation file used by the bound
Lake executable:

| Pinned source | SHA-256 | M2.4 rule |
|---|---|---|
| `src/lake/Lake/Config/Env.lean` | `ef138a965d4925430872bfe17fecfbac9918a1591a32b137c129e014160a2545` | process/toolchain/cache/search-path environment |
| `src/lake/Lake/Load/Config.lean` | `4cefa5608c40b09dc2f09c5a9bde268a7ecf1e2958aea097f65045e5e823ff6b` | complete workspace load inputs |
| `src/lake/Lake/Load/Package.lean` | `76f81510f46bc8a818a43434b88757b2205cea4c4110026ce9f906527528077f` | explicit extension and Lean-before-TOML selection |
| `src/lake/Lake/Load/Workspace.lean` | `4b8408625a6a26af64cca9be45fdf2d8b6eff598300291d30c73407d83ede65b` | root load, manifest fallback, update/materialization |
| `src/lake/Lake/Load/Manifest.lean` | `f02a122996066cf46493f0015b9fa8654f1567e3e68075eedeefc53de899f29b` | manifest version and exact package entries |
| `src/lake/Lake/Load/Resolve.lean` | `5f68db06b06f4c9b199d1d41efdc6894541e2e3d7c27d7c6558ab9032cf90e80` | dependency resolution, override order, manifest writes |
| `src/lake/Lake/Load/Materialize.lean` | `a90578143785ef745b25dd99dd68ee02dde10bedde68f7c89733c38e8d44792d` | path/Git package materialization and checkout state |
| `src/lake/Lake/Load/Lean/Elab.lean` | `a82779fc0106c17ad2286715a19dfd87ce728422916a09e2c8c9aeebff9cfbcc` | executable Lean configuration and cached OLean behavior |
| `src/lake/Lake/Load/Toml.lean` | `dd11843d899ced1103cc3a70dd807d30a88eb809641f37adb519e99c8219641a` | declarative TOML decoding |
| `src/lake/Lake/CLI/Main.lean` | `dd6096edf0ddd731254698192f78bcafd1586095969e153404513d8bfb21ec64` | command options, build/query/update/setup dispatch |
| `src/lake/Lake/CLI/Build.lean` | `c331755cdeab8ee10076a6092408fc81828785b01df02d698b3c842113d00e3c` | target/facet/path resolution and query fetching |
| `src/lake/Lake/CLI/Serve.lean` | `013ee743584ca9d0f19ce886aa795cdb93f59e3c389965667626d09912e0d600` | `setup-file` build and server boundary |
| `src/lake/Lake/Build/Context.lean` | `9df71322393c5cc3bf0c62f5356e14be810b8591f48c37792405206aad068e49` | old/hash/no-build/output-map build state |
| `src/lake/Lake/Build/Trace.lean` | `6bdbbb078c712ef5380a300be198422b3a72d9503d76d4f7787a435aa55cb0f5` | incremental trace representation |
| `src/lake/Lake/Build/Module.lean` | `5f571af60381a38095821a086a5bb8ab332652e341f54ad070b4da7cc3b9eb98` | imports, module artifacts, setup, dynlibs, plugins, facets |
| `src/lake/Lake/Build/Package.lean` | `24ded762ba509fda6ee498932ed76cea70d3755eecbea26d18fec8606ccaf448` | package dependency/cache/release facets |
| `src/lake/Lake/Build/Library.lean` | `758ecbd4d7a23b38b16210366af2c5df9a28a152cc5dde3fe5dcbdd7a38b25af` | library modules/default/native facets and extra dependencies |
| `src/lake/Lake/Build/ExternLib.lean` | `207f3350dd3a728ce36b9a135578a1d3a3738b44e2fd66b3cded55410e97d1f7` | external-library configured targets |
| `src/lake/Lake/Build/Executable.lean` | `62d52713d69aac28205ec65ad78c268f70218cd6c69316f14c1e71e3d315f9f7` | executable configured targets |
| `src/lake/Lake/Build/InitFacets.lean` | `cf40908649d37f8bad6d3527c8bd0e26381c413c6f4ad3adc25209654cf5e389` | builtin facet registry |

The official GitHub API maps `refs/tags/v4.30.0` directly to the target commit
and reports tree `0271450d1b109f9a0e5fadea2b6044160e9af7dd`. It reports
`CLI/Main.lean` as the 46,527-byte Git blob
`65b0e7fd0d6cd21d512edb49a276bcc65ae31c78`, `Load/Workspace.lean` as
the 2,176-byte blob `9f25dd62bc752ede695a25fc20371157eb65d64b`, and
`Build/Module.lean` as the 58,010-byte blob
`1a109c899aabab7deb1e1b182e59c22cee8335dc`. These corroborate the
clean-checkout SHA-256 rows; they do not replace process or workspace
identity.

Primary online context is the official
[Lake reference](https://lean-lang.org/doc/reference/latest/Build-Tools-and-Distribution/Lake/),
[Lean 4.30 release note](https://lean-lang.org/doc/reference/latest/releases/v4.30.0/),
and pinned
[`CLI/Main.lean`](https://github.com/leanprover/lean4/blob/d024af099ca4bf2c86f649261ebf59565dc8c622/src/lake/Lake/CLI/Main.lean),
[`Load/Workspace.lean`](https://github.com/leanprover/lean4/blob/d024af099ca4bf2c86f649261ebf59565dc8c622/src/lake/Lake/Load/Workspace.lean),
and [`Build/Module.lean`](https://github.com/leanprover/lean4/blob/d024af099ca4bf2c86f649261ebf59565dc8c622/src/lake/Lake/Build/Module.lean).
The pinned implementation is authoritative when later reference prose differs.

This section is read-only research. It creates no configured-source,
workspace, package, target, facet, job, artifact, cache, network, or outcome
evidence.

## 3. Current registered floor, not the final M2.4 denominator

The accepted U2 authority contains 52 direct inline Lake cases: seven in both
profiles and 45 full-Lake-only. A clean pinned-source audit additionally finds
28 of the 31 registered wrapper-directory runners with active lexical Lake
child-command candidates. Those candidates require M2.3 static or trace proof
before becoming M2.4 inputs.

| Read-only route | Cases/scopes | Tracked support files | Bytes | Tracked config roots |
|---|---:|---:|---:|---:|
| configured inline Lake | 52 | 1,045 | 250,410 | 70 |
| wrapper-directory Lake candidates | 28 | 270 | 168,866 | 37 |
| disjoint research-floor union | 80 | 1,315 | 419,276 | 107 |

The 107 roots contain 60 Lean-only configurations, 40 TOML-only
configurations, and seven roots containing both, for 67 `lakefile.lean` and 47
`lakefile.toml` files. Nine direct Lake cases have no tracked configuration
root because they exercise no-config commands or create/translate workspace
files during the case. No selected support scope contains a tracked live
`lake-manifest.json`; manifests are generated, copied from fixtures, or
otherwise mutated during execution. The 80-scope floor contains 29 tracked
`lean-toolchain` files.

These counts deliberately do not include shared support reached outside a
case's support scope, such as `tests/lake/tests/common.sh`. Conversely, a
support scope may contain an unexecuted helper such as `cache/online-test.sh`
or `toml/fetch-tests.sh`. Content inclusion is neither reachability nor
exclusion. Accepted M2.3 edges must add shared support and reject unreachable
support files before M2.4.1 freezes its exact input set.

The pinned CMake tree has 55 `tests/lake/{examples,tests}/**/test.sh` paths and
registers 52. It excludes `examples/bootstrap`, `tests/toolchain`, and
`tests/online`; their reasons and bytes remain selection evidence, not U2
cases. The exact M2.4 denominator can be larger than 80 if M2.3 proves another
dynamic Lake boundary and smaller than 80 if a lexical wrapper candidate is
unreachable. It cannot be guessed from this audit.

## 4. Workspace discovery and configuration identity

Every M2.4 projection must bind:

- exact `lake` executable and recursive dynamic identity, Lean toolchain,
  Lake home, platform, architecture, cwd, `-d` root, `-f` configuration path,
  ordered CLI options/`-K` settings, and remaining subcommand arguments;
- pre-normalized and resolved workspace/package/configuration paths, symlink
  chain, file type, mode, bytes, SHA-256, Git identity, and clean-state owner;
- the complete environment allowlist, especially `ELAN*`, `LAKE*`, `LEAN*`,
  `RESERVOIR*`, `HOME`, `XDG_CACHE_HOME`, `PATH`, compiler/archive overrides,
  library paths, proxy/TLS variables, locale, and platform variables;
- system Lake configuration path/absence and bytes, package URL map, cache
  directory/service/endpoints, artifact-cache policy, initial `LEAN_PATH` and
  `LEAN_SRC_PATH`, and every executable resolved through `PATH`; and
- pre-tree inventory plus a private writable workspace/store. The pinned Lean
  checkout and accepted U2 authority remain read-only.

If `-f` has an extension, only that exact supported file is selected. Without
an extension, pinned Lake checks `.lean` before `.toml` and logs that choice
when both exist. M2.4 must retain both candidates, their existence/type/content,
the selected path, selection reason, and explicit-versus-default status.
Normalizing first and then silently picking a different file is invalid.

### 4.1 TOML and Lean are not equivalent evidence routes

TOML configuration is declarative only after the exact pinned parser and
decoder accept its bytes. The decoded package still depends on defaults,
environment, platform, toolchain, and Lake version.

A Lean configuration is executable Lean code. It may import modules, read
environment/files, run arbitrary configuration-time IO, register custom
targets/facets/scripts containing opaque functions, and vary by platform or
options. Lexical DSL rows cannot close it. The later attempt must evaluate it
under the bound environment and retain process/file effects plus the resulting
workspace projection. Unsupported dynamic configuration becomes a typed
residual or observed trace requirement, not an inferred declarative row.

### 4.2 Configuration cache and generated projects

Lean configuration results may be cached under `.lake/config/**` as OLean
state. `--reconfigure`, source/configuration hashes, imported Lake modules,
toolchain identity, cached file presence, and the exact cache selected at load
time are therefore part of the projection. A current `lakefile.lean` beside a
stale accepted `.olean` is not current configuration evidence.

`lake init`, `lake new`, and `lake translate-config` create or transform
workspace files. Their templates, language, requested name, destination,
pre-tree, generated paths/modes/bytes, and post-tree must be retained. Later
commands bind the generated bytes actually present, not the template or the
source that existed before generation.

## 5. Manifests, overrides, and materialized packages

A missing manifest does not mean zero dependencies. Unless the bound command
and configuration choose a different route, `loadWorkspace` calls
`updateAndMaterialize`, which can resolve versions, write
`lake-manifest.json`, clone/update Git repositories, change
`lean-toolchain`, and contact Reservoir or another endpoint. M2.4 must record
the branch taken before claiming any package graph.

The target manifest format is `1.2`; the loader also contains explicit
compatibility behavior for older versions. Every manifest row retains raw
bytes, parsed version, root name, Lake/packages directories, fixed-toolchain
state, ordered package entries, scope/inherited/config/manifest paths, and
path-versus-Git source including URL, input revision, resolved revision, and
subdirectory.

Materialization applies package entries in this order:

1. manifest entries;
2. `.lake/package-overrides.json` entries; and
3. ordered CLI `--packages` entries.

Later insertions for the same package name win. The authority must retain all
shadowed rows, the winner and reason, and package indices used to disambiguate
same-named packages. It must not sort away manifest order or merge aliases.

For a path dependency, retain lexical/resolved paths, containment, file-tree
identity, and the rule that no copy is made. For a Git dependency, retain the
configured and package-map URL, filtered remote identity, repository state,
revision lookup, checked-out commit, clean/dirty/untracked state, subdirectory,
and every materialization process/effect. A local `file://` Git repository is
still a Git materialization, while a remote-looking URL that is never fetched
is only a conditional edge.

Nested package manifests/configurations and toolchain-update/restart behavior
must be explicit. One root package's successful load cannot close a dependency
whose configuration or nested manifest failed, drifted, or was skipped.

## 6. Target, facet, and job-graph semantics

M2.4 must retain the exact ordered target specifications and reproduce pinned
resolution, including:

- `@package`, `package/target`, `+Module`, filesystem path, and `:facet`
  disambiguation;
- default root/package targets when no explicit target remains;
- package, module, library, executable, external-library, input-file/input-dir,
  and custom target kinds;
- target lookup order across the topologically ordered package workspace;
- default and explicit builtin/custom facets, buildability, output formatter,
  and every expansion from one request into multiple build specs; and
- registered job keys, dependency edges, cycle/failure state, scheduling
  owner, produced value/artifact, and final requested result order.

Custom targets, facets, and scripts can execute arbitrary Lean IO. Their
configured existence is not their dependency closure. They require exact
evaluated configuration plus supported static semantics, a separately retained
observed job/process/file trace, or a reviewed decline.

### 6.1 `lake query` is a build, not a read-only dependency dump

Pinned `lake query` loads the workspace, parses the same target specifications
as `lake build`, calls each target's fetch job, and only then formats results.
It can configure, update/materialize, build, restore/fetch artifacts, run custom
jobs, and write traces/caches. `lake query ...:deps --json` can contribute an
exact requested-facet result, but it cannot by itself prove all internal jobs,
inputs, effects, unselected facets, or package variants.

Query result order, duplicates, empty/null outputs, text/JSON formatter, raw
streams, terminal state, and all build evidence must be retained separately.
A printed artifact path proves neither existence nor the inputs that produced
it until content and provenance are checked.

### 6.2 `lake setup-file` is a build projection, not full closure

Pinned `setup-file` loads a workspace, identifies an internal or external
module, parses or accepts a header, builds imports/extra dependencies and
configured dynamic libraries/plugins, and prints `ModuleSetup` JSON. The
underlying top-level setup code explicitly does not construct a proper trace
state. It is a valuable projection of name/package, header mode, import
artifacts, dynlibs, plugins, and options, but not a complete Lake job/artifact
trace and not an editor transcript.

M2.4 owns that configured setup projection. M2.2 validates its module/artifact
resolution, M2.5 owns compiler/load/runtime behavior, and M2.6 owns the later
server request sequence. `lake serve` fallback and JSON-RPC behavior cannot be
credited under M2.4 merely because `setup-file` succeeded.

## 7. Build state, traces, artifacts, and caches

Every build/query/setup attempt must bind the exact `BuildConfig`, including
old-mode, hash trust/rehash, `--no-build`, verbosity, output-mapping path,
resource limits, concurrency, and cache flags. The pre-state must inventory:

- source/configuration/manifest/override/dependency trees;
- `.lake/config`, `.lake/build`, package stores, local/system artifact caches,
  trace/hash/`.nobuild` files, output mappings, staged files, and module
  archives;
- toolchain and platform artifacts plus filesystem timestamp resolution; and
- absence as an explicit state, not an omitted row.

Post-state records every create/read/write/remove/rename/link, mode, mtime,
size, SHA-256, producer job/process, and pre-state relationship. Lake's own
incremental/content hashes and traces are inputs to its behavior, not
cryptographic evidence identities. Every retained artifact and output mapping
receives an independent SHA-256 and domain-separated record seal.

Lean 4.30 adds on-demand remote artifact retrieval, platform-sensitive output
mappings, `.ltar` module archives, and changed cache restoration behavior.
M2.4 must distinguish at least:

- built locally, already up to date, replayed, restored from local cache,
  fetched from remote cache, unpacked from module/package archive, and absent;
- root versus dependency outputs and platform-dependent versus independent
  mappings;
- declared cache service, selected service, input/output mapping, remote
  scope/revision/toolchain/platform key, local object, and build-directory
  projection; and
- cache lookup/fetch failure from target build failure or optional fallback.

No user-global cache or package directory may be used implicitly. Each
provider/attempt receives an isolated, pre-inventoried cache namespace or an
explicit empty-cache state.

## 8. Network and external-state policy

The three explicitly excluded Lake tests are not permission to ignore network
semantics in selected cases. The selected tree contains distinct shapes that
must not be blended:

- a configured URL or endpoint retained only as data;
- an invalid remote installed specifically to prove no fetch occurs;
- an unexecuted online helper present inside a selected support scope;
- local `file://` Git materialization;
- an expected cloud-release/cache failure that may invoke `curl`; and
- a real online package/cache operation.

M2.4.1 must classify every endpoint and branch before any process. A later
attempt binds DNS/proxy/TLS/CA state, executable identities, endpoint
allowlist, credentials-absent rule, timeout, byte limits, cache state, and
expected request/response/effect classes. Secrets are forbidden from inputs
and evidence; post-capture redaction is not an authority strategy.

No network is permitted merely because a command is called `update`, `build`,
`query`, or `cache`. An intentionally online row remains unobserved until an
exact separately authorized attempt. A no-fetch branch needs negative network
observation or a complete supported static proof under bound state. Blocking
network and then accepting an unrelated failure is not equivalent behavior.

## 9. Required evidence routes and ownership

Each Lake edge keeps one M2 evidence state from the parent contract:

- `declared-static` for exact configuration/manifest syntax only;
- `resolved-static` for a complete supported resolver under bound inputs;
- `configured` for exact evaluated workspace/target/facet/setup bytes;
- `observed-runtime` for a retained job/process/file/network observation;
- `conditional-not-taken` with a complete condition and alternate branch;
- `intentionally-online`, `provider-unavailable`, `declined`, or `unresolved`
  as defined by M2.

Configuration evaluation, workspace resolution, job execution, artifact
production, child-process execution, and behavioral outcome are separate
events. A configured `ExternLib`, `dynlib`, plugin, compiler argument, server
command, or executable path transfers to M2.5/M2.6 with its M2.4 origin. It
does not become a link/load/request/native-support observation.

One provider/profile/platform cannot close another. A default local build
cannot close release/sanitizer/Windows/macOS variants, and one cold-cache run
cannot close a warm/local/remote-cache conditional unless every alternative
is registered and dispositioned.

## 10. Required sealed schema

M2.4.1 and later results must add domain-separated rows without removing any
parent M2 field.

### Provider and workspace attempt

- parent M2.1-M2.3 pointers, provider/profile/platform/selection/case owners;
- source copy, executable/toolchain/dynamic identity, cwd/root/config paths,
  command/argv, environment, system configuration, resource/network/cache
  policy, pre/post inventories, process formula, evidence root, completion,
  and attempt seal; and
- observed process/job/effect counts plus zero outcome/pair/performance/parity
  fields.

### Configuration and workspace

- lexical/resolved root/config paths, candidates, selected language/reason,
  raw bytes/mode/SHA-256, imports/defaults/options, evaluated configuration
  identity, cache OLean/trace identity, config-time effects/residuals;
- generated config/template/translation rows and pre/post source identity;
- exact workspace package order, package index/name/scope/root/configuration,
  directories, environment augmentation, facet registry, and workspace seal;
  and
- every configuration warning/error and raw evidence pointer.

### Manifest, override, and package materialization

- raw/parsed manifest version and ordered entries, nested-manifest pointers,
  fixed-toolchain/packages-directory state, manifest identity and writes;
- ordered manifest/workspace/CLI override candidates, shadowing event and
  selected row;
- path/Git source, URL map, input/resolved revision, repository/tree/clean
  state, subdirectory, materialization command/effects, package content digest,
  package dependency adjacency and closure digest; and
- missing/outdated/corrupt/network/checkout/toolchain residuals and owner.

### Target, facet, job, and artifact

- raw target spec and order, parser branch, package/target/module/path/facet
  resolution events, defaults, expanded build specs, kind/buildable/formatter;
- evaluated custom-target/facet/script identity and unsupported/dynamic state;
- job key/kind/caption, dependency/predecessor order, cycle state, action,
  child boundary, terminal state, raw trace pointer, and job/list/graph seals;
- artifact logical role/path/format/platform, pre/post bytes/mode/mtime/SHA-256,
  producer, inputs, Lake trace/hash/cache mapping, cache route, and downstream
  owner; and
- query/setup text/JSON projection, exact result order, duplicate/empty rows,
  and projection seal.

### Case/provider projection and aggregate

- exact accepted M2.3 boundary edges and equivalence/residual class;
- workspace/package/target/job/artifact graph roots, state counts, downstream
  transfers, conditional branches, unresolved/declined rows and owners;
- aggregate union/intersection with variant ownership preserved; and
- zero native outcome, pair, performance, complete population/axis/gate, and
  parity credit unless separately earned.

## 11. Fail-closed control families

M2.4.1 must freeze exact synthetic inputs, expected rows, process accounting,
and limits for at least these independent families:

1. explicit `.lean`/`.toml` versus extensionless selection, including both
   files present and Lean-before-TOML precedence;
2. relative, absolute, symlinked, space-containing, missing, directory, and
   escaping workspace/config paths;
3. declarative TOML versus executable Lean configuration with controlled
   environment/file effects and unsupported dynamic behavior;
4. current source with valid, stale, cross-toolchain, corrupt, or mismatched
   cached configuration OLean;
5. absent manifest triggering update/materialization rather than empty closure;
6. current and supported-old manifests plus future-major, too-old, malformed,
   reordered, duplicate, and wrong-root rows;
7. manifest -> workspace override -> ordered CLI override precedence with all
   shadowed rows retained;
8. local path, local `file://` Git, pinned remote Git, URL-map override,
   revision/subdirectory, dirty checkout, changed remote, and missing package;
9. nested manifest/config success and failure plus fixed-toolchain
   update/restart boundaries;
10. explicit/default package, module, library, executable, external/input,
    custom, filesystem-path, and ambiguous target resolution;
11. default versus explicit facets, multiple-spec expansion, duplicate result,
    unbuildable/unknown facet, and package-order ambiguity;
12. a `query` that is already up to date versus one that builds, runs a custom
    job, restores cache state, or fails after producing a partial result;
13. `setup-file` internal/external/config-file/header-override projections,
    missing configuration exit 2, invalid configuration, and incomplete trace;
14. custom target/facet/script with complete supported semantics, observed
    effect, unsupported dynamic residual, and failure;
15. acyclic job diamond, shared job, failed dependency, legitimate optional
    fetch fallback, and bounded build-cycle rejection;
16. fresh/up-to-date/old/rehash/no-build states including trace/hash/mtime and
    filesystem-resolution perturbations;
17. local artifact-cache miss/hit/replay/restore/corrupt/missing-output mapping
    with independent SHA-256 checks;
18. remote cache disabled, configured-but-not-selected, mapping-only,
    on-demand fetch, failure/fallback, wrong scope/toolchain/platform, and
    post-completion mutation;
19. `.ltar`, package release archive, built-local, cached, and unpacked states
    without converting archive presence into constituent provenance;
20. equal Lake hash with differing evidence bytes, and equal bytes with
    different producer/input identity;
21. generated `init`/`new`/translated projects with exact pre/post trees,
    language/template/name differences, and overwrite rejection;
22. endpoint-as-data, unreachable online helper, proven no-fetch invalid
    remote, local Git fetch, expected network failure, and authorized online
    request as distinct states;
23. environment/system-config/cache/PATH/home/proxy/platform drift and use of
    one provider to close another;
24. imported module/artifact rows transferred to M2.2, compiler/link/dynlib/
    plugin/executable rows to M2.5, and server/request rows to M2.6 without
    downstream credit;
25. truncated/partial/timeout/cancelled/orphaned process or job evidence,
    retry, incomplete post-tree, existing evidence root, and post-completion
    mutation; and
26. any unaccepted M2.1-M2.3 parent, guessed case transfer, nonzero native/
    pair/performance/parity field, or terminal promotion.

Every semantic mutation reseals the row, containing lists, graph, case
projection, aggregate, and top-level authority so the intended invariant—not a
stale digest—causes rejection.

## 12. Source-first sequence and process gate

1. **M2.4.0 plan:** this document freezes target semantics and the current
   read-only research floor. It creates no authority and runs no Lake process.
2. **M2.4.1 input/static authority:** only after accepted M2.1, M2.2, and M2.3
   results, bind the exact transferred case/provider boundaries, workspace and
   support bytes, configuration/manifest/override/cache pre-state, synthetic
   controls, supported static grammar, residual/equivalence classes, exact
   process formula, limits, evidence root, and authorization digest. All
   observed and credit fields remain zero.
3. **M2.4.2 implementation:** implement offline authority validation,
   workspace/config/manifest/package/target/facet/job/cache normalization,
   process/store capture, trace joins, post-tree validation, and semantic
   mutation tests. Commit and push before rendering authorization.
4. **M2.4.3 attempt:** only an exact later user authorization may run the
   frozen Lake/configuration/build/query/setup/network program. Validate its
   immutable completion-last evidence before a separate offline promotion.

Read-only-sounding Lake commands remain external build processes. The exact
process count cannot be known until accepted M2.3 transfers and M2.4.1 static
analysis determine workspace states, command equivalence classes, controls,
and dynamic/network residuals. No phrase such as “one process per case,” “one
query per target,” or “reuse the official build” may hide those inputs.

Stop before any process if local/tracking/remote refs differ, an evidence root
exists, the source/pre-state is dirty or ambiguous, user/system cache state is
not isolated, any executable/configuration/dependency/endpoint identity is
unbound, network policy is incomplete, or an accepted parent is absent.

## 13. Plan acceptance and nonclaims

This preregistration is accepted only when:

1. pinned source identities, direct 52-case/70-root counts, three excluded
   test paths, and the 28 wrapper-directory candidate floor reproduce from the
   committed authorities plus a clean target checkout;
2. config-language selection, executable configuration, missing-manifest
   update, ordered overrides, materialization, target/facet resolution,
   query/setup build behavior, cache/network state, and downstream ownership
   are explicit;
3. M2.4 is registered in terminal parity evidence and live roadmap/status
   surfaces without changing any closure or credit counter;
4. complete-parity generation, semantic tests, prose checks, links, JSON,
   whitespace, and relevant documentation gates pass; and
5. M2.1-M2.4 evidence remains absent, no M2.4 process has run, and every M2
   observation/native/pair/performance/parity field plus all terminal counters
   remains zero.

This plan does not claim that any Lake configuration loaded, manifest parsed
or updated, package materialized, target/facet resolved, job ran, artifact was
built/cached/restored, endpoint was contacted or avoided, project/server setup
completed, or native behavior matched. It does not authorize M2.1, M2.2,
M2.3, or M2.4. Complete Lean parity still requires accepted M2.1, separately
bound and accepted M2.2-M2.7, M3 review, every U0-U9 population, every A0-A11
axis, and every G1-G10 gate at one published revision.

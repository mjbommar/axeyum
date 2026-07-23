# Lean U2 TL0.6.4 M1 plan — pinned-content surface refinement

Status: **preregistered; no M1 scanner, authority, source signal, refined case,
native outcome, pair, or parity credit exists**

Date: 2026-07-23

Target: Lean `v4.30.0` at
`d024af099ca4bf2c86f649261ebf59565dc8c622`.

Parents:
[accepted M0 result](lean-u2-native-surface-classification-tl0.6.4-m0-result-2026-07-23.md),
[M0 authority](lean-u2-native-surface-classification-v1.json),
[U2 registration authority](lean-u2-test-authority-2026-07-22.md), and
[complete-parity contract](lean4-complete-parity-contract-2026-07-22.md).

## 1. Decision boundary

M1 must inspect the content-bound U2 source universe, not infer language or
runtime requirements from family names. It will analyze every one of the 7,004
Git-tracked files bound by the U2 registration authority and project those
findings onto every one of the 3,723 registered cases. The projection must
distinguish:

- the exact primary and sidecar files;
- exact case-local support files for directory cases;
- official family runners and registration wrappers;
- exact per-case initialization, before, and after hooks when present; and
- the larger shared support scope, whose signals are inspected but cannot be
  promoted to an individual pile case without a case-local reachability edge.

M1 is a content census and conservative surface refinement. It does not resolve
Lean imports, prove reachability through generated artifacts, interpret shell
programs, run a compiler, decide native Axeyum support, or form a semantic pair.
Every refined row remains provisional until M2 exact dependency closure and M3
full-row review.

This is an evidence-contract step under accepted
[ADR-0345](../research/09-decisions/adr-0345-preregister-lean-system-interoperability.md).
It changes no public Lean or Axeyum semantic behavior and requires no new
semantic ADR.

## 2. Frozen inputs

The implementation must reject physical or semantic drift in these committed
parents before reading an upstream byte:

| Input | SHA-256 | Required validation |
|---|---|---|
| `docs/plan/lean-u2-test-authority-v1.json` | `d7446e7965bac100ac6b5c607cbb7c87b5b80063fc23b3ec998fff2736d5d18e` | U2 registration validator returns no failures |
| `scripts/gen-lean-u2-test-authority.py` | `2c173c2621c374179ee346aa8cc710a84e8c37792b2ead25d4e80f8144ad34ba` | loaded from frozen bytes |
| `docs/plan/lean-u2-native-surface-classification-v1.json` | `89b29bc6820d1d948d5cd4defdd28eb59ddb55a5924a3cf770c0b21282959959` | M0 validator returns no failures |
| `scripts/gen-lean-u2-native-surface-classification.py` | `4827fc4ed27e729b36f2c0451059e4a4c7e4186ac8650eb54e8e98b1d740ccf6` | loaded from frozen bytes |

The parents bind the target commit, 7,004-file content-list digest
`f2c8b9c9276ac85dfef7d8e4fc32abe2350a3ae9e659a9a5795cba7f0390631f`,
3,723-case digest
`37050cfb25f0ecfa2256ccb9516124092fc611af5d7be94cce1e9e0745745cd3`,
M0 case-row digest
`f0c4d2cded9c0fb7a681438d6fe0e7b696e118cdafc5a2281bd13af51d9d1cdd`,
and the ten-surface registry.

Reproduction requires an explicit `--source-root` whose Git `HEAD` equals the
target commit. Every tracked path must have the exact mode, blob identity, byte
length, and SHA-256 from the parent content manifest. Untracked files, Git LFS
placeholders, submodules, path escapes, unsupported modes, unreadable bytes, or
missing/extra selected files fail closed. The ordinary committed `--check`
path must remain offline and validate the sealed derived authority without an
external checkout.

## 3. File population and role projection

The scanner must visit all 7,004 manifest rows in parent order, including
4,095 `.lean`, 1,488 `.expected`, 539 `.toml`, 239 `.sh`, 200 `.txt`, 170
`.json`, and every less common extension or extensionless file. Unknown,
binary, or deliberately ignored media still receive an inspected file record;
they may not disappear from the denominator merely because no signal decoder
applies.

Each file receives exactly one media class and zero or more nonexclusive roles:

- `primary` or `sidecar`, derived only from parent case rows;
- `case-local-support`, for a directory case's exact support subtree;
- `family-runner` or `registration-wrapper`, derived from the normalized
  registration command plus pinned runner resolution;
- `case-hook`, limited to exact `<case>.init.sh`, `<case>.before.sh`, and
  `<case>.after.sh` conventions recognized by the pinned runner;
- `shared-support`, for other files in a pile case's over-approximating support
  scope; or
- `unreferenced-content`, when bound by the global manifest but by no case
  projection.

Role derivation is case indexed. A file can serve multiple cases and roles, but
the global file is scanned once and each occurrence is reconstructed from exact
ordered references. Directory boundaries use normalized POSIX paths and reject
`..`, absolute paths, ambiguous normalization, and prefix-only matches.

Shared-support findings are reported as a scope census. They cannot add a
required surface to an individual pile case. Case-local files, exact hooks, and
exact harness files may refine a case, but every promotion retains the complete
file/signal evidence path.

## 4. Frozen signal registry

The implementation commit must freeze the signal catalog before publishing
derived counts. Each signal has:

- stable ID and version;
- applicable media classes;
- lexical or structured matcher definition;
- required token/config/command shape;
- evidence role policy;
- mapped native surface or `candidate-only` disposition;
- confidence class (`exact-token`, `structured-field`, `exact-command`, or
  `candidate`); and
- positive, comment/string, near-identifier, malformed, and omission controls.

At minimum the catalog covers these dimensions without claiming exhaustive
Lean semantics:

| Dimension | Required conservative evidence examples | Surface effect |
|---|---|---|
| source/parser/macro | active Lean tokens for `syntax`, `macro`, `macro_rules`, parser/elaborator declarations, quotations, and scoped syntax | `parser-macro`, sometimes `elaborator` |
| declarations/elaboration | active declaration/command tokens including theorem/def/opaque/axiom/structure/class/inductive, equations, mutual blocks, termination clauses, deriving, instances, and commands | `elaborator` |
| tactic/meta | active tactic blocks/commands and explicit `Lean.Meta`, `Lean.Elab.Tactic`, tactic elaborator, macro tactic, or metaprogram APIs | `tactic-meta` |
| modules/projects | active `import`/`prelude`, Lake/TOML structured fields, project manifests, package/facet/build/cache commands | `modules-lake` candidate or direct case-local evidence |
| editor/RPC | structured server request methods, LSP/RPC payload fields, server harness commands, cancellation/edit/version operations | `editor-rpc` |
| compiler/runtime | `#eval`/`#reduce`/`run_tac`, executable/interpreter/compiler commands, code-generation configuration, foreign source builds, effects/files/process output | `compiler-runtime` |
| FFI/native libraries | active Lean `extern`/`@[extern]`/`@[implemented_by]`, C-family ABI declarations, native linker/library flags, plugin/shared-library commands | `ffi` plus `compiler-runtime` |
| adversarial | expected-failure family plus explicit malformed/resource/crash/stale/cancellation controls | `adversarial` with component surface |

Names and filenames alone are never positive semantic evidence. Plain substring
search is insufficient. The Lean scanner must at least distinguish active code
from nested block comments, line comments, ordinary strings, character-like
syntax, quoted syntax, and identifiers so that `syntax` does not match
`mySyntax` or a comment. Structured JSON/TOML must parse successfully before a
field signal is exact. Shell/Python/C-family scanning must distinguish comments
and quoted data from command or declaration evidence to the extent claimed;
ambiguous constructs stay `candidate` and non-promoting.

Absence of a recognized signal proves only `no-signal-observed-v1`. It never
proves absence of a construct, dependency, FFI edge, effect, or native surface.

## 5. Exact evidence representation

Every positive or candidate hit records:

- file path, parent file SHA-256, media class, and file roles;
- signal ID/version and confidence/disposition;
- zero-based byte start/end and one-based line/column;
- exact matched-byte length and SHA-256;
- a bounded normalized context digest, not an unbounded source quotation;
- matcher route and, for structured media, the canonical field path; and
- the surface effect or explicit `non-promoting` reason.

Byte intervals must be ordered, in range, nonoverlapping for a single matcher
route unless the registry explicitly permits nesting, and reproducible from the
pinned checkout. UTF-8 decoding errors do not permit lossy replacement; they
route the file to binary/unsupported-media accounting.

The committed authority stores enough metadata and seals to validate itself
offline. Optional reproduction with `--source-root` must rederive identical
file rows, evidence intervals, case projections, aggregates, and top-level
seals byte for byte.

## 6. Case refinement and non-crediting state

Each of the 3,723 M1 case rows retains the complete M0 row identity and adds:

1. exact ordered primary, sidecar, runner, wrapper, hook, case-local, and
   shared-scope file references;
2. per-role content-closure digests and completeness counts;
3. promoted exact signals and separately listed candidate/non-promoting
   signals;
4. `m0_direct_surfaces`, `content_observed_surfaces`, and their conservative
   ordered union;
5. an evidence path from each added surface to one or more exact signal hits;
6. negative accounting for applicable signal families with no observed hit;
7. `classification_state = content-census-provisional` and
   `content_refinement = complete-census`; and
8. unchanged `module_dependency_closure = not-run`,
   `native_outcome = not-run`, and zero execution/pairing/parity credit.

The conservative union may add a surface; M1 may not remove an M0 floor.
Candidate-only or shared-support-only evidence cannot add a case surface. Exact
FFI evidence may add `ffi`, whose registry closure adds `compiler-runtime`,
`elaborator`, `parser-macro`, and `kernel-import`; the closure implementation
must reuse the frozen M0 DAG rather than duplicate it.

M1 remains incomplete for TL0.6.4 even when all content rows validate. M2 must
decide exact reachability and dependency closure; M3 may confirm, add, or remove
only a content-derived provisional surface with an explicit reviewed reason.

## 7. Review controls and mutation teeth

The source-first implementation must include a frozen control corpus selected
before aggregate counts are inspected. It includes at least one pinned positive
and one confounder for every signal family and media decoder, with expected
byte intervals. Required false-positive controls include nested Lean comments,
line comments, strings containing keywords, near identifiers, quoted syntax,
JSON string values that resemble field names, shell comments/arguments that
resemble commands, and C comments/string literals that resemble ABI symbols.

Required false-negative controls include multiline tokens/configuration,
escaped/quoted forms explicitly supported by the matcher, runner hooks, exact
directory-local support, active FFI/linker declarations, server request fields,
and one file with no recognized signal. Unsupported dynamic construction must
produce an explicit candidate/residual rather than a false exact hit.

Focused tests must reject at least:

- drift in either parent file, validator source, target commit, content/case
  digest, M0 surface registry, DAG, or case rows;
- missing, extra, duplicated, reordered, unreadable, wrong-mode, wrong-blob,
  wrong-byte-count, or wrong-hash source files;
- incomplete 7,004-file or 3,723-case coverage;
- path traversal, ambiguous scope prefixing, wrong role projection, missed
  runner/hook, or a shared-support signal promoted to one pile case;
- unknown/duplicate/reordered signal definitions or changed mapping/policy;
- a comment/string/near-identifier false positive or registered positive
  false negative;
- an out-of-range, wrong-location, wrong-digest, duplicate, or misordered hit;
- a content-observed surface without an exact evidence path, removal of an M0
  floor, or a wrong transitive closure;
- any claim of exact import/dependency closure, native support/decline,
  execution, pairing, performance, U2 completion, axis/gate completion, or
  parity credit; and
- aggregate, per-file, per-case, ordered-list, or top-level seal drift and
  stale generated JSON/Markdown.

Tests that target inner semantics must recompute enclosing seals so rejection
comes from the intended invariant rather than the first checksum.

## 8. Planned artifacts and gates

The implementation checkpoint will add:

- `scripts/gen-lean-u2-native-surface-content.py`;
- `scripts/tests/test_lean_u2_native_surface_content.py`;
- `docs/plan/lean-u2-native-surface-content-v1.json`;
- `docs/plan/generated/lean-u2-native-surface-content.json`; and
- `docs/plan/generated/lean-u2-native-surface-content.md`.

The canonical authority contains the signal registry, all 7,004 file rows,
every evidence hit, all 3,723 case projections, exact residuals/claims, and
domain-separated SHA-256 seals over canonical JSON. Generated summaries are
views, not alternate authorities.

Acceptance requires:

1. this plan committed and pushed alone before scanner implementation;
2. exact optional reproduction from the pinned checkout plus offline committed
   validation;
3. complete file/case coverage and all control/mutation tests;
4. generator regeneration/`--check`, M0 and complete-parity tests, parity-docs,
   link, Python/shell, and whitespace gates;
5. CI and local check integration; and
6. a separately committed result updating the contract, roadmap,
   implementation plan, plan index, `PLAN.md`, `STATUS.md`, and project state
   without promoting TL0.6.4 or any terminal counter.

If an unrelated frozen historical authority blocks the aggregate parity suite,
the result must name its exact failure and still run every task-owned gate. M1
must not rebind unrelated historical evidence merely to make the suite green.

## 9. Stop conditions and continuation

Stop without publication if the pinned checkout cannot reproduce all parent
file identities, a media decoder cannot preserve exact bytes, a registered
control is ambiguous, a case projection would require filename guessing, or a
surface promotion lacks exact content evidence.

M1 runs no Lean, Axeyum, CTest, Lake, server, compiler, runtime, provider, or
native test process. It grants no support, execution, pair, performance,
population, axis, gate, or parity credit.

After accepted M1:

- **M2** resolves exact Lean imports, generated artifacts, shell/project
  reachability, libraries/FFI, requests, and runtime dependencies using
  semantic/build evidence rather than lexical signals alone;
- **M3** reviews every full-population row and resolves all provisional fields;
  and
- **TL0.6.5** may form native pairs only after accepted TL0.6.4 and matching
  complete official/native execution evidence.

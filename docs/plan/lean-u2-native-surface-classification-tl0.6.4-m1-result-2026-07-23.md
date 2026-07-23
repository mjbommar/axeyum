# Lean U2 TL0.6.4 M1 result — complete tracked-content surface census

Status: **accepted bounded M1; TL0.6.4 remains PARTIAL**

Date: 2026-07-23

Target: Lean `v4.30.0` at
`d024af099ca4bf2c86f649261ebf59565dc8c622`.

Parents:
[M1 source-first plan](lean-u2-native-surface-classification-tl0.6.4-m1-plan-2026-07-23.md),
[generated-wrapper correction](lean-u2-native-surface-classification-tl0.6.4-m1-generated-wrapper-r1-plan-2026-07-23.md),
[lossless compaction plan](lean-u2-native-surface-classification-tl0.6.4-m1-authority-compaction-r2-plan-2026-07-23.md), and
[accepted M0 result](lean-u2-native-surface-classification-tl0.6.4-m0-result-2026-07-23.md).

## 1. Verdict

M1 is accepted for its source-only boundary. The canonical
[content authority](lean-u2-native-surface-content-v1.json) inspects all 7,004
Git-tracked files bound by the U2 registration authority and projects their
content evidence onto all 3,723 registered cases. It retains 90,909 exact or
candidate signal spans under 21 frozen signal definitions, exact file roles,
94 support-scope censuses, per-case evidence paths, and conservative surface
unions that cannot remove the M0 harness floor.

This is not exact dependency closure or native compatibility. All 3,723 rows
remain `content-census-provisional`; every module/generated/runtime/library/
FFI/request/project dependency closure and native outcome remains `not-run`.
There are zero native outcomes, pairs, performance rows, complete populations
or axes, satisfied terminal gates, and parity credit. The 24 provisional FFI
case surfaces are content signals that M2 must prove reachable; they are not
Axeyum FFI support or executed FFI cases.

## 2. Source-first and correction sequence

The work was committed and pushed in reviewable checkpoints:

1. `ed85cfd9` preregistered full tracked-content inspection before a scanner or
   count existed.
2. `dbd88bea` recorded that `tests/with_stage1_test_env.sh` is generated, not
   tracked, and assigned its exact materialization to M2.
3. `3a063e76` implemented and tested the frozen scanner before corpus counts
   were derived.
4. `d29cff6a` published the first complete authority after correcting one
   positive control that did not contain the promised exact token.
5. `108a2043` preregistered lossless authority compaction after GitHub warned
   that the 54.72 MB first representation exceeded its recommended threshold.
6. `6293cff3` replaced redundant per-hit seals with exact indices into sealed
   per-file hit lists, retaining all semantic fields and counts while reducing
   the current authority below 50,000,000 bytes. Shared history was not
   rewritten.
7. `88b13bc0` integrated M1 into local/CI parity gates and the terminal
   scoreboard with every terminal counter unchanged.

## 3. Complete tracked-source denominator

| Dimension | Retained count |
|---|---:|
| tracked files inspected | 7,004 |
| registered case projections | 3,723 |
| support-scope censuses | 94 |
| registered signal definitions | 21 |
| observed signal definitions | 19 |
| exact signal hits | 89,602 |
| candidate-only signal hits | 1,307 |
| all signal hits | 90,909 |
| cases with a content-observed provisional surface | 3,394 |
| cases with no content-observed provisional surface | 329 |
| cases with a generated-wrapper residual | 3,670 |

The media denominator is:

| Media | Files | Decoder state notes |
|---|---:|---|
| Lean | 4,092 | active-token scanner with nested-comment, string, identifier, and syntax-quotation controls |
| expected output | 1,488 | inspected; textual signals are candidate-only |
| TOML | 529 | exact fields require successful `tomllib` parsing |
| text | 444 | candidate-only command/RPC signals |
| shell | 237 | comment/string-aware candidate scanner |
| JSON | 170 | exact fields require successful JSON parsing |
| Python | 19 | comment/string-aware candidate scanner |
| binary | 10 | inspected with no decoder |
| C family | 9 | comment/string-aware exact ABI token scanner |
| symlink | 6 | link bytes and identities inspected; target reachability remains M2 |

Across all media, 6,694 files decoded, 16 binary/symlink rows were inspected
without a decoder, and 294 structured-media rows were recorded as
`malformed-structured`. That state means the strict JSON/TOML decoder did not
admit the file; it is not silently treated as “no dependency” and remains
visible for M2/M3 review.

## 4. Exact signal and role accounting

The largest signal families are 65,469 declaration tokens, 14,039 tactic-block
tokens, 4,622 evaluation commands, 1,544 import commands, 1,314 recursion
controls, and 1,085 syntax quotations. The census also retains 573 syntax/
macro declarations, 332 meta-API references, 187 elaborator extensions, 78
server API references, 51 compiler API references, 46 Lean FFI declarations,
10 C-family ABI occurrences, two structured RPC method fields, one native-link
TOML field, and every lower-count signal in the generated summary.

File roles are nonexclusive and exact: 3,723 primaries, 1,591 sidecars, 33
case hooks, 1,331 case-local support files, 93 family runners, three generated-
wrapper templates, and 7,002 shared-support files. Shared-support and
candidate-only findings cannot promote an individual pile case. The generated
wrapper is inventoried for 3,670 cases but cannot promote any M1 surface.

## 5. Provisional surface projection

Direct and transitive counts after conservative M0 union are:

| Native surface | Direct cases | Closure cases |
|---|---:|---:|
| `kernel-import` | 871 | 3,717 |
| `parser-macro` | 439 | 3,717 |
| `elaborator` | 3,463 | 3,717 |
| `tactic-meta` | 1,678 | 1,678 |
| `modules-lake` | 81 | 223 |
| `editor-rpc` | 147 | 147 |
| `compiler-runtime` | 841 | 860 |
| `ffi` | 24 | 24 |
| `toolchain-cli` | 6 | 6 |
| `adversarial` | 316 | 316 |

These are conservative provisional requirements, not implemented capability
counts. M1 never removes an M0 floor. M2 may add dependencies and must decide
reachability; M3 may alter a content-derived provisional surface only with a
retained reviewed reason.

## 6. Retained artifact identities

| Artifact | Bytes | SHA-256 |
|---|---:|---|
| canonical authority | 49,295,677 | `c83d10ce0f0619d4327dbbd7544bd584360cb080d35778ca7798a5f7da17560f` |
| generated JSON | 4,103 | `69ff3dee7411d7460d75bc3aa9fa2b6cbfa2e331b6c3d6336b20aa6737cb910e` |
| generated Markdown | 2,613 | `257f7a4903f213afd0a66eea99eed850731f0d978198e8102e6dbe503b2760b0` |
| generator | — | `107d699e3ab372ee78e686affcb7cbd940d6ff4ae3446dc29f90d1cd6927fb05` |
| focused tests | — | `8acec41e70a820c2bd5b713673fc98f6019cd675885e8f2169b24ad265472da4` |

Canonical logical seals:

- record: `d10f350d2c01d116538c9b52dcef71f38c473c81a36b3b41f75da4f39b889887`;
- files: `c52e4c465adbbbcd56577647be14c01bd3364779240661c0dbcfa138a17de13c`;
- scopes: `bd0c56bdd5f11c087f21aa6ba00c2f57b1f4b804f7e1c5954bd4a1a04fd9fdaf`;
- cases: `40190bb4aa7ea1160d5789ff4a98bc81716a51d6ea72f36839e0a43a3268b415`;
  and
- signal registry:
  `3a4d0a8785440453b1b4e2eb586afa2d8b6ebf01c78b8bbce27a4242bdae9a80`.

## 7. Validation and bounded failure

Accepted task-owned gates include:

- 15 focused scanner/authority/mutation tests;
- offline authority and generated-report validation;
- byte-for-byte authority reproduction from the exact pinned checkout;
- nine complete-parity registry tests;
- complete-parity regeneration with 0/10 populations, 0/12 axes, zero pairs,
  zero satisfied gates, and `terminal_ready=false`;
- Python compilation, shell syntax, whitespace, parity-document, and link
  checks.

The repository-wide `just parity-docs` run reaches and passes the M0 gate, then
fails in the older TL0.7.4 execution-acceptance test because the live
`scripts/install-pinned-lean.sh` hash is
`8a48e25ee2d2fb6d364dcbe0505b8a2fd660237e18e536d52117dc947d4c71ee`
while that historical authority pins
`75acb49a48e18b43523257ac22bc82889d614a6678c1cc3a457b3a150e1c7f71`.
M1 did not modify either file and did not rebind historical evidence to hide
the unrelated drift.

The subsequent source-first
[TL0.7.4 R2 repair](lean-execution-acceptance-tl0.7.4-merge-drift-r2-result-2026-07-23.md)
now closes that gate defect without rewriting the historical authority or any
downstream U2 evidence. It separates historical result inputs from the current
compatible installer and adds mutation coverage for both identities.

## 8. Nonclaims and required continuation

M1 does not claim an exact Lean import graph, configured wrapper bytes,
generated-artifact reachability, shell/project semantics, linked libraries,
runtime effects, FFI reachability, request reachability, native support or
decline, official-provider completion, semantic agreement, or performance.

TL0.6.4 remains PARTIAL until:

1. M2 derives and content-binds exact Lean imports, configured/generated
   artifacts, shell/project reachability, libraries/FFI, requests, and runtime
   dependencies without treating lexical signals as closure;
2. M3 reviews all 3,723 rows, resolves every provisional/candidate/malformed/
   generated residual, and publishes stable owners and decline routes; and
3. the accepted full authority still preserves zero silent official-Lean
   delegation and no credit below a case's required native surface.

TL0.6.5 may form matched native rows only after that accepted TL0.6.4 boundary
and matching complete official/native execution evidence.

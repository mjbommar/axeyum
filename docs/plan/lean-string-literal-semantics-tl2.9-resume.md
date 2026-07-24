# Resume handoff — Lean TL2.9 String-literal semantics

Status: **paused after the pushed P0 source/design checkpoint; no semantic code
has been written**

Paused: 2026-07-23

Owner lane: Lean complete-parity

Branch: `agent/lean/string-literals-tl2-9`

Worktree: `/home/mjbommar/projects/personal/axeyum-lean-string-r1`

P0 commit:
`41efefb56d3ce841f30396e525ec130d34885408`

Decision:
[proposed ADR-0366](../research/09-decisions/adr-0366-preregister-lean-string-literal-semantics.md)

Execution plan:
[TL2.9 P0--M5 plan](lean-string-literal-semantics-tl2.9-plan-2026-07-23.md)

This file is the authoritative restart point. Read it after
[`multi-agent-operations.md`](../contributor-guide/multi-agent-operations.md)
and [`PLAN.md`](../../PLAN.md); do not reconstruct the state from changelog
fragments.

## 1. Exact pause state

P0 is complete and pushed. It adds only research and documentation:

- source-backed proposed ADR-0366;
- the P0--M5 execution/mutation/resource/commit plan;
- complete-parity contract/roadmap and implementation-ledger links;
- research-question and ADR-index entries;
- generated complete-parity current-source hashes; and
- live PLAN/STATUS/plan-index links.

No file under `crates/`, `scripts/`, fixtures, or evidence roots changed. No
kernel typing/reduction, importer, identity, renderer, test, or generated seam
implementation exists on this branch.

No Lean binary, lean4export, solver, official String closure, M2.1 native
dependency execution, or official differential was invoked. The only network
research used read-only `gh api` calls against exact pinned GitHub commits.

The historical String export remains unretained and unrerun. Its frozen
identity is:

| Property | Value |
|---|---|
| Source root | `importStringLiteral` in `docs/plan/fixtures/lean4export-v4.30-blocker-census.lean` |
| Bytes / records | 570,807 / 10,339 |
| Names / nonzero levels / expressions / declarations | 1,781 / 24 / 8,243 / 290 |
| SHA-256 | `2404a6ca64999088ee9e4aa76f3426e77fda8eed5c63f5d8ad593c6b08ae0ab4` |
| Current first product blocker | unknown; the historical projection decline is obsolete |

Do not claim reproduction of those bytes from the committed source/hash alone.

## 2. Git and integration state

The branch was created from quotient result commit
`099ced1144954c1b92547eec45baf27c35934fa2`. During P0, that commit landed on
`main` through merge commit `6bfba9d82282511ce51ff3fb90f1cec6719f2877`.
Therefore the prerequisite is integrated; a future owner should still fetch
and preview the current merge rather than assuming no later drift.

At the P0 checkpoint:

- local branch and `origin/agent/lean/string-literals-tl2-9` both pointed to
  `41efefb56d3ce841f30396e525ec130d34885408`;
- the worktree was clean after push;
- ADR-0366 was the next unused number on then-current `origin/main`; and
- the branch contained the required co-author trailer.

The pause handoff is committed after P0 on the same branch. On resume, use the
containing branch tip as the authoritative pause commit and verify local,
tracking, and `git ls-remote` identities before editing.

## 3. Source facts already established

Pinned Lean:
`leanprover/lean4@d024af099ca4bf2c86f649261ebf59565dc8c622`
(`v4.30.0`).

Pinned lean4export:
`leanprover/lean4export@a3e35a584f59b390667db7269cd37fca8575e4bf`
(format 3.1).

The exact source contracts are:

1. `Literal.type` maps `.strVal` to `Const String`.
2. `string_lit_to_constructor` UTF-8-decodes the payload to Unicode scalar
   values, builds `List Char` in original scalar order using
   `List.nil.{0}`/`List.cons.{0}`, applies `Char.ofNat` to Nat literals, and
   wraps the list with `String.ofList`.
3. A bare String literal remains WHNF.
4. Definitional equality tries the conversion symmetrically only against an
   immediate `String.ofList` application.
5. Projection reduction converts and WHNFs a String literal before ordinary
   constructor-field selection.
6. Recursor reduction converts and WHNFs a String literal major before ordinary
   checked recursor-rule selection.
7. lean4export emits `{"strVal": s}` and forces dependencies for
   `Char.ofNat` and `String.ofList`.
8. Rust `String::chars()` is the correct scalar iterator. Iterating bytes is
   wrong for every multi-byte code point. Composed and decomposed Unicode
   sequences remain distinct.

The pinned Prelude names are `Char`, `Char.mk`, `Char.ofNat`, `List`,
`List.nil`, `List.cons`, `String`, `String.ofByteArray`, and `String.ofList`.
The old implementation-ledger wording using `String.mk` was corrected.

## 4. Current code seam

Inspect these locations before M1; line numbers will drift:

- `crates/axeyum-lean-kernel/src/tc.rs`
  - `KernelError::UnsupportedLit` and `NatLiteralBootstrapMismatch`;
  - `whnf_no_unfolding_uncached`;
  - `reduce_projection`;
  - `def_eq_quick`, `lazy_delta_step`, and `def_eq_core_uncached`;
  - `NatLiteralBootstrap`, `nat_literal_bootstrap`, and
    `nat_literal_to_constructor`;
  - `infer_core`, whose `Lit::Str` arm currently returns `UnsupportedLit`.
- `crates/axeyum-lean-kernel/src/inductive.rs`
  - `reduce_rec`, which currently converts only Nat literal majors.
- `crates/axeyum-lean-import/src/lib.rs`
  - expression import, where `strVal` currently returns
    `Unsupported(literal-string-typing)`.
- `crates/axeyum-lean-import/src/identity.rs`
  - identity-v1 already hashes `Lit::Str` under tag 10 using raw UTF-8 bytes;
    preserve this byte-for-byte.
- `crates/axeyum-lean-kernel/src/lean_pp.rs`
  - rendering already emits string literals; no P0 renderer change is needed.
- `crates/axeyum-lean-kernel/src/string_prelude.rs`
  - this is a finite solver-proof encoding and must not satisfy or replace the
    official Lean core bootstrap.

## 5. Important unresolved implementation question

Port the pinned defeq control flow carefully. Axeyum's current
`lazy_delta_step` returns delta-exhausted expressions, while official Lean
tries String expansion late in `is_def_eq_core`. If Axeyum eagerly unfolds the
other `String.ofList` definition before the special hook sees the immediate
application, a superficially placed helper may never fire—or an earlier helper
may widen behavior beyond the pinned control flow.

Before editing M2:

1. trace one direct literal-versus-`String.ofList` case through the current
   Rust defeq loop;
2. preserve the original candidate expression or adjust the sequencing in the
   smallest source-faithful way;
3. test transparent wrappers, wrong heads, aliases, extra application spine,
   and both orientations; and
4. do not use a broad literal-to-constructor normalization in ordinary WHNF.

This is not a reason to shrink the feature. It is the main semantic placement
risk that the next owner must resolve before claiming parity with the pinned
rule.

## 6. Resume sequence

1. Read the multi-agent guide, PLAN, this handoff, ADR-0366, and the execution
   plan in that order.
2. Run `git fetch origin --prune`; verify the branch tracking ref and current
   `origin/main`.
3. Confirm ADR-0366 has not been independently occupied or superseded. If it
   has, renumber only through a dedicated documentation commit before code.
4. Preview integration with `git merge-tree`; do not merge to `main`.
5. Re-run `git diff --check`, the terminal complete-parity test/generator, and
   links to establish a current baseline.
6. Start M1 only: add `StringLiteralBootstrapMismatch`, the checked bootstrap,
   literal inference, canonical scalar/list conversion, and native bootstrap/
   payload tests. Keep importer `strVal` fail-closed in M1.
7. Format only owned Rust files with `rustfmt --edition 2024`; use a distinct
   worktree target directory and pathspec commits.
8. Commit and push M1 before beginning M2.
9. Implement M2's defeq/projection/recursor hooks and repeated generated seam;
   commit/push separately.
10. Implement M3's importer/identity/synthetic publication evidence;
    commit/push separately.
11. Do not run M4/M5, Lean, or lean4export without explicit authorization.

## 7. Validation already completed

The P0 documentation run produced this evidence:

- `git diff --check`: pass;
- `just parity-docs`: every stage through the terminal generator passed, then
  the generator correctly rejected stale complete-parity derived files;
- `python3 scripts/gen-lean-complete-parity.py`: regenerated only current
  source identities/counters and retained the honest terminal line
  `complete_populations=0`, `complete_axes=0`, `paired_cells=0`,
  `gates_satisfied=0`, `terminal_ready=false`;
- `python3 -m unittest scripts.tests.test_lean_complete_parity`: 25 tests pass;
- `python3 scripts/gen-lean-complete-parity.py --check`: pass after generation;
- `just links`: pass; and
- implementation ledger denominator preserved at 139 rows (`DONE` 27,
  `PARTIAL` 8, `TODO` 104, `BLOCKED` 0). TL2.9 remains `TODO` while paused so
  the current ledger parser does not silently drop the row.

No `just check` claim was made. Current `main` has separately recorded
out-of-lane Rust formatting drift; this docs-only pause did not edit those
files.

## 8. Stop and authorization boundaries

- Do not regenerate or retrieve the official String stream through execution
  without explicit authorization.
- Do not run the pinned-Lean differential without explicit authorization.
- Do not retire `literal-string-typing` from compatibility evidence merely
  because native parsing exists; the exact official root must be measured.
- Do not accept ADR-0366 or mark TL2.9 DONE before M4/M5 close.
- Do not alter accepted evidence roots or historical hashes.
- Do not merge this topic branch to `main`; hand it to the integration owner
  only after the branch-specific green gate and clean merge preview.

## 9. Honest current claim

Axeyum has a pinned-source, mutation-complete implementation plan for Lean
String literals. It does not yet type, convert, import, project, or recurse over
String literals in the Rust kernel. The official large root is unretained and
unmeasured against the current product. Complete K1 and complete Lean parity
remain open.

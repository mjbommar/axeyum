# Lean TL2.9 String-literal semantics execution plan

Status: **PAUSED after pushed P0; implementation and authorized official
evidence open**

Date: 2026-07-23

Owner: Lean complete-parity lane

Decision:
[proposed ADR-0366](../research/09-decisions/adr-0366-preregister-lean-string-literal-semantics.md)

Resume:
[authoritative TL2.9 handoff](lean-string-literal-semantics-tl2.9-resume.md)

Parent contracts:
[Lean system implementation plan](lean-system-implementation-plan-2026-07-21.md),
[complete-parity contract](lean4-complete-parity-contract-2026-07-22.md),
[execution roadmap](lean4-complete-parity-roadmap-2026-07-22.md), and
[official blocker census](lean4export-official-blocker-census-2026-07-21.md)

## 1. Objective and bounded claim

Implement the pinned Lean 4.30 kernel semantics for raw String literals:
checked typing, exact Unicode-scalar `String.ofList` conversion, symmetric
definitional equality, projection reduction, recursor reduction, and
fail-closed format-3.1 ingestion.

The strongest offline result is:

> Axeyum implements the source-backed String-literal kernel rule for registered
> native and synthetic wire populations, with checked reserved bootstraps,
> Unicode-scalar mutation evidence, and deterministic seam coverage.

That does not establish the official String root, complete K1, `Init`/`Std` or
mathlib compatibility, frontend string elaboration, native runtime behavior,
or complete Lean parity. Those claims require the separately authorized large
closure and pinned-Lean differential.

This branch is stacked on quotient result commit
`099ced1144954c1b92547eec45baf27c35934fa2`; integration must land that one
commit before this branch or rebase this branch without dropping its result
surfaces.

## 2. Frozen authority and current baseline

### 2.1 Official implementation

| Authority | Exact identity | Required behavior |
|---|---|---|
| Lean | `leanprover/lean4@d024af099ca4bf2c86f649261ebf59565dc8c622` (`v4.30.0`) | `Literal.type` maps `.strVal` to `String` |
| Lean | same revision | `string_lit_to_constructor` UTF-8-decodes to Unicode scalars and builds `String.ofList (List Char)` |
| Lean | same revision | type checker performs String expansion only in defeq, projection, and recursor conversion hooks |
| lean4export | `leanprover/lean4export@a3e35a584f59b390667db7269cd37fca8575e4bf` | writes `{"strVal": s}` and forces `Char.ofNat` plus `String.ofList` dependency closures |

ADR-0366 records direct immutable source links. P0 used `gh api` only; it did
not run Lean, the exporter, Axeyum, or a solver.

### 2.2 Historical root identity

Producing source:
[`lean4export-v4.30-blocker-census.lean`](fixtures/lean4export-v4.30-blocker-census.lean)

Selected root: `importStringLiteral`

| Property | Frozen historical value |
|---|---|
| Bytes / records | 570,807 / 10,339 |
| Names / nonzero levels / expressions | 1,781 / 24 / 8,243 |
| Declaration records | 290 |
| SHA-256 | `2404a6ca64999088ee9e4aa76f3426e77fda8eed5c63f5d8ad593c6b08ae0ab4` |
| Retention | not retained; source, command, pins, counts, and hash only |
| Current first blocker | unknown; the historical line-184 projection decline is obsolete |

No P0 or offline test may claim reproduction of those bytes. A synthetic
fixture must be labeled synthetic and must not reuse the official hash or root
credit.

### 2.3 Product baseline

- `Lit::Str(String)` is already closed, interned, substituted/lifted as an
  atomic expression, UTF-8 hashed under identity-v1 tag 10, and rendered.
- `Kernel::infer` returns `UnsupportedLit` for every String literal.
- WHNF has no String expansion; projection and recursor reduction handle only
  constructor terms (plus Nat recursor conversion).
- format-3.1 `strVal` returns
  `Unsupported { code: "literal-string-typing" }` before construction.
- no retained official String stream is available for current-product replay.

## 3. Trusted semantic contract

### 3.1 Bootstrap authentication

Implement one private validator returning the names/types needed for expansion.
It checks the exact reserved surface frozen in ADR-0366: canonical Nat;
universe-polymorphic `List` with exact nil/cons structure; non-polymorphic
`Char` plus `Char.ofNat : Nat -> Char`; and non-polymorphic `String` plus
`String.ofList : List Char -> String`.

The first mismatch returns `StringLiteralBootstrapMismatch { name }`.
Validation is recomputed from checked declarations; no caller-set feature bit
or importer assertion can enable the primitive. The existing finite `Str`
prelude never satisfies this check.

### 3.2 Conversion algorithm

For `Lit::Str(payload)`:

1. validate the bootstrap;
2. iterate `payload.chars()` (Unicode scalar values, never bytes);
3. start from `List.nil.{0} Char`;
4. traverse the scalars in reverse, prepending
   `List.cons.{0} Char (Char.ofNat (Lit codepoint))`;
5. return `String.ofList list`.

Typing returns `Const String` without expansion. Ordinary WHNF leaves a bare
literal compact. Expansion occurs only in the three registered hooks.

### 3.3 Defeq hook

After the ordinary quick/reduction/congruence/eta paths fail, try both
orientations. Fire only when one side is a String literal and the other is an
immediate application whose function is the checked zero-level
`String.ofList` constant. Compare the WHNF of the expansion with the original
application through ordinary `def_eq_core`.

The helper must not recognize an alias, wrong universe arguments, additional
application spine, or same-spelled constant in a failed bootstrap.

### 3.4 Projection and recursor hooks

Projection reduction WHNFs its structure value. If the result is a String
literal, convert it and WHNF the conversion before the existing constructor
selection. Recursor reduction does the same after Nat-literal conversion's
mutually exclusive branch and before checked recursor-rule lookup.

The actual constructor and recursor metadata remain authoritative. Conversion
does not bypass projection inference, recursor arity, major-family typing, or
rule matching.

### 3.5 Wire, identity, and publication

The reader accepts a JSON string payload and constructs `Lit::Str(value)`.
`serde_json` owns JSON escape and Unicode validation; there is no lossy repair.
The kernel owns semantic bootstrap validation when a declaration uses the
expression. Completion-only publication remains unchanged.

Identity-v1's existing String tag and raw UTF-8 payload bytes are frozen. Add
tests, not a schema revision. Composed and decomposed strings therefore have
different identities, while alternative JSON escape spellings decoding to the
same scalar string have the same semantic expression identity.

## 4. Registered evidence populations

### 4.1 Bootstrap mutations

| ID | Mutation |
|---|---|
| B01 | empty environment |
| B02 | canonical Nat missing or malformed |
| B03 | `List` missing, wrong kind, universe arity, parameter/index count, recursion flag, or constructor order |
| B04 | `List.nil` wrong owner/index/field count/type/binder information |
| B05 | `List.cons` wrong owner/index/field count/type/binder information |
| B06 | `Char` missing, polymorphic, recursive, wrong sort, constructor name/count, or field count |
| B07 | `Char.ofNat` missing, wrong declaration kind/uparams/domain/codomain/binder information |
| B08 | `String` missing, polymorphic, recursive, wrong sort, constructor name/count, or field count |
| B09 | `String.ofList` missing, wrong declaration kind/uparams/domain/codomain/binder information |
| B10 | finite solver-proof `Str`/`Char` prelude substituted for Lean core names |

### 4.2 Payload and conversion rows

Required positives: empty; ASCII; embedded NUL/newline/quote/backslash; one
two-byte BMP scalar; one three-byte BMP scalar; one supplementary-plane
scalar; composed and decomposed accents; repeated and mixed scripts.

Required negatives: adjacent payload; reversed scalars; duplicated/dropped
scalar; UTF-8 bytes treated as characters; wrong `Char.ofNat`; wrong nil/cons;
wrong/reordered tail; wrong `String.ofList`; extra application argument; and
normalization of composed/decomposed input.

### 4.3 Reduction rows

- defeq in both orientations, direct and through transparent wrappers;
- projection from empty, single-scalar, multi-scalar, and non-ASCII literals;
- String recursor on those same majors;
- stuck, underapplied, wrong-head, wrong-owner, wrong-field, wrong-rule, and
  ill-typed controls; and
- proof that ordinary WHNF of the bare literal is unchanged.

### 4.4 Deterministic seam grammar

Generate at least 512 unique descriptors crossing:

- bootstrap state;
- payload class and scalar count;
- direct/wrapped expression;
- same/different/ofList comparison;
- no-reduction/projection/recursor operation; and
- accept/reject/inert expected outcome.

Run the grammar twice, require identical sorted rows and summary digest, and
exercise the public kernel path rather than a duplicate reference evaluator.
Every attempted false theorem admission must reject.

### 4.5 Synthetic wire controls

Before official execution is authorized, use explicitly synthetic records to
prove JSON decoding, dense indexing, report counts, late-error rollback, and
identity behavior. Do not label hand-written declarations as official Lean.

## 5. Milestones and stop conditions

### P0 — source authority and design preregistration

Deliver proposed ADR-0366, this plan, decision index/research question, and
live contract/roadmap/status links. Run documentation/parity checks. Commit and
push before semantic code.

Stop if ADR-0366 is occupied, the pinned source differs, branch ownership is
unclear, or the historical closure identity changes.

### M1 — checked typing and canonical conversion

Add the typed error, bootstrap validator, literal inference, conversion helper,
and exhaustive bootstrap/payload tests. Keep importer `strVal` fail-closed.

Stop if any same-name malformed bootstrap enables typing, scalar iteration is
byte-based, ordinary WHNF expands literals, or Nat regressions appear.

### M2 — defeq, projection, recursor, and generated seams

Wire the three exact hooks, add positive/false/stuck mutations, and close the
twice-identical generated public-path grammar. Do not add unrelated String or
Char primitives.

Stop on asymmetry, expansion under an unvalidated bootstrap, untyped
projection/recursor reduction, cache-dependent results, nondeterministic
digests, or any generated false admission.

### M3 — importer, identity, and synthetic publication evidence

Construct `Lit::Str` from valid JSON strings; add escape/scalar/malformed JSON,
late-failure, report, and identity tests; preserve every existing digest. Run
focused kernel/importer suites, path-scoped formatting, clippy, and rustdoc.

Stop if invalid Unicode is repaired, a failure publishes a kernel, an existing
identity changes, or removal of `literal-string-typing` would overstate the
unmeasured official root. Compatibility may record implementation separately
while keeping the official row open.

### M4 — authorized official closure retention and product measurement

Requires explicit authorization to execute pinned Lean/lean4export. Export the
exact source root twice under the registered resource lane, require byte
identity, reconcile the historical hash, retain the stream in the
content-addressed artifact path required by TL1.9, and inventory it with the
independent reader before running Axeyum.

Then import twice. If it declines, freeze the exact line/category/code/message,
zero publication, and next semantic owner. If it succeeds, require exact
declaration/axiom/identity counts and computation of `importStringLiteral`.
Either outcome advances the measured root; only complete success may close its
K1 row.

Stop on pin/source/command/hash drift, non-identical exports, missing resource
evidence, incomplete retention, Python/Rust inventory disagreement, or any
attempt to repair a newly observed blocker inside the measurement milestone.

### M5 — authorized differential and final acceptance

Requires explicit authorization to execute pinned Lean. Run the preregistered
positive/false controls over typing, scalar order, ofList equality, projection,
and recursor computation. Reconcile every result with Axeyum, run all lane and
repository gates available to the topic branch, update generated compatibility
and complete-parity surfaces, accept ADR-0366 only if every required gate is
closed, and push the containing commit.

If repository-wide `just check` fails only on pre-existing out-of-lane files,
record the exact boundary without editing them; the Lean-focused gates still
must be green. TL2.9 remains WIP until M4 and M5 close.

## 6. Validation commands

Offline commands, with a worktree-local target directory:

```sh
rustfmt --edition 2024 crates/axeyum-lean-kernel/src/tc.rs \
  crates/axeyum-lean-kernel/src/inductive.rs \
  crates/axeyum-lean-kernel/tests/string_literal_semantics.rs \
  crates/axeyum-lean-kernel/tests/string_literal_seam_grammar.rs \
  crates/axeyum-lean-import/src/lib.rs
cargo test -p axeyum-lean-kernel --test string_literal_semantics
cargo test -p axeyum-lean-kernel --test string_literal_seam_grammar
cargo test -p axeyum-lean-kernel
cargo test -p axeyum-lean-import
cargo clippy -p axeyum-lean-kernel -p axeyum-lean-import --all-targets --all-features -- -D warnings
RUSTDOCFLAGS="-D warnings" cargo doc -p axeyum-lean-kernel -p axeyum-lean-import --all-features --no-deps
just parity-docs
just foundational-resources
just links
git diff --check
```

Do not invoke a real Lean binary, lean4export, the official String closure, or
M4/M5 scripts without separate authorization.

## 7. Commit and integration protocol

1. Work only in the isolated `agent/lean/string-literals-tl2-9` worktree.
2. Commit P0 before M1; commit M1, M2, M3, and final evidence separately.
3. Stage explicit owned pathspecs and verify each commit with `git show --stat`.
4. Use `rustfmt --edition 2024` only on owned Rust files; never `cargo fmt`.
5. Include exactly:
   `Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>`.
6. Push each milestone and verify local/tracking/remote equality.
7. Do not merge to `main`; hand the ordered branch and clean merge-tree result
   to the integration owner.

## 8. Completion claim

TL2.9 is complete only when all ADR-0366 evidence gates are proved, the exact
official root's current first blocker is known, the authorized differential
agrees, generated status surfaces retain every broader gap, the containing
commit is pushed, and no required work remains. Until then the honest status is
WIP with zero complete-K1 or full-parity credit.

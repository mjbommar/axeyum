# 03 -- Architecture

## Overview

```
producers (Rust reports/examples, Python scripts)
        |  emit Doc-IR JSON (schema-versioned)
        v
  assembly (per-document manifest: blocks + checked refs + tag overrides)
        |  resolve refs against: fact ledger, kernel inventory, run records
        v                                   (FAIL-CLOSED at this step)
  emitters: markdown | latex | html   (pure functions of resolved IR)
```

## Document IR (Rust structs, serde; JSON as interchange so Python
## producers/consumers are first-class)

```rust
Document { schema_version, meta: DocMeta, blocks: Vec<Block> }
Block    { id: BlockId, tag: Verbosity, kind: BlockKind,
           provenance: Option<Provenance> }
Verbosity = Essential | Detail | Archive
BlockKind =
  | Prose(rich_text)                    // human narrative, inline math
  | Claim { label, statement: RichTextOrRef, status: EvidenceStatus,
            evidence: Vec<EvidenceRef> }
  | Statement(FormalRef)                // theorem/fact pulled by reference
  | Steps(Vec<Step>)                    // derivation: input, op, output
  | Table { caption, columns, rows, source: Provenance }
  | Certificate { kind: Sat|UnsatDrat|KernelAdmission|ReportRun,
                  summary, artifact_refs, replay: Command }
  | Figure(FigureSpec)                  // Polygon | Plot | DepGraph | Svg
  | Include { path, render_hint }       // archive-tier external artifact
Provenance { generator, command, inputs: Vec<(path, sha256)>,
             exit_status: i32, epoch: CommitEpoch }
EvidenceRef -> a run record (JSON file) carrying its own Provenance
FormalRef   -> fact id (artifacts/facts/F-*.json) | kernel NameId
               (resolved via the inventory examples, never source grep)
```

JSON Schema at `artifacts/ontology/docir.schema.json`, validated by a
Python gate (`scripts/validate-docir.py`) mirroring `validate-facts.py` --
same two-implementation discipline: Rust serde model + independent Python
schema validation.

## Checked references (the antiquotation layer)

Assembly resolves every `FormalRef`/`EvidenceRef` BEFORE emission:
- fact refs -> the ledger JSON (statement text, status axes);
- kernel refs -> `nat_theorem_inventory`-style canonical types;
- evidence refs -> run-record files written by producers (`--emit-run`).
Failure modes, all build errors: dangling ref; statement text inlined
where a ref is required; evidence exit_status != 0 under strict mode;
hash mismatch between a run record and the current artifact.

## Emitters

- **Markdown**: CommonMark; `Detail` -> `<details><summary>`; `Archive`
  -> link; badges as text + shields-style inline SVG (self-contained
  data: URIs); tables native; figures as checked-in SVG.
- **LaTeX**: a small package `axeyum.sty` (`\axclaim`, `\axstatement`,
  `\axtable`, `\axcert`, `\axbadge`); `Detail` -> configurable
  (inline | appendix | margin-linked); `Archive` -> `\href` to repo path
  at pinned commit; generated `.tex` fragments under `latex/generated/`
  (the NoH paper template already has that directory -- deliberate).
- **HTML**: single self-contained file; see 05.

Emitter law: emitters are TOTAL and DUMB -- all failure happens in
assembly. An emitter never inspects evidence; it renders resolved,
already-judged blocks. This keeps the trusted logic in one small place.

## Where code lives (crate and ADR plan)

Repo law (ADR-0001): crates only after a boundary is proven by use.
Plan: P0 builds inside a NEW top-level directory `render/` as a plain
cargo package NOT in the workspace members list (like a tool, not public
surface), plus `scripts/validate-docir.py`. Promotion to a workspace
crate `axeyum-render` happens via ADR after P0 exit criteria are met,
because at that point the boundary (Doc-IR schema = public evidence
format) is exercised by two producers and three emitters. A second ADR
covers the run-record format (it is an evidence artifact: semantics,
replay, checker route must be explicit per Hard Rules).

## Determinism and testing hooks

- No wall clock: `epoch` comes from the pinned commit or
  SOURCE_DATE_EPOCH.
- BTreeMap/sorted everywhere; goldens are byte-exact.
- Every emitter has golden-file tests; assembly has NEGATIVE tests
  (each fail-closed rule above = one test that must die if the guard is
  deleted -- the exactly-one-test-dies discipline).
- Cross-format property: the set of (claim label, status) pairs is
  identical across md/latex/html emissions of the same document.

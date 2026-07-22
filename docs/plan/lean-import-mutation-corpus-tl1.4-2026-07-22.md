# TL1.4 result — generated Lean import mutation corpus

Date: 2026-07-22

Status: complete

Decision: [ADR-0349](../research/09-decisions/adr-0349-generated-lean-import-mutation-corpus.md)

## Result

TL1.4 adds a deterministic 226-case adversarial corpus for the official
`lean4export` format-3.1 boundary. Every generated case has a unique stable ID,
expected outcome class, and exact ordered summary. Two complete generations and
executions are byte-identical in process; no case panics.

The corpus covers every planned family: truncation at every official record,
duplicate IDs, forward references, unknown fields, deep JSON, Unicode, integer
boundaries, cycles, versions, and record discriminants. It also distinguishes
an invalid record body from an unauthenticated but grammatically valid EOF
prefix.

## Exact population

The frozen summary is:

```text
LEAN_IMPORT_MUTATIONS|cases=226|json=67|kernel=1|malformed=90|published=3|published-unsealed=64|unsupported:format-version=1
```

The 226 cases comprise:

- 65 EOF prefixes before each official flat-fixture record;
- 65 one-byte body truncations, one for every official record;
- 65 extra top-level fields, one for every official record;
- four selected nested unknown fields;
- three duplicate-ID cases;
- six forward/self name, level, and expression references;
- one declaration self-cycle;
- two JSON-depth controls;
- four Unicode/numeral controls;
- five integer-width/type controls;
- four version/exporter metadata controls;
- two unknown/multiple-discriminant controls.

These totals are asserted in the test, not copied only into documentation.

## Stable outcome classes

The corpus classifies only public error variants and registered unsupported
codes:

- `json`: malformed JSON, excessive nesting, or invalid surrogate syntax;
- `malformed`: format shape, topology, ID, field, numeral, or integer errors;
- `kernel`: independently rejected declaration semantics;
- `unsupported:format-version`: pinned-format decline;
- `published`: deliberate bounded-nesting and Unicode positive controls;
- `published-unsealed`: valid complete-record prefixes without artifact
  identity.

Messages are not used as the stable oracle. This allows diagnostics to improve
without weakening the parser/admission class contract.

## Truncation result and upstream boundary

Removing the final `}` from each of the 65 official records produces 65 JSON
rejections. By contrast, the empty stream rejects but each of the 64 non-full
prefixes ending after a complete record publishes relative to its delivered
bytes. This follows the upstream grammar: metadata is followed by a sequence of
backward-referencing primitives/declarations, with no footer, expected count,
or root manifest.

Those prefixes are not credited as the full official fixture. They are labeled
`published-unsealed`; their declaration counts never exceed the full fixture,
and the exact full control still reports five declaration records and eight
admitted declarations. `CompletedImport` documentation now says explicitly
that completion is relative to delivered EOF. TL0.3, TL1.6, and TL1.9 own an
external digest/manifest, checkpoint completion, and content-addressed durable
artifact identity.

Primary format source:

- [`lean4export` NDJSON 3.1.0](https://github.com/leanprover/lean4export/blob/v4.30.0/format_ndjson.md)

## Other mutation evidence

- Raw `λ😀` and its JSON-escaped spelling independently admit the same checked
  declaration name.
- A lone surrogate rejects as JSON; Arabic-Indic digits reject as a Nat wire
  value because the format path requires ASCII decimal digits.
- Depth 16 metadata publishes; depth 256 rejects through serde's recursion
  guard without stack failure.
- Duplicate name, level, and expression IDs reject dense-order violations.
- Name/level/expression forward and self references reject before admission.
- A theorem value referring to its own not-yet-admitted constant reaches the
  independent kernel and rejects as a semantic cycle.
- Negative, floating, overflowing, maximum, and projection-width integers
  reject without narrowing or panic.
- Every official record rejects an added top-level field, and selected nested
  metadata/name/expression/declaration fields reject as well.

## Validation

At the TL1.4 checkpoint, the importer passed 23 integration cases across two
binaries plus its example target. The mutation binary's three tests cover corpus generation/
execution, Unicode equivalence, and explicit unsealed-prefix accounting.
Warning-denied Clippy/rustdoc, compile-fail doctest, compatibility/prototype,
parity-prose, foundational-resource, focused formatting, JSON, and link gates
pass under build concurrency capped at two.

## What this does not claim

- a bare upstream stream authenticates its producer-intended length;
- `published-unsealed` earns any exact fixture, dependency-root, or broad Lean
  compatibility credit;
- persistent checkpoint/resume or content-addressed storage is implemented;
- property-guided fuzzing replaces the deterministic corpus—TL1.5 still owns
  that additional layer;
- declaration content/dependency digests were not part of TL1.4; TL1.7 has
  since landed them;
- any new Lean wire construct or kernel semantic fragment is admitted.

## Next action

TL1.7 subsequently landed axiom/declaration/dependency identity. Resume the
numbered queue with the remaining official inductive fixture matrix; TL1.5
remains the property-fuzz layer over this frozen discriminant/path corpus.

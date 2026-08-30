# Library artifact and Lean compatibility roadmap

Status: accepted programme under ADR-0717
Date: 2026-08-30

## Outcome

Axeyum should interoperate at the artifacts that carry mathematical meaning
before it imitates the language that produced them.  The target is a narrow,
stable boundary:

```text
Lean/Mathlib elaborated declaration  <->  content-addressed core declaration
                                               |
                                     Axeyum checked proof term
                                               |
                                  pinned Lean kernel acceptance
```

Rust and Python remain the primary native programming surfaces.  They reduce
the urgency of general Lean input syntax, but do not replace declaration reuse,
dependent elaboration, Lean workflow, or independent proof acceptance.

## Current capability ledger

| Surface | Already present | Boundary that remains |
|---|---|---|
| Independent core checker | Names, universes, expressions, environments, reduction, definitional equality, checking, and selected inductive/recursor/projection/quotient slices in `axeyum-lean-kernel` | Complete pinned populations and assurance for unsupported Lean-core constructs |
| Declaration interchange | Fail-closed `lean4export` reader, explicit writer, identities, dependency selection, round trips, mutations, bounded real-Lean differential tests | Complete subject coverage, portable versioned packs, and universal root/dependency replay |
| Mathlib statement frontier | Pinned v4.30 source identity, proof-isolated statement extraction, selected Nat/Int catalog and survival atlas | Full selected declaration graph and systematic representability joins |
| Proof reconstruction | Solver, CAS, importer and producer routes converge on `Kernel::add_declaration` | Universal independent export/replay and one credit contract |
| Python/Rust API | Rust crates plus PyO3 surfaces for SMT, IR, solver, CAS, kernel, producers, knowledge and agent orchestration | Stable high-level theorem/discovery API and ergonomic receipts |
| Lean source | Rendered selected modules; no general input frontend | Parser, macro expansion, elaboration, coercions, metavariables, typeclasses, tactics |
| Lean workflow | External pinned-Lean probes | Thin in-Lean goal adapter; Lake/editor/package integration only if demanded |

The generated [`lean-compatibility.md`](generated/lean-compatibility.md) remains
the status authority.  Acceptance of emitted source is output compatibility,
not evidence of source compatibility.

## Phases and exits

### C0 — Freeze the artifact contract

Define one versioned record for a declaration root and its closure:

- Lean and Mathlib versions and source commits;
- canonical name, kind, universes, type, optional value, and content digests;
- separate direct type, value/proof, and transitive dependencies;
- trusted-declaration identities;
- normalization and renderer versions;
- source population identity and exact coverage counts.

**Exit:** two independent readers reproduce all identities on a bounded positive
pack; missing, duplicate, reordered, truncated, and value-exposed statement-only
mutations fail.  The validator fails on a missing expected root, not merely a
malformed row.

### C1 — Complete declaration and theorem graph extraction

Run a pinned Lean-side extractor on server5 against the released Mathlib
environment.  Store proof-free type graph data separately from proof/value
dependencies.  Produce sharded, content-addressed artifacts so 2–3 lanes never
write one graph file.

**Exit:** every declaration in the selected population has exactly one row;
edge endpoints resolve; module/declaration totals and seals reproduce; a
deleted edge, row, or shard makes the aggregate gate fail.  Producer processes
can read only the proof-isolated projection.

### C2 — Universal checked interchange for credited roots

For every headline theorem that is representable in the pinned Lean slice:

1. export the exact reachable Axeyum closure;
2. fresh-import or replay it through an independent path;
3. submit it to pinned Lean's kernel;
4. bind the result to the fact receipt.

**Exit:** the generated credit census reports expected, attempted, accepted,
declined-by-typed-reason, missing, and extra counts.  `missing=0` is mandatory;
declines do not silently inherit Lean-accepted credit.

### C3 — Thin Lean adapter

Build a small Lean command/tactic adapter that receives an already elaborated
goal plus environment identity, calls Axeyum as a sidecar/library, and returns a
proof/certificate that Lean itself checks.  It must not trust Axeyum's verdict
or add an axiom.

**Exit:** a preregistered representative goal pack covers success, unknown,
timeout, unsupported, malformed response, wrong goal, wrong environment, and
mutated proof.  All successes are accepted by Lean and every mutation rejects.

### C4 — Demand-gated elaboration features

Maintain a blocker census for declarations that cannot cross C0–C3.  Admit a
source/elaboration feature only when it is the smallest shared blocker for a
preregistered high-value population.  Likely high-value families include
structures/typeclasses, coercions, dependent records, finite collections, and
notation normalization; parser cosmetics without survival gain rank lower.

**Exit per feature:** before/after population survival, exact Lean differential
behavior, no enlarged trusted surface, and at least one downstream producer or
user workflow consuming the feature.

### C5 — Reconsider native source/workflow compatibility

Only after C3 has real use and C4 metrics show repeated adapter friction should
the project consider broader `.lean`, Lake, package, editor, compiler, or runtime
compatibility.  K2 source and K4 workflow remain separate claims.

## Parallel ownership

| Lane | Owns | Does not own |
|---|---|---|
| `artifact-extract` | Pinned external extraction, sharded raw graph, seals | Axeyum proof producers or fact status |
| `artifact-join` | Validators, graph joins, generated dashboards | Reading upstream proof values during production |
| `lean-adapter` | Goal protocol and pinned-Lean acceptance pack | Kernel admission policy or broad elaborator work |

Each lane writes a distinct status file and artifact subtree.  Aggregate files
have one generated writer under ADR-0652.

## Metrics

- declaration population expected / observed / sealed;
- type edges and proof edges, reported separately;
- credited roots independently replayed / declined / missing;
- declarations blocked by each Lean feature;
- thin-adapter successes, typed declines, and mutation rejection;
- new downstream facts or workflows unlocked per compatibility increment.

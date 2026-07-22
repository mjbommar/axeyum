# TL1.7 result: canonical Lean declaration and dependency identity

Date: 2026-07-22

Status: complete

Decision: [ADR-0350](../research/09-decisions/adr-0350-canonical-lean-declaration-identity.md)

## Outcome

Every successful format-3.1 import now publishes a versioned, canonically
ordered identity manifest inside `ImportReport`:

- `axiom_identities` binds each imported axiom's displayed UTF-8 name and
  `Kernel::render_lean(type)` to plain SHA-256. The type formula is exactly the
  accepted TL0.4 axiom-ledger formula.
- `declaration_identities` binds every independently admitted axiom,
  definition, theorem, opaque, inductive, constructor, and recursor to a
  domain-separated structural content SHA-256.
- each declaration also publishes its sorted direct dependencies, with every
  dependency name bound to that admitted declaration's content SHA-256, plus a
  digest of the complete ordered dependency binding.
- `identity_version` is
  `axeyum-lean-declaration-identity-v1`; changing the encoding requires a new
  version rather than silently drifting existing identities.

The manifest is built only after the complete stream checks inside TL1.3's
private staging kernel. Failed imports still publish no environment or digest
manifest.

## Canonical boundary

The structural Merkle encoding covers hierarchical names, universe levels,
every represented expression node, binder information, arbitrary-precision Nat
and String payloads, declaration variants, reducibility hints, inductive and
constructor metadata, and complete recursor rules. Scalars use fixed-width
big-endian encodings; byte strings and lists are length-prefixed; child arena
handles are replaced by their canonical 32-byte digest. Expression hashing is
iterative and memoized, so shared subterms are hashed once and deep expression
DAGs are not recursively expanded.

Neither wire/arena IDs, declaration record order, JSON spelling, Rust `Debug`
output, nor the readable Lean printer enters structural declaration identity.
The printer remains only the established TL0.4 axiom type projection. The
`sha2` dependency is confined to the untrusted importer crate; the independent
kernel remains dependency-free.

## Frozen flat-fixture evidence

The official flat fixture produces eight exact v1 declaration identities. The
five new identity tests freeze all eight full content/dependency digests. Three
representative rows are:

| Declaration | Kind | Content SHA-256 | Direct dependencies |
|---|---|---|---|
| `P` | axiom | `0bdd9ce84a603187f198c16bd42f43af439c2c352d8dcfeabdf13e6f5ef574b6` | none |
| `identity` | theorem | `29ad0b801ead6f7df353cc79e68939398c71b60af92a2631ca5b2a47f3f70dae` | `P` |
| `Two.rec` | recursor | `28f4d4fb59759afe6f189a24288f3197757aa14a367df2c895e86bfda474322f` | `Two`, `Two.left`, `Two.right` |

The axiom ledger-compatible identities for `P` are:

- name SHA-256:
  `5c62e091b8c0565f1bafad0dad5934276143ae2ccef7a5381e8ada5b1a8d26d2`;
- rendered-type SHA-256:
  `57d968860fabe1008d2c72342adec04b70f4bae48b7bcf6ebca915624100c353`.

## Mutation and invariance evidence

The focused TL1.7 binary proves:

1. repeated imports produce exactly equal axiom and declaration manifests;
2. moving an independent declaration record after another declaration leaves
   every identity unchanged;
3. changing the valid axiom `P : Prop` to `P : Type` changes the ledger type
   digest and `P` content digest;
4. the dependent theorem `identity` keeps the same content digest under that
   mutation, but its dependency digest and bound `P` content change;
5. replacing `chooseLeft := Two.left` with the equally typed `Two.right`
   changes its content/dependency identity while unrelated declarations remain
   byte-identical;
6. changing retained binder information changes structural content even though
   the readable printer omits that annotation;
7. all public digests are lowercase 64-hex and all rows/dependencies remain
   unique and canonically ordered.

The frozen inductive/constructor/recursor rows ensure generated kernel metadata
and recursor rules, rather than only exported JSON, participate in identity.

## Validation

- importer: 28 integration tests across three binaries plus the example target;
- compile-fail doctest: one external-forging rejection;
- warning-denied package Clippy and rustdoc: pass with two build jobs;
- package rustfmt and scoped `git diff --check`: pass;
- compatibility/prototype/ledger: 21 Python tests, 12-row compatibility check,
  and 65-row axiom-ledger check pass;
- parity prose: 35 rows, 680 comparisons, zero disagreements;
- foundational resources: 137 concepts and 174 packs validate with no generated
  drift;
- documentation links: pass.

The repository-wide `cargo fmt --all --check` is not credited: pre-existing
unrelated benchmark/CAS formatting drift remains outside this change. Every
TL1.7 Rust file passes package-scoped formatting. Repository-wide `cargo deny
check` is also not credited: the existing `axeyum-wasm` manifest lacks a
recognized license field and the existing benchmark/Rayon graph retains
`crossbeam-epoch 0.9.18` under RUSTSEC-2026-0204. TL1.7 reuses the already-
locked `sha2` package and introduces no new transitive package.

## What this does not claim

- v1 is not alpha-normalized semantic equivalence, proof irrelevance, source
  identity, or a transitive module/root digest;
- an accepted upstream EOF authenticates the producer-intended artifact;
- direct dependency rows implement modules, environment merging, cache
  invalidation, or content-addressed storage;
- the public reader API is stable before TL1.10;
- any new Lean construct, broad `Init`/`Std`/mathlib closure, or general Lean
  compatibility is admitted.

## Next action

Resume the numbered implementation queue by generating the remaining official
recursive-indexed, reflexive, mutual, nested, and well-founded fixture matrix.
Keep the direct-recursive positive control beside each decline. TL1.5 is now
dependency-ready for property fuzzing over the frozen TL1.4 paths; TL2.11 owns
strict positivity before semantic admission widens.

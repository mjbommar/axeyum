# ADR-0350: Publish canonical Lean declaration and dependency identities

Status: accepted

Date: 2026-07-22

## Context

TL1.7 must bind every admitted `lean4export` declaration to stable content and
dependency identities. It must also publish each imported axiom's name/type
identity in the same vocabulary as the accepted TL0.4 axiom ledger. Arena IDs,
wire record numbers, declaration admission order, Rust `Debug` output, and JSON
spelling are unsuitable: all can change while the checked declaration remains
the same. The existing Lean pretty-printer is useful for the ledger's reviewed
type projection, but it omits retained core structure such as binder info and
does not serialize inductive/constructor/recursor metadata completely.

One hash also cannot distinguish two different facts:

- the declaration's own checked structural content changed; and
- one of the declarations it names changed while its own term stayed the same.

That distinction is required by later dependency-closed prelude, module, cache,
and artifact work.

## Decision

**Publish a sorted identity manifest in every successful `ImportReport`. Keep
axiom ledger identity compatible with TL0.4, and compute declaration content
and direct-dependency identities from a separate complete canonical structural
Merkle encoding.**

### Axiom identity

For every admitted axiom, record:

- `name`: the kernel's exact displayed hierarchical name;
- `name_sha256`: SHA-256 of the UTF-8 bytes of `name`;
- `type_sha256`: SHA-256 of the UTF-8 bytes returned by
  `Kernel::render_lean(declaration.ty())`.

The type rule deliberately matches
`docs/plan/lean-axiom-ledger-v1.json`. It is a ledger comparison identity, not a
complete serialization of kernel structure. The declaration's structural
content digest supplies the stronger identity.

### Canonical structural content

Use SHA-256 with explicit ASCII domain/version tags. Every scalar is fixed
width and big-endian; every byte sequence and list is length-prefixed. Child
nodes enter their parent as their 32-byte canonical digest. Memoize by arena
handle only as a local performance optimization; handles are never hashed.

The canonical node vocabulary covers:

1. hierarchical name nodes: anonymous, string component, numeric component;
2. universe nodes: zero, successor, max, imax, parameter;
3. expression nodes: bound/free variable, sort, constant with ordered universe
   arguments, projection, application, lambda, pi, let, and Nat/String literal;
4. binder information and literal bytes;
5. every declaration variant, its canonical name, ordered universe parameters,
   type, optional value, reducibility hint, inductive/constructor metadata, and
   complete ordered recursor-rule metadata and right-hand sides.

The resulting `content_sha256` is independent of JSON key order, wire IDs,
arena IDs, and declaration admission order. It is intentionally sensitive to
otherwise unchecked presentation fields retained in the kernel, such as binder
names, because v1 claims exact checked-environment content identity rather than
alpha-normalized theorem identity. A later normalized identity must use a new
domain/version rather than silently changing v1.

### Direct dependencies

For each declaration, collect direct references from:

- its type and optional value;
- projection type names;
- inductive constructor-name metadata;
- a constructor's parent inductive;
- recursor constructor names and rule right-hand sides.

Remove self references, deduplicate by canonical name, and sort by canonical
name bytes. Every dependency row records the displayed name and that admitted
declaration's `content_sha256`. `dependency_sha256` hashes the ordered sequence
of canonical dependency-name digest plus dependency content digest under its
own domain. Thus a dependency's content mutation changes downstream dependency
identity even when the downstream declaration content is byte-identical.

All referenced declarations must be present in the completed private kernel.
An impossible missing dependency is an importer invariant failure and prevents
publication rather than emitting a partial manifest.

### Publication shape

`ImportReport` retains the existing `axioms: Vec<String>` compatibility field
until TL1.10, and adds:

- `axiom_identities: Vec<AxiomIdentity>`;
- `declaration_identities: Vec<DeclarationIdentity>`.

Both vectors sort by canonical structural name bytes, not admission order.
`DeclarationIdentity` includes the displayed name, stable declaration-kind
label, `content_sha256`, `dependency_sha256`, and its sorted dependency rows.
The report is constructed only after the complete stream has checked, inside
the TL1.3 private publication boundary.

## Exit gates

TL1.7 is complete only when:

1. repeated import yields exactly equal identity manifests;
2. reordering independent declaration records leaves the complete identity
   manifests unchanged;
3. a valid axiom type mutation changes its ledger type digest and structural
   content digest;
4. that dependency mutation leaves a dependent declaration's content digest
   unchanged but changes its dependency digest;
5. a valid definition-body mutation changes content identity without changing
   its type or unrelated declarations;
6. inductive, constructor, and recursor identity covers all generated metadata
   and rules, with no debug-string or arena-ID input;
7. all digest strings are lowercase 64-hex and all public rows are uniquely,
   canonically ordered;
8. importer, compatibility, resource, warning-denied Clippy/rustdoc, doctest,
   formatting, and link gates pass under the existing bounded job policy;
9. PLAN, STATUS, roadmaps, result documentation, and public API docs state the
   exact identity and non-claim boundaries.

## Alternatives

### Hash the original NDJSON record

Rejected. JSON key order, whitespace, wire IDs, metadata, and record placement
are transport details, not admitted declaration identity. It would also assign
generated constructor/recursor identity to exporter bytes rather than the
independently reconstructed kernel declarations.

### Hash `Debug` output or arena handles

Rejected. Neither is a stable public format, and handle allocation order is
exactly what the reordering gate must erase.

### Use `render_lean` for all declaration content

Rejected. It is intentionally a readable source projection, not a complete
kernel serialization; binder info and generated declaration metadata can be
lost. It remains only for TL0.4-compatible axiom type identity.

### Hash the transitive dependency closure recursively

Rejected for v1. Direct rows already bind dependency content and compose into a
closure, while inductive metadata can contain natural intra-group cycles. A
recursive closure hash would require a separate strongly-connected-component
and module-root contract owned by TL7.1-TL7.2.

## Consequences

- Imported axioms can be compared directly with the accepted 65-row TL0.4
  ledger while retaining a stronger structural declaration identity.
- Generated inductive declarations receive identities for what the independent
  kernel actually admitted, not merely what the exporter claimed.
- Later prelude, module, cache, and content-addressed artifact work can bind
  direct dependencies without relying on stream order.
- V1 is exact structural identity, not alpha-normalized semantic equivalence,
  source identity, proof irrelevance, producer-intended stream completion, or
  transitive module-root identity.

## Result

The accepted implementation publishes the version
`axeyum-lean-declaration-identity-v1`. Five focused tests freeze all eight flat-
fixture identities and prove repeated-import equality, independent declaration-
record reorder invariance, valid axiom-type propagation, valid definition-body
sensitivity, and binder-info coverage outside the readable printer. The full
importer gate passes 28 integration tests across three binaries. See the
[TL1.7 result](../../plan/lean-declaration-identity-tl1.7-2026-07-22.md).

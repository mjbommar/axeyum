# The library artifact contract (L1 phase C0)

This directory freezes the versioned record format that C1's pinned Lean-side
extractor will produce at scale, plus a small, committed, hand-built positive
pack that exercises the format today. It is a **contract**, not a pipeline:
nothing here invokes `lean4export` or builds Mathlib. C1
(`artifact-extract`, per the roadmap's lane table) owns turning a live
Lean/Mathlib environment into packs of this shape; this directory owns *what
shape a pack must have* and *what a validator must catch when it doesn't*.

Governing docs: `docs/plan/library-artifact-compatibility-roadmap-2026-08-30.md`
section C0, and
`docs/research/09-decisions/adr-0717-library-construction-is-graph-directed-through-an-artifact-compatible-trust-anchor.md`.
The design decisions specific to this contract are recorded in
`docs/research/09-decisions/adr-0800-the-library-artifact-record-splits-type-and-proof-into-different-files.md`.

## Why a positive pack is hand-built, not extracted

The bounded pack under `packs/` describes nine real Lean/Mathlib-core
declarations (`Nat`, `Nat.zero`, `Nat.succ`, `Nat.rec`, `Eq`, `Eq.refl`,
`id`, `Nat.add`, `Nat.add_comm`) with faithful types and a plausible rendering
of their values. The type/value **text** is this contract's own canonical
rendering, not lean4export's raw output — C1 owns matching that rendering to
the real extractor. What is genuine here is the *shape* and the *digests*:
every digest in the committed pack is mechanically recomputed from the
recorded fields by two independently written readers (below), so the pack
cannot silently drift from what the spec says a valid pack looks like.

## Record shape

A **pack** (`packs/*.pack.json`) is one JSON object:

```
contract_version          string, e.g. "0.1.0"
lean_version               e.g. "4.30.0"
lean_commit                 the pinned Lean commit
mathlib_version              e.g. "v4.30.0" tag/branch label
mathlib_commit                the pinned Mathlib commit (c5ea0035... in this repo)
normalization_version       integer; bumps whenever the canonical text renderer's
                             normalization rules change (whitespace, binder names, ...)
renderer_version             integer; bumps whenever the type/value -> string
                             renderer changes, independent of normalization
source_population           { population_id, requested_roots: [name...],
                              expected_declaration_count: int }
trusted_declaration_identities   [name...] -- every declaration in this pack whose
                                  kind carries no proof term (Inductive, Constructor,
                                  Recursor, Axiom, Opaque, Quotient); derived, never
                                  asserted independently of `declarations`
pack_digest                  "sha256:<hex>" -- see "Pack digest" below
declarations                 [declaration...] -- canonical order: ascending by `name`
```

A **declaration** record:

```
name                  canonical dotted name, e.g. "Nat.add_comm"
kind                  one of Inductive | Constructor | Recursor | Axiom | Opaque
                       | Quotient | Definition | Theorem
universes             [name...] -- universe parameter names, [] if none
type                  canonical rendered text of the declaration's type
value                 canonical rendered text of the value/proof, or null
type_digest            "sha256:<hex>" of the UTF-8 bytes of `type`
value_digest            "sha256:<hex>" of the UTF-8 bytes of `value`, or null iff
                        value is null
identity_digest         "sha256:<hex>", see "Identity digest" below
direct_type_deps        [name...] sorted, names the TYPE mentions
direct_value_deps       [name...] sorted, names the VALUE/proof mentions (in
                        addition to whatever the type already mentions); []
                        if value is null
transitive_type_deps    [name...] sorted -- full closure reachable by following
                        ONLY direct_type_deps edges (of this and every
                        dependency), starting from this declaration's own
                        direct_type_deps
transitive_value_deps   [name...] sorted -- full closure reachable by following
                        BOTH direct_type_deps and direct_value_deps edges,
                        starting from the union of this declaration's own
                        direct_type_deps and direct_value_deps
```

`transitive_type_deps` never depends on any `value`/`direct_value_deps` field,
anywhere in the closure — see "Structural separation" below.

Invariant: `kind` is a **trusted** kind (Inductive, Constructor, Recursor,
Axiom, Opaque, Quotient) if and only if `value`, `value_digest` are `null` and
`direct_value_deps`, `transitive_value_deps` are `[]`. Definition and Theorem
always carry a non-null value. This is a sanity invariant on the full pack; it
is distinct from the producer-projection guard below, which applies to every
declaration regardless of kind.

## Canonical digest algorithm (both readers implement this from this text,
## not from each other's code)

- `type_digest`  = `"sha256:" + hex(sha256(utf8(type)))`
- `value_digest` = `null` if `value is null`, else `"sha256:" + hex(sha256(utf8(value)))`
- `identity_digest` = `"sha256:" + hex(sha256(utf8(identity_string)))` where

  ```
  identity_string =
      name + "\x00" + kind + "\x00" + ",".join(universes) + "\x00" +
      type_digest + "\x00" + (value_digest or "NONE") + "\x00" +
      ",".join(sorted(direct_type_deps)) + "\x00" +
      ",".join(sorted(direct_value_deps))
  ```

  `direct_type_deps`/`direct_value_deps` are sorted before joining so the
  identity digest is a function of the *sets*, not of on-disk array order.
  `universes` is joined WITHOUT sorting: universe parameter order is part of
  a declaration's public interface (it decides how a caller instantiates
  `.{u,v}`), so reordering it is a real change, not noise.

- `pack_digest` = `"sha256:" + hex(sha256(utf8(chain_string)))` where

  ```
  chain_string = "\n".join(d["identity_digest"] for d in declarations)
  ```

  taken in **file order** — this is deliberately order-sensitive. Per-record
  identity is order-independent (dependency sets are sorted before hashing),
  but the pack as a sequence is a hash chain over that order, so permuting
  `declarations` changes `pack_digest` even though no individual record
  changed. This is what makes the REORDERED mutation class distinct from
  TRUNCATED/DUPLICATE: content-level checks alone cannot see a permutation.

## Transitive closures

`transitive_type_deps(d)` = least fixed point of: start with
`direct_type_deps(d)`; for every name `n` already in the set, if `n` has a
record, add `direct_type_deps(n)`; repeat to a fixed point. It never expands
through any `direct_value_deps` edge, of `d` or of anything in its closure.

`transitive_value_deps(d)` = same fixed-point construction, but starting from
`direct_type_deps(d) ∪ direct_value_deps(d)` and expanding through BOTH kinds
of edge at every node.

## Structural separation of type and proof/value data

Planning rule (`docs/plan/global/50-planning-rules.md`): "Proof data does not
leak into autonomous discovery: upstream proof/value dependency edges may
measure and sequence work but are physically excluded from proof-isolated
producer inputs and autonomous credit." This contract enforces that
physically, not just by convention:

- The full pack (`*.pack.json`) is the archival/evaluation artifact. It is
  never hashed as if it were the producer input, and nothing that dispatches
  a producer keeps a live handle to it.
- A **producer projection** (`*.typeproj.json`) is derived from the pack by a
  pure, one-directional function (`project_type_only` in both readers) that
  emits, per declaration, **exactly** the keys `name`, `kind`, `universes`,
  `type`, `type_digest`, `direct_type_deps`, `transitive_type_deps`. The keys
  `value`, `value_digest`, `direct_value_deps`, `transitive_value_deps` are
  never written to this file — not nulled, ABSENT, so a consumer that reads
  this file's records as (e.g.) a Python `TypedDict`/dataclass with only
  those five-plus-two fields cannot reach proof data through it even by
  mistake; there is no attribute path to it. The projection function itself
  never reads `value` or `direct_value_deps` off the source record — it is
  written to destructure only the allowed fields, so it cannot leak them even
  if the schema grew a new value-bearing field later without the projector
  being updated (a validator step separately fails closed if it does, see
  the VALUE_EXPOSED guard).
- The projection is the only thing a producer-input pipeline may read. The
  full pack lives in a different directory role (`packs/`, evaluation-only)
  from the projection (co-located here only because this is a demonstration
  contract; a real deployment gives them different filesystem roots so a
  producer process's read scope cannot even name the archival file).

## The five mutation classes, and which guard kills each

`scripts/check-library-artifact-contract.py` (reader A / the validator) runs
five independent guards. `scripts/check-library-artifact-contract-reader-b.py`
(reader B) reimplements identity/closure/guard logic from this spec with a
different traversal, different digest assembly, and a different visited-set
representation, and must agree with reader A on every accepted pack.

| # | Mutation | Guard | What it checks | What it can't be confused with |
|---|----------|-------|-----------------|-------------------------------|
| 1 | MISSING  | `check_missing_roots` | Every `expected_roots` name for the pack's declared `population_id`, read from `populations/<population_id>.json` (an authority file the pack under test does **not** control), is present among `declarations[*].name`. | DUPLICATE (names present but repeated), TRUNCATED (names present but content corrupted) |
| 2 | DUPLICATE | `check_no_duplicate_names` | `declarations[*].name` has no repeats. | MISSING (a name entirely absent), REORDERED (names all present once, in the wrong sequence) |
| 3 | REORDERED | `check_pack_digest` | Recomputed `pack_digest` (order-sensitive hash chain over `identity_digest` in file order) equals the recorded `pack_digest`. | TRUNCATED (a per-record digest mismatch, order untouched), DUPLICATE (a name-uniqueness violation, order untouched) |
| 4 | TRUNCATED | `check_record_digests` | For every record, recomputing `type_digest`/`value_digest`/`identity_digest` from that record's own `type`/`value`/`name`/`kind`/`universes`/dep-lists reproduces the recorded digests. | REORDERED (whole-pack sequence check, not a per-record content check), VALUE_EXPOSED (a projection-file key-shape check, not a digest check) |
| 5 | VALUE_EXPOSED | `check_typeproj_no_value_leak` | Every record in a `*.typeproj.json` file has **exactly** the seven allowed keys — no `value`, `value_digest`, `direct_value_deps`, or `transitive_value_deps` key present, on any record, of any kind. | The trusted-kind/value invariant above (a full-pack sanity check, not a producer-projection check) |

`scripts/tests/test-library-artifact-contract-mutations.py` builds one
mutated copy of the good pack (or its projection) per row above, asserts the
validator rejects it while the unmutated pack and the OTHER four mutated
copies still validate, and then — in a scratch copy of the validator source,
never the tracked file — deletes each guard's code one at a time and asserts
that **exactly** the matching mutation's test flips from fail to pass while
the other four stay correctly failing. The guard -> test kill table is
printed by that script and reproduced in
`docs/plan/status/l1-c0-artifact-contract.md`.

## What this contract does not capture

The positive pack's type/value text is this contract's own hand-authored
rendering of real Lean/Mathlib-core declarations, not lean4export's actual
byte-for-byte output — C0 freezes the *record shape and validation contract*,
not a working extractor; wiring a real pinned Lean-side extractor that emits
packs of this exact shape, at population scale, sharded and content-addressed,
is C1's job.

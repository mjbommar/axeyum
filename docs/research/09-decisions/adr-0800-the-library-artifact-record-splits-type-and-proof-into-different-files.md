# ADR-0800: The library artifact record splits type and proof into different files, and a missing root is checked against an authority the pack does not control

Status: accepted
Date: 2026-08-30
Index-summary: L1 phase C0 freezes the library-artifact pack format: per-declaration content digests, an order-sensitive pack digest, a type-only producer projection with no value-bearing key, and root coverage checked against an external population registry

## Context

`docs/plan/library-artifact-compatibility-roadmap-2026-08-30.md` section C0
calls for one versioned record for a declaration root and its closure,
carrying Lean/Mathlib version identity, per-declaration digests, separate
type/proof dependency edges, trusted-declaration identities, normalization
and renderer versions, and source-population coverage counts. Its exit
criterion is that two independent readers reproduce all identities on a
bounded positive pack, and that missing, duplicate, reordered, truncated, and
value-exposed-statement-only mutations all fail -- specifically including a
missing EXPECTED ROOT, not merely a malformed row.

`docs/plan/global/50-planning-rules.md` separately requires: "Proof data does
not leak into autonomous discovery: upstream proof/value dependency edges may
measure and sequence work but are physically excluded from proof-isolated
producer inputs and autonomous credit." A record format that merely
documents this as a convention (e.g. "producers should ignore the `value`
field") does not meet "physically excluded" -- nothing stops a producer
pipeline from reading it anyway, and nothing in this repository's own history
suggests that convention alone holds (see CLAUDE.md's repeated account of
checkers that could not fail because nothing in their construction depended
on the thing they were meant to check).

This ADR covers only C0: the record shape and its validator. It does not
build the pinned Lean-side extractor (C1), the universal checked interchange
(C2), or the Lean adapter (C3); those remain separately owned per the
roadmap's lane table.

## Decision

1. **A pack is one JSON record** (`artifacts/library-artifact/packs/*.pack.json`)
   carrying Lean/Mathlib version and commit identity, a
   `normalization_version`/`renderer_version` pair, a `source_population`
   block (population id, requested roots, expected declaration count), a
   derived `trusted_declaration_identities` list, an order-sensitive
   `pack_digest`, and an array of declaration records in canonical
   (ascending-by-name) order.

2. **Every declaration record carries four separate dependency fields**:
   `direct_type_deps`, `direct_value_deps`, `transitive_type_deps`,
   `transitive_value_deps`. The two transitive fields are defined so that
   `transitive_type_deps` is a closure over ONLY `direct_type_deps` edges,
   full stop -- its computation never reads any `value` or
   `direct_value_deps` field belonging to itself or to anything in its own
   closure. This is checked, not merely documented: reader B's `Graph` class
   in `check-library-artifact-contract-reader-b.py` exposes a
   `type_neighbors` method that returns only `direct_type_deps`, structurally
   incapable of returning a value edge.

3. **A separate, derived producer-facing artifact — the type-only
   projection (`*.typeproj.json`) — is the only thing a producer pipeline
   may read**, and it enforces the planning rule's "physically excluded"
   structurally rather than by convention: the projection function
   (`project_type_only` in both readers) DESTRUCTURES only the seven
   type-facing keys out of a declaration dict; `value`, `value_digest`,
   `direct_value_deps`, and `transitive_value_deps` are never named by that
   function, so they cannot leak through it even if the source record grew a
   new value-bearing field the projector was not updated for. The projection
   file itself never contains those four keys on any record, of any kind --
   checked by `check_typeproj_no_value_leak`, one of the five guards below.
   A consumer that reads this file into a narrow type (e.g. a Python
   TypedDict with exactly those seven fields) has no attribute path to proof
   data at all, which is the strongest version of "cannot accidentally
   receive proof edges" available without a second runtime/process boundary.
   A real deployment should additionally give the archival pack and the
   type-only projection different filesystem roots, so a producer process's
   read scope cannot even name the archival file; this repository's
   demonstration keeps them side by side in one directory for legibility.

4. **Two independently-coded readers**, not one implementation run twice.
   Reader A (`scripts/check-library-artifact-contract.py`) is the aggregate-
   gate validator. Reader B
   (`scripts/check-library-artifact-contract-reader-b.py`) reimplements the
   same spec with a different digest-assembly style (incremental
   `hashlib.update()` calls instead of join-then-hash), a different data
   model (a frozen dataclass plus an adjacency `Graph` object instead of raw
   dicts), and a different traversal (depth-first recursion with a memoized
   visited set instead of a breadth-first worklist). Building reader B this
   way caught a real defect before any test did: its first draft appended a
   trailing separator byte after the LAST hashed field, so every
   `identity_digest` disagreed with reader A's on the very first run. That is
   the exit criterion's whole point -- agreement between genuinely different
   code is evidence the specification is unambiguous; agreement between one
   implementation and itself is not evidence of anything.

5. **A missing root is checked against an external authority.** The MISSING
   guard (`check_missing_roots`) loads `artifacts/library-artifact/
   populations/<population_id>.json` -- a file the pack under test does not
   write and cannot edit -- and requires every name in that file's
   `expected_roots` to be present among the pack's own declaration names. A
   pack that deletes a root AND edits its own `source_population.
   requested_roots`/`expected_declaration_count` to match (simulating an
   attacker cleaning up every self-referential field it controls) still
   fails, because the guard never treats those pack-internal fields as its
   source of truth. Proven in
   `scripts/tests/test-library-artifact-contract.py::
   test_missing_root_ignores_the_packs_own_tampered_metadata`.

6. **Five guards, five distinct mutation classes, mutation-verified 1:1.**
   `scripts/tests/test-library-artifact-contract-mutations.sh` builds a
   scratch copy of reader A, deletes one of the five `# GUARD:<NAME>`-
   delimited functions at a time (replacing its body with `return []`), and
   requires that deletion to flip EXACTLY its own mutation's fixture from
   FAIL to PASS while the other four stay FAIL and the good pack stays PASS:

   | Mutation | Guard | What only that guard checks |
   |---|---|---|
   | MISSING | `check_missing_roots` | external-registry root coverage |
   | DUPLICATE | `check_no_duplicate_names` | name uniqueness |
   | REORDERED | `check_pack_digest` | order-sensitive hash-chain over file order |
   | TRUNCATED | `check_record_digests` | per-record digest/closure recomputation |
   | VALUE_EXPOSED | `check_typeproj_no_value_leak` | projection-file key shape |

   Each mutation fixture is built "surgically" in
   `scripts/tests/library_artifact_mutations.py`: every OTHER
   self-referential field an attacker could plausibly recompute (pack_digest,
   the pack's own declared counts/roots) is kept internally consistent, so
   that a guard's removal cannot be rescued by an unrelated check catching
   the same mutation by accident. This is what makes the 1:1 kill table mean
   something rather than being an artifact of overlapping checks.

## Alternatives

**Null out `value`/`direct_value_deps` on a producer-facing copy of the same
record shape, rather than a genuinely narrower schema.** Rejected: a nulled
field is still a key a consumer can read, and a later change to the
projector that forgot to null a new value-bearing field would silently leak
it. Destructuring into a strictly smaller allowed-key set, checked by a
dedicated guard, fails closed instead.

**Use `jsonschema` for structural validation.** Rejected for the same reason
`scripts/validate-facts.py` gives: it would make the C0 gate depend on a
package not guaranteed present on every host that runs `just check`/
`check.sh`. A JSON Schema document is still committed
(`artifacts/library-artifact/schema/library-artifact-pack.schema.json`) as
reference documentation; the gate itself validates structurally in pure
Python.

**Check root coverage against a field inside the pack itself
(`source_population.requested_roots`).** Rejected: this is exactly the
"every X" trap CLAUDE.md documents repeatedly -- a check that derives its
expected population from the artifact it is checking cannot see an artifact
that is missing something it should have. An external registry file is
authority the mutation cannot also control.

**One reader, run twice, or two readers sharing a digest-assembly helper.**
Rejected per the roadmap's own exit-criterion framing: agreement between a
tool and itself is not the evidence the exit criterion asks for. Reader B
was required to differ in traversal, data structure, and digest assembly
specifically so that agreement is evidence about the SPEC, not about one
codebase's internal consistency.

## Consequences

C1 (`artifact-extract`) must produce packs whose declaration records satisfy
this exact shape and whose digests reproduce under both readers; it inherits
the type/value separation and the sharded, content-addressed requirement
this ADR does not itself build. C2's universal checked interchange and C3's
Lean adapter both consume the type-only projection as their producer-facing
input, never the archival pack, for anything upstream of an already-decided
kernel admission. The bounded positive pack under `artifacts/library-artifact/
packs/nat-add-comm-v1.pack.json` is a hand-authored demonstration of the
contract (nine Lean-core declarations: `Nat`, `Nat.zero`, `Nat.succ`,
`Nat.rec`, `Eq`, `Eq.refl`, `id`, `Nat.add`, `Nat.add_comm`), not C1's
output -- its type/value TEXT is this contract's own rendering, while its
digests are mechanically derived and independently reproduced, which is what
C0 asks for.

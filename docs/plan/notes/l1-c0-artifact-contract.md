# Notes: l1-c0-artifact-contract

Detail moved out of [`../status/l1-c0-artifact-contract.md`](../status/l1-c0-artifact-contract.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

- **Two independent readers.** `scripts/check-library-artifact-contract.py`
  (reader A, the aggregate-gate validator) and
  `scripts/check-library-artifact-contract-reader-b.py` (reader B) implement
  the digest/closure spec in `artifacts/library-artifact/README.md` with
  deliberately different code: join-then-hash vs. incremental
  `hashlib.update()`, raw dicts vs. a frozen dataclass + adjacency `Graph`,
  breadth-first worklist vs. depth-first memoized recursion. Building reader
  B this way caught a real bug on its FIRST run, before any test did: its
  first draft appended a trailing separator byte after the last hashed
  field, so every `identity_digest` disagreed with reader A's. Fixed to hash
  exactly `"\x00".join(fields)`'s byte sequence; both readers now agree
  byte-for-byte on all 9 declarations' `type_digest`/`value_digest`/
  `identity_digest`, both transitive closures, and the order-sensitive
  `pack_digest`.
- **Structural type/proof separation.** `docs/plan/global/50-planning-rules.md`
  requires proof/value data be "physically excluded from proof-isolated
  producer inputs." Enforced structurally, not by convention: the type-only
  producer projection (`packs/nat-add-comm-v1.typeproj.json`) is built by a
  function that DESTRUCTURES only the seven type-facing keys out of a
  declaration — `value`/`value_digest`/`direct_value_deps`/
  `transitive_value_deps` are never named by it, so a schema change adding a
  new value-bearing field cannot leak through this projector without
  updating it. The VALUE_EXPOSED guard independently checks the projection
  file itself never carries a forbidden key, on any record, of any kind.
- **Five mutation classes, five distinct guards, mutation-verified 1:1.**
  `scripts/tests/test-library-artifact-contract-mutations.sh` neuters one of
  the five `# GUARD:<NAME>`-delimited functions at a time in a SCRATCH COPY
  of reader A (never the tracked file) and confirms exactly the matching
  mutation's fixture flips FAIL -> PASS while the other four stay FAIL and
  the good pack stays PASS:

  | Mutation | Guard |
  |---|---|
  | MISSING | `check_missing_roots` |
  | DUPLICATE | `check_no_duplicate_names` |
  | REORDERED | `check_pack_digest` |
  | TRUNCATED | `check_record_digests` |
  | VALUE_EXPOSED | `check_typeproj_no_value_leak` |

  Each mutation fixture (`scripts/tests/library_artifact_mutations.py`) is
  built surgically: every OTHER self-referential field an attacker could
  recompute (`pack_digest`, the pack's own declared counts/roots) is kept
  internally consistent, so a guard's removal cannot be rescued by an
  unrelated check catching the same mutation by accident.
- **Fails on a missing expected root, not merely a malformed row.** The
  MISSING guard cross-checks against `artifacts/library-artifact/
  populations/<population_id>.json` — a file the pack under test does not
  control. Proven directly: deleting `id` from the pack AND editing the
  pack's own `source_population.requested_roots`/
  `expected_declaration_count` to hide the deletion still fails, naming `id`
  by name, because the guard never reads those pack-internal fields as its
  authority (`test_missing_root_ignores_the_packs_own_tampered_metadata`).

14 tests in `scripts/tests/test-library-artifact-contract.py`, all green.
Registered in both `justfile` (`library-artifact-contract` recipe, added to
`check:`'s dependency list) and `scripts/check.sh` (four `step` lines:
`library-artifact-contract`, `library-artifact-contract-reader-b`,
`library-artifact-contract-tests`, `library-artifact-contract-mutations`).
Verified via `AXEYUM_CHECK_LIST=1 bash scripts/check.sh` (steps register,
list-only) and `just library-artifact-contract` (full run, all green) —
never the full aggregate gate.

**What this contract does NOT capture**, stated plainly: the positive pack's
type/value TEXT is this contract's own hand-authored rendering of real
Lean/Mathlib-core declarations, not lean4export's actual byte-for-byte
output. C0 freezes the record shape and validation contract; a real pinned
Lean-side extractor producing packs of this exact shape at population scale,
sharded and content-addressed, is C1's job.

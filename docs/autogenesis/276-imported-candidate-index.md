# Footprint-aware imported candidate index

Date: 2026-08-26

## Result

Imported theorem candidates now have a separate generated search population:
[`imported-candidate-search-index-v1.json`](../../artifacts/autogenesis/imported-candidate-search-index-v1.json).
The generator scans only explicit, independently imported candidate audits. It
publishes canonical and alpha-stable type identities, declaration and direct-
dependency identities, exact theorem dependencies, external stream receipts,
and measured axiom footprints.

Every row receives one fail-closed routing disposition:

- `candidate-executable` only when its measured footprint is empty; or
- `reconstruct-required` when any assumption remains.

The first population contains one candidate, `Nat.testBit_bitwise`. It has five
footprint members and is therefore strategy-eligible but not execution-
eligible. The index reports 1 candidate, 0 executable, and 1 requiring
reconstruction.

This population is intentionally separate from the native kernel lemma index.
Merging them would erase three distinctions that matter:

1. the declaration lives in an imported stream rather than Axeyum's constructed
   prelude;
2. its proof carries assumptions even though its proposition may be
   constructively provable; and
3. its external capsule must be resolved and re-hashed before use.

## Descriptor surface

The new `imported_candidate_descriptor` Rust example imports a root-selected
stream and emits the machine-readable fields used by the index. For
`Nat.testBit_bitwise` it confirms the generic type
`testBit (bitwise f x y) i = f (testBit x i) (testBit y i)`, exact structural
hashes, 29 direct theorem dependencies, and the five-member footprint. This
makes the audit reproducible without parsing human-oriented command output.

The descriptor is diagnostic: it does not admit the candidate into another
kernel, authorize transport, or claim the external file is part of Git.

## Next integration

1. Add this index to the agent's candidate-only read surface beside, not inside,
   the native lemma index.
2. Match by exact/alpha type structure and visible operators; preserve source,
   footprint, and disposition in every returned row.
3. Refuse an execution attempt for `reconstruct-required` candidates. Instead,
   dispatch a reconstruction strategy over the target kernel's transparent
   definitions and allowed axiom-free premises.
4. On successful empty-footprint reconstruction, create a new checked receipt;
   never mutate the original imported audit to pretend its proof was clean.
5. Expand the population only through root-selected, content-addressed audits;
   theorem-name discovery alone never creates an index row.

The normal Autogenesis knowledge gate checks artifact freshness without the
external mount. The candidate replay recipe re-hashes the external stream,
reruns the ordinary independent import, and emits the exact descriptor.

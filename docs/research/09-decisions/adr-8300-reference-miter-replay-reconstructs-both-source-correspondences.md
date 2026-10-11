# ADR-8300: Reference-miter replay reconstructs both source correspondences

Status: proposed
Date: 2026-10-11

## Decision

The existing end-to-end QF_BV producer carries a reference-miter DIMACS/DRAT
pair and a final UNSAT certificate. Its legacy `recheck` checks the two clausal
refutations; it does not establish their correspondence to a caller's source.
Keep that text-checking API, describe its boundary explicitly, and add
`EndToEndUnsatOutcome::recheck_for_bool_terms(arena, assertions)`.

Factor deterministic reference-miter construction out of the search producer.
Replay never calls SAT search. Require that the final certificate matches the
exact deterministic encoding of the original Boolean assertions, and that the
faithfulness certificate matches the exact reconstructed miter for those same
assertions. Then check both refutations. A valid refutation for another CNF
cannot substitute for either correspondence. Unsupported terms and malformed
proof text remain errors; uncertified outcomes and mismatches cannot succeed.

The existing independent reference bit-blaster and Tseitin correspondence are
explicit trusted code. This is stronger source-bound replay, not a kernel proof,
a generic theory-elimination certificate, or original-byte authentication.
Equivalent queries with identical deterministic encodings may replay. Existing
unlimited replay and search-only production deadlines keep their documented
contracts; a future timed checker must thread one deadline across every phase.

## Validation

Honest Boolean/BV certificates replay; rebuilding the original typed query in
another arena and reparsing its writer output also replay. A substituted SAT
query, an unrelated valid final refutation, an unrelated valid miter refutation,
modified hints, and missing refutation steps must not succeed. Uncertified and
unsupported cases are explicit. Private snapshot mutations of each of the two
source-correspondence guards must each kill exactly one intended control.
Check independent-reference producer fixtures after factoring construction;
require nonzero populations, full solver tests, and workspace library tests.


## Python contract

Expose `proofs.certify_qf_bv_unsat_end_to_end` with explicit certified,
satisfiable, and not-certified outcomes. A not-certified result contains no
proof and supplies no verdict. Both searches share the optional deadline;
deterministic construction/checking retain the existing unlimited contract.
A budget already expired at Python entry declines before production.

`EndToEndUnsatProof` stores separate faithfulness and final `UnsatProof` data.
Its restoration constructor bounds each component by the existing 8 MiB/text,
16 MiB/component transport caps (32 MiB combined); it accepts no claim.
`recheck_refutations` checks only the two clausal proofs;
`recheck_for_bool_terms` supplies source-bound reference-miter replay. Expose
both components for file export; miter LRAT remains explicitly absent.

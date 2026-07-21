# ADR-0337: Preregister Tock end-to-end proof v3

Status: proposed
Date: 2026-07-21

## Context

ADR-0336 v2 correctly rejects its first target result because the generic
`prove` route returns a plain clausal DRAT fallback whose per-run trust ledger
marks BitBlast uncertified. This is documented behavior, not a newly discovered
missing checker: ADR-0031 explicitly distinguishes plain DRAT export from the
separate bit-blast-miter route.

The read-only post-result audit finds an existing stronger API:
`certify_qf_bv_unsat_end_to_end_within`. It first proves production bit-blasting
equivalent to the independently implemented reference bit-blaster using a
DRAT-checked miter, then produces and checks the final bit-blasted-CNF DRAT
refutation. `EndToEndUnsatOutcome::recheck` reparses and independently rechecks
both stored certificates. The capability matrix already classifies this route
as checked; the generic evidence route simply did not select it for the target.

## Decision

Create proof v3 by changing only the eight positive proof rows to the existing
end-to-end certification API. Keep the six countermodel controls and every
authenticated input/reflection/native-replay rule unchanged. This is an API
selection correction and measured evidence use case, not new bit-blaster or
checker research.

## Frozen v3 gates

1. Commit and push this zero-result ADR before changing the Rust runner or
   adding v3 producer bytes. V1 and v2 remain frozen and are never rerun.
2. Pin and validate v2 registration SHA-256 `47ac5872...c6f4`, accepted preflight
   SHA-256 `9222aa62...63f`, and negative SHA-256 `2a584106...4b75`. Require one
   official v2 invocation/query, raw `Proved`, zero credited rows, exact
   BitBlast=false/Tseitin=true/SatRefutation=true ledger, absent output, and no
   reported OOM-delta failure.
3. For each existing positive goal `g`, certify the single assertion `not g`
   with `certify_qf_bv_unsat_end_to_end_within` and an absolute 30-second
   per-row deadline. Credit only `EndToEndUnsatOutcome::Certified` followed by
   `recheck() == Ok(true)`. `Satisfiable`, `NotCertified`, error, timeout, or
   failed recheck receives no proof credit.
4. Report the evidence family as composed miter+refutation DRAT. Each proof row
   must carry deterministic SHA-256 and byte counts for faithfulness DIMACS,
   faithfulness DRAT, final DIMACS, final DRAT, and final LRAT when present. Wall
   time remains observational and excluded from stable result identity.
5. Replace v2's single `solver` policy with an exact two-part policy: positive
   rows use the end-to-end route, 30-second deadline, two DRAT rechecks, and the
   outer cgroup; controls retain v2's exact pure-Rust QF_BV `SolverConfig`, model
   replay, and native oracle. Do not claim unused node/CNF knobs govern the
   end-to-end proof API.
6. Preserve v2's authenticated capture/canonical hashes, LLVM reflection,
   definedness/value goals, independent floor-log/MSB specifications, three
   mutation families per target, row ordering/counts, pushed-HEAD archive and
   link policy, tool identities, corrected lock, 600-second runner timeout,
   4-GiB cgroup, atomic cleanup, and stable identity projection.
7. Version registration/result schemas and use only ignored
   `target/tock-log2-20260721/proof-v3`. Before target observation, push the
   runner/producer/registration and run the same fresh archived-HEAD
   non-authenticated independent-spec compilation preflight. It must leave v3
   output absent.
8. After the successful preflight is recorded and pushed, require local HEAD,
   tracking, and remote `main` equality and invoke v3 exactly once. Acceptance
   remains exactly two functions, eight end-to-end certified proofs, six
   replayed controls, zero `UNKNOWN`, and zero `DISAGREE`.
9. Any official v3 failure closes v3. Never relabel plain DRAT, weaken the
   all-certified requirement, omit either recheck, or rerun after observation.

No v3 proof query, certificate hash/size, control, row, or output may be observed
before the v3 producer and registration are committed, pushed, and pass their
no-query archived compilation preflight.

## Rejected alternatives

- **Mark v2 BitBlast certified because the global ledger says it is
  certifiable.** Rejected: certification is per run; v2 did not run the miter.
- **Accept the v2 clausal DRAT alone.** Rejected: it certifies only the encoded
  CNF and does not close the target term-to-AIG lowering boundary.
- **Build a new verified bit-blaster.** Rejected for this step: the existing
  independent-reference miter route already meets Axeyum's documented trust
  standard and is the missing API selection.
- **Run v3 before freezing the policy split.** Rejected: the end-to-end API has
  different enforceable limits from generic `SolverConfig`; reporting them as
  identical would be misleading.

## Consequences

- The Tock cell becomes a concrete, reproducible dual-DRAT use case if the
  existing end-to-end route handles the exact reflected formulas.
- Failure remains scientifically useful: it will identify a genuine coverage,
  deadline, memory, or certificate-recheck boundary rather than a mislabeled
  trust ledger.

## References

- [ADR-0336](adr-0336-preregister-tock-log2-proof-v2.md).
- [ADR-0031](adr-0031-reduction-trust-ledger.md).
- [Scalable bit-blast certification](../07-verification/scalable-bitblast-certification.md).
- [Capability matrix](../08-planning/capability-matrix.md).

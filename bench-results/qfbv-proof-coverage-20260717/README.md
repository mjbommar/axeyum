# Generated QF_BV proof-coverage denominator

- Date: 2026-07-17
- Axeyum revision: `7866b92138f547462f5461b023ced9f89395cb60`
- Report SHA-256:
  `abbc150cb8f0dbaa367389380828ee6e96625b6bb62d721cbe336b023980c330`
- Seed-83 SHA-256:
  `8e11e509c92e6cfc358ee3490954acca1873cef98e5fd2351a8e91ea25f14715`
- Base population: the ADR-0225 4,000-formula fixed-seed sweep
- Selected denominator: jointly UNSAT, width at most 8, seed divisible by 4

The base sweep contains 1,487 SAT and 2,513 UNSAT formulas. The predeclared
proof subset contains 169 UNSAT formulas, or 6.725030% of the full generated
UNSAT population. All 169 produce independently rechecked CNF DRAT proofs, and
all 169 produce end-to-end certificates whose faithfulness-miter and final DRAT
components both recheck. Thus coverage is 100% of the selected denominator,
not 100% of all 2,513 UNSAT formulas; 2,344 UNSAT rows were not measured by
this run.

The wider width-at-most-8 cohort is not accepted. A stride-one diagnostic
isolates deterministic seed 83: its CNF DRAT proof finishes and rechecks, but
the end-to-end faithfulness route does not finish before a 15-second
process-level timeout. The exact query is [`seed-83.smt2`](seed-83.smt2). This
is not a failed certificate or a solver disagreement; it exposes that the
certificate API has no cooperative per-instance deadline, so the row remains
unmeasured rather than being counted against or inside coverage.

Exact counts, commands, and boundary classification are in
[`report.json`](report.json). The next honest widening step is a deadline-aware
or process-isolated proof harness, followed by a broader declared denominator;
waiting indefinitely inside the current API is not an evidence method.

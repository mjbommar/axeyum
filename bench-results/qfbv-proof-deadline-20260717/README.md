# Deadline-aware generated QF_BV proof coverage — 2026-07-17

The complete width-at-most-8 UNSAT cohort from the standing 4,000-formula
generator now runs under an explicit 100 ms proof-search deadline per proof
route. This removes ADR-0226's indefinite seed-83 block without excluding the
row or converting resource expiry into a verdict.

| Measure | Result |
|---|---:|
| Generated formulas | 4,000 |
| Axeyum/Z3 decided and agreed | 4,000 |
| SAT original-model replays | 1,487/1,487 |
| Total generated UNSAT | 2,513 |
| Predeclared width≤8 UNSAT denominator | 1,505 (59.888579%) |
| CNF DRAT proved and rechecked | 1,505/1,505 (100%) |
| End-to-end faithfulness + DRAT certified and rechecked | 1,487/1,505 (98.803987%) |
| End-to-end `NotCertified` at the resource policy | 18/1,505 (1.196013%) |

The 18 uncovered seeds are `83, 359, 741, 1063, 1094, 1275, 1437, 1495,
1873, 1906, 2635, 2793, 2826, 2907, 2986, 3127, 3447, 3638`. They remain
inside the denominator. CNF DRAT succeeds on all 18; only the stronger
faithfulness-miter composition is not certified under this budget.

## Identity and command

- Axeyum revision: `86791f90b259797ae6d53a3f33adc873b9c9cb8e`,
  clean tracked tree.
- Rust: `rustc 1.97.0-nightly (f53b654a8 2026-04-30)`.
- Report SHA-256:
  `c7ec63c3ad2edfe20e631ed1323acb46057f0f70d4d777cc6ba2dc1078fa1571`.

```sh
AXEYUM_QFBV_PROOF_SAMPLE_STRIDE=1 \
AXEYUM_QFBV_PROOF_DEADLINE_MS=100 \
cargo test -p axeyum-solver --all-features \
  --test bv_differential_fuzz bv_differential_fuzz_disagree_zero -- --nocapture
```

The source-exact run passes in 554.96 seconds. A preceding content-equivalent
repetition produced the same counts and exact uncovered-seed list in 553.83
seconds. cvc5 was unavailable for these proof-specific repetitions; ADR-0225
already records exhaustive cvc5 agreement over all 4,000 formulas and remains
the neutral-oracle evidence.

[`report.json`](report.json) records the complete population, selection,
deadline contract, assurance-level counts, uncovered seeds, source/toolchain,
and claim exclusions.

## Deadline and claim boundary

The new public bounded API threads one absolute deadline through the
faithfulness-miter proof search and the final CNF-refutation proof search.
Expiry returns `Inconclusive`/`NotCertified`; it never fabricates SAT or UNSAT.
Completed proofs still independently recheck.

The deadline intentionally does not interrupt deterministic lowering,
miter/CNF construction, or completed-proof checking. Several rows therefore
take longer than 100 ms end to end. This artifact closes the known indefinite
proof-search block, not the separate whole-certificate process-isolation
boundary.

Coverage is 98.803987% of the selected 1,505-row denominator, not 100% of
finishers and not 100% of all 2,513 generated UNSAT formulas. The 169/169
ADR-0226 subset remains a valid smaller all-certified gate; this wider result
supersedes it only for population coverage, not routine CI cost.

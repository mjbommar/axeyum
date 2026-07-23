# Lean U2 TL0.6.5 R2 result — derived comparison outcomes

Date: 2026-07-23  
Status: **accepted bounded schema correction; no execution or parity credit**  
Plan: [R2 derived-outcome plan](lean-u2-matched-execution-tl0.6.5-outcome-derivation-r2-plan-2026-07-23.md)  
Implementation checkpoint: `7d2a4f54`

## Result

The terminal paired-cell validator no longer trusts a sealed comparison label.
Every complete official/Axeyum execution now projects one typed result class,
and the comparison retains separate canonical normalized-observable identities
for the two sides. State, result classes, normalized availability, and
normalized equality deterministically derive the only admissible outcome.

This closes the R1 residual where two immutable `complete` records could claim
`agree-success` without either side proving `success` or the comparison proving
normalized equality.

## Accepted schema

Execution records add `result_class` with exact complete-state values:

- `success`;
- `reject`;
- `decline`;
- `timeout`;
- `resource-exhaustion`; or
- `failure`.

`not-run` and `invalid` require null result class. The comparison adds
`official_normalized_sha256` and `axeyum_normalized_sha256`; a non-complete side
requires null. Both fields and the typed side classes are covered by the
existing execution, comparison, cell, and population seals.

## Derived classifier

Invalid state dominates as `invalid-run`; otherwise absent state derives
`not-run`. For two complete sides:

- equal present normalized identities derive `agree-success` for two
  successes and `agree-reject` for two rejections;
- unequal present normalized identities for the same semantic result class
  derive `semantic-mismatch`;
- absent normalization needed for semantic equality derives `unadjudicated`;
- official success against any non-success derives `official-only`;
- Axeyum success against official rejection derives `axeyum-only`; and
- every other valid complete-result pairing derives `unadjudicated`.

The declared comparison outcome must equal this result. A comparison cannot
choose `unadjudicated` to hide a known canonical mismatch.

## Controls

The 23-test complete-parity module now includes:

- positive derivation for all eight outcome classes;
- agreement with different execution-local command/outcome identities but
  equal normalized identities;
- normalized-output mutation with execution/comparison/cell/population seals
  recomputed, which rejects stale agreement as `semantic-mismatch`;
- result-class mutation with all seals/citations recomputed, which rejects
  stale agreement as `official-only`;
- missing normalized identity deriving `unadjudicated` rather than agreement;
- non-complete side records rejecting non-null result class; and
- non-complete sides rejecting non-null normalized identity.

These controls prove schema and classifier behavior only. They do not
implement or validate the future parser, elaborator, kernel, tactic, module,
runtime, server, or Lake normalizers.

## Validation checkpoint

The implementation checkpoint passed:

- five focused result/normalization/coherence tests;
- `python3 -m unittest scripts.tests.test_lean_complete_parity` — 23 tests;
- deterministic complete-parity generation; and
- `git diff --check`.

The full parity-document, link, and differently rooted detached-worktree gates
remain required at the final documentation checkpoint.

## Research basis

Lean's pinned
[test-suite contract](https://github.com/leanprover/lean4/blob/v4.30.0/tests/README.md)
separates expected exit and output behavior. BenchExec's
[result classifier](https://github.com/sosy-lab/benchexec/blob/main/benchexec/result.py)
separates a tool result from correctness, unknown, missing, and error
categories. The [SMT-COMP 2025 rules](https://smt-comp.github.io/2025/rules.pdf)
separately account for semantic answers, `unknown`, abort, errors, and model
validation. R2 applies that separation to Axeyum's existing taxonomy without
adopting any external scoring policy.

## Truth boundary and next work

R2 creates no official or Axeyum outcome, paired cell, performance row,
complete paired-population authority, U2 promotion, axis completion, terminal
gate, or parity credit. TL0.6.3 and TL0.6.4 remain incomplete parents. After
they are accepted, TL0.6.5 M0 must derive the complete layer-expanded
comparison-obligation authority; M1 must then implement each registered
layer-specific canonical normalizer and its semantic/ignored-field mutation
controls before any native attempt can earn a paired outcome.


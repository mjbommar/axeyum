# Lean U2 TL0.6.5 R5 result — normalization axis coverage

Date: 2026-07-23

Status: **accepted bounded relational correction; no process or parity credit**

Plan: [R5 axis-coverage plan](lean-u2-matched-execution-tl0.6.5-axis-coverage-r5-plan-2026-07-23.md)

Preregistration: `42acfaa3`

Normalization-authority checkpoint: `40baa245`

Complete-parity integration checkpoint: `8e794435`

## Result

The terminal registry now enforces the relation that its normalization
contracts already claimed to seal: a paired cell's axis must occur in the
selected contract's `applicable_axes`. Before R5, a fully resealed control
moved a kernel/assurance cell from A1 to A0 without changing its layer or v2
normalizer, and the terminal validator accepted it:

```text
RESEALED_WRONG_AXIS_ACCEPTED=True
```

R5 makes that control reject even after recomputing the execution, comparison,
cell, and bounded-population authority seals. The validator does not infer an
axis from a layer name, population, source family, or outcome.

R5 also closes the registry-level A10 omission. The current
[v3 machine authority](lean-u2-normalization-contracts-v3.json) covers every
terminal axis A0--A11 and adds one `lean-mathlib-ecosystem-v3` profile-level
contract for A10. The immutable [v1](lean-u2-normalization-contracts-v1.json)
and [v2](lean-u2-normalization-contracts-v2.json) authorities remain historical
inputs, not current normalizers.

## Accepted v3 authority

The v3 authority and generated
[summary](generated/lean-u2-normalization-contracts.md) bind:

- ten normalization contracts;
- 76 compared fields and 20 narrowly justified ignored-field rules;
- 96 typed field occurrences: 73 SHA-256 identities, three sealed enums, ten
  nonnegative integers, and ten nonempty strings;
- all twelve terminal axes; and
- fifteen exact contract/axis applicability occurrences.

The new A10 contract selects eight exact identities:

1. `axiom_trust_closure_sha256`;
2. `build_outcomes_sha256`;
3. `declaration_closure_sha256`;
4. `failure_classification_sha256`;
5. `module_outcomes_sha256`;
6. `runtime_tests_sha256`;
7. `tactic_results_sha256`; and
8. `test_outcomes_sha256`.

Source and dependency identity remain common paired-cell fields. Command,
resource, attempt, completion, assurance, and performance evidence remain
independently sealed side records. In particular, functional normalization
does not turn a timing or resource difference into a semantic mismatch.

This is a profile-level projection contract only. It is not a mathlib
population, dependency closure, build, test, tactic run, runtime observation,
or A10 parity result.

## Relational and projection controls

Nine normalization tests establish deterministic v3 sealing and rendering,
exact A0--A11 union coverage, contract-local nonempty/unique/numeric-sorted
axis lists, stale-seal rejection, and exhaustive value controls:

- every one of the 76 semantic-field mutations changes its projection digest;
- every one of the 20 ignored-field mutations preserves its projection digest;
  and
- malformed values reject across all 96 typed occurrences.

Twenty-five complete-parity tests retain the prior population, execution,
outcome, seal, and terminal-claim controls while adding the exhaustive
contract/axis matrix. All 15 registered pairs pass, all 105 unregistered pairs
reject after full resealing, and the sole A10/mathlib pair is among the
positive controls. Authentic v1 and v2 IDs and seals also reject under the v3
terminal authority.

## Validation checkpoint

The accepted checkpoints passed:

- `python3 -m unittest scripts.tests.test_lean_u2_normalization_contracts` —
  nine tests;
- `python3 -m unittest scripts.tests.test_lean_complete_parity` — 25 tests;
- both generators under `--check`;
- `just parity-docs`, including the complete registered Lean/SMT evidence
  suite;
- `just links`; and
- a differently rooted detached replay at
  `/tmp/axeyum-lean-r5-replay.zbOHbk` of all 34 focused tests and both
  authority checks.

The normalization truth line is:

```text
LEAN_U2_NORMALIZATION|contracts=10|compared_fields=76|ignored_rules=20|covered_axes=12|axis_contracts=15|typed_fields=96|sha256=73|enum=3|nonnegative_integer=10|nonempty_string=10|raw_extractors=0|semantic_canonicalizers=0|paired_cells=0|parity_credit=0
```

The terminal truth remains:

```text
LEAN_COMPLETE_PARITY|populations=10|complete_populations=0|axes=12|complete_axes=0|paired_cells=0|gates_satisfied=0|terminal_ready=false
```

No M2.1 native-header process or M2.2--M2.7 external process was launched.

## Portability integration boundary

The ROOT-relative portability repair remains present and validated on this
Lean branch. It is not yet on `main`. At the R5 closure check, remote `main`
was `3969125545372bc81802e381c26c10f2ee0f9e49`, and docs run
[`30029123431`](https://github.com/mjbommar/axeyum/actions/runs/30029123431)
still failed with:

```text
LEAN_PROCESS_ATTEMPT_ERROR|exit-zero-4g: run/spec attribution drift
```

Therefore R5 does not claim that shared `main`, its docs gate, or SMT
ADR-0362's downstream integration dependency is repaired. The branch-local
repair remains documented in the
[portability R1 result](lean-complete-parity-worktree-portability-r1-result-2026-07-23.md).

## Research basis

JSON Schema 2020-12's
[applicator vocabulary](https://json-schema.org/draft/2020-12/draft-bhutton-json-schema-00#section-10.2.2)
distinguishes field-local validation from whole-object conditional relations.
R5 implements only the repository's sealed axis/normalizer relation; it does
not claim general JSON Schema support.

Lean's
[Lake reference](https://lean-lang.org/doc/reference/latest/Build-Tools-and-Distribution/Lake/)
separates packages, dependencies, modules, targets, facets, artifacts, test
drivers, and runtime execution. The pinned mathlib
[README](https://github.com/leanprover-community/mathlib4/blob/v4.30.0/README.md)
directs the full test path through `lake test`. Those separate observable
classes justify an A10 profile contract rather than a file-presence or
single-exit-code proxy.

## Truth boundary and next work

R5 completes normalization-axis coverage, not any terminal axis. Raw official
and Axeyum extractors, semantic canonicalizers, complete comparison
obligations, matched outcomes, paired cells, performance rows, U2 promotion,
completed axes/gates, and Lean parity credit remain absent or zero.

TL0.6.5 execution remains gated on complete accepted TL0.6.3 and TL0.6.4
parents. After those parents exist, M0 must derive the exact layer-expanded
obligation authority and M1 must prove that each raw official/Axeyum adapter
produces the registered selected identities before M2 may authorize a native
attempt.

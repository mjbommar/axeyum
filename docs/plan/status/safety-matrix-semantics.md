# S0 column semantics — evidence is not coverage

<!-- plan-section: lane-status -->

Lane: `safety-matrix-semantics`
Phase: S0 of the trusted-library safety roadmap (ADR-0717)
Decision: [ADR-0795](../../research/09-decisions/adr-0795-the-safety-matrix-measures-per-fact-evidence-and-coverage-is-a-second-axis.md)

**Status:** COMPLETE — audited all nine S0 safety-matrix columns against every
centrally-run gate providing the same protection. Two defects found in opposite
directions; the overstating one is repaired, the understating one is a second
axis the census now reports separately. ADR-0795.

## The finding

Eight of the nine columns ask *"does this fact's own record exercise this
protection"*. They were read as *coverage*. `exact_statement` never asked that
question at all — it reads a ledger-wide manifest — so the census already mixed
the two axes without saying so.

| column | census | true coverage | direction |
|---|---:|---|---|
| `exact_statement` | 2121 | 2121 | correct, wrong axis (S1, ADR-0763) |
| `kernel_theorem` | 1467 | 1956 resolved by S2 | understates by design |
| `per_theorem_footprint` | 59 | 1956 (S2 `guard_forbidden_trust`) | understates by 1903 |
| `env_footprint` | 1863 | 1863 | correct |
| `circularity` | **38 → 14** | 1956 (S2 self + alias) | **OVERSTATED and understated** |
| `semantic_falsification` | 95 | **8 demonstrated** (S3) | **OVERSTATES by 87** |
| `mutation_control` | 15 | not a per-fact protection | mis-shaped |
| `independent_replay` | 8 | not measurable from a fact (S4, ADR-0760) | understates, unquantified |
| `coverage_bearing_checker` | 1443 | 1443 | correct |

**The overstatement is the one to read first.** 24 of `circularity`'s 38 rows
were credited by `kernel_declaration_projection`, which walks no closure —
its own module doc says the projection "must not be confused with a transitive
closure". Every one names a `definition`, which has no proof body to be
circular in, and the committed greps do not even constrain the footprint-size
field. Two further alternatives in the pattern matched **zero** commands.

## Landed changes

| commit | what |
|---|---|
| `0dd554239` | lane opened; premise on record before conclusions existed |
| `839c98204` | `circularity` 38 → 14; `exact_statement` moved to a coverage axis excluded from `protection_count`; the four uncredited gates named in the summary with what each must emit |
| `ba8426aa1` | `scripts/tests/test_safety_matrix.py` — 7 controls, 4 of them mutations the census could not previously fail on |
| this | ADR-0795, index, status |

## Verdict on S1's control repair

Detail moved to [`../notes/safety-matrix-semantics.md`](../notes/safety-matrix-semantics.md).


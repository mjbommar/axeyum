# Claim Label Matrix

This is the consumer-facing label policy for foundational-resource rows and
pack cards. It translates public JSON fields into display labels without
turning educational examples into theorem, benchmark, or parity claims.

Use this with:

- [Trust Boundary Queries](TRUST-BOUNDARY-QUERIES.md) for proof-status and
  result-status drilldowns.
- [Proof Route Query Matrix](PROOF-ROUTE-QUERY-MATRIX.md) for route summaries.
- [Checker Tamper Matrix](CHECKER-TAMPER-MATRIX.md) for corrupted-evidence
  commands and tamper gaps.

The current public summary is:

```text
concept_rows=131
non_template_packs=167
checks=1089
expected_results=not-run:130,sat:557,unsat:402
proof_statuses=checked:393,lean-horizon:130,replay-only:566
solver_reuse=promoted:167
```

## Row Labels

Each check row has two independent axes:

```text
expected_result: sat | unsat | not-run
proof_status: checked | replay-only | lean-horizon
```

Use the pair, not either field alone.

| Result + proof status | Display label | Allowed claim | Do not claim |
|---|---|---|---|
| `sat` + `checked` | checked witness | The finite or encoded claim has a witness/model that is replayed or otherwise checked by the named route. | General satisfiability for a broader theorem family, performance, or solver parity. |
| `sat` + `replay-only` | finite witness replay | The committed finite witness, table, trace, or arithmetic value validates against the pack model. | Proof-object certification or theorem proof. |
| `unsat` + `checked` | checked refutation | The finite or encoded false claim is rejected by a named checked route such as DRAT/LRAT, Farkas, Diophantine, Alethe, QF_BV DRAT, or a checked replay route. | The corresponding unbounded theorem, encoder soundness beyond the named route, or benchmark superiority. |
| `unsat` + `replay-only` | finite rejection replay | The validator recomputes the fixed finite contradiction and rejects the malformed source claim. | Proof-object tamper coverage or independent certificate checking. |
| `not-run` + `lean-horizon` | theorem horizon | The row records a theorem or proof-assistant boundary and the dependency needed to graduate. | A failed solver run, checked SMT evidence, finite replay, or a proved theorem. |
| Any other pair | invalid or future status | Treat as schema drift until a plan update defines the pair. | Silent display or promotion. |

## Pack Labels

Pack cards usually contain several rows. Display all relevant labels instead of
collapsing a mixed pack into a single over-strong badge.

| Pack condition | Primary card label | Secondary chips |
|---|---|---|
| At least one `checked` row | checked evidence pack | show route chips such as `Farkas`, `Alethe`, `QF_BV`, `Bool/CNF`, or `Diophantine` |
| No `checked` rows and at least one `replay-only` row | finite replay pack | show result chips `sat witness` or `unsat replay` |
| At least one `lean-horizon` row | theorem boundary included | show `Lean horizon` as a boundary chip, not as failure |
| Mixed checked/replay/horizon rows | mixed trust story | show every chip needed for the rows being displayed |

Pack-level `solver_reuse=promoted` means the pack has a deliberate solver or
proof feedback disposition. Pack-level `solver_reuse=non-benchmark-horizon`
means the pack has a deliberate non-benchmark disposition until another proof
or solver artifact exists. Neither means the pack is a benchmark, theorem
proof, or parity result.

## Route Labels

Use route labels only after checking the row's proof status.

| Route text | Label | Boundary |
|---|---|---|
| `boolean-cnf-lrat` or `boolean` | DRAT/LRAT checked CNF | Checks the finite CNF proof object, not arbitrary source-to-CNF encoders. |
| `qf-bv-bitblast` or `qf-bv` | QF_BV DRAT checked | Checks the generated CNF proof; width must be part of the claim. |
| `qf-lia-diophantine` or `Diophantine` | integer certificate checked | Checks the concrete linear integer obstruction. |
| `qf-lra-farkas` or `Farkas` | rational Farkas checked | Checks exact linear rational infeasibility. |
| `qf-uf-congruence-alethe` or `Alethe` | congruence/Alethe checked | Checks equality/congruence conflict evidence for covered shapes. |
| `finite-model-replay` or `finite-replay` | finite replay | Recomputes a fixed finite source claim; no separate proof object. |
| `lean-horizon-template` or `lean` | Lean horizon | Marks theorem work that is not yet a checked resource proof. |

## Copy Rules

Prefer short labels in generated pages or UI cards:

- `checked witness`
- `checked refutation`
- `finite witness replay`
- `finite rejection replay`
- `theorem horizon`
- `mixed trust story`

Then put the exact route in a secondary field:

```text
checked refutation - QF_LRA/Farkas
finite witness replay - finite table
theorem horizon - compactness
```

Do not write:

- "proved" unless the row names a checked proof/evidence route for the exact
  finite or encoded claim being displayed.
- "Lean certified" unless a concrete Lean artifact is checked and the relevant
  recipe says the route is Lean-covered.
- "benchmark" or "faster than Z3/cvc5" unless the row is part of a committed
  benchmark corpus with measured results.
- "general theorem" when the evidence is a finite replay, fixed-width BV row,
  bounded trace, or exact rational shadow.

## Query Checks

Use these commands to audit label inputs:

```sh
python3 scripts/query-foundational-resources.py labels

python3 scripts/query-foundational-resources.py labels \
  --scope rows \
  --label "checked refutation" \
  --require-any

python3 scripts/query-foundational-resources.py labels \
  --scope packs \
  --label "mixed trust story" \
  --require-any

python3 scripts/query-foundational-resources.py summary

python3 scripts/query-foundational-resources.py checks \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --proof-status replay-only \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --proof-status lean-horizon \
  --expected-result not-run \
  --require-any
```

For route-specific display labels, drill into a row after choosing the label:

```sh
python3 scripts/query-foundational-resources.py checks \
  --route Farkas \
  --proof-status checked \
  --expected-result unsat \
  --require-any
```

## Review Checklist

Before a consumer displays a label:

1. Read `expected_result`.
2. Read `proof_status`.
3. Read the route or validation label.
4. Check whether the row is finite, bounded, computable, numerical, or a
   theorem horizon.
5. Link to the pack or learner page for limitations.
6. Avoid benchmark, parity, and theorem language unless separate evidence
   proves those stronger claims.

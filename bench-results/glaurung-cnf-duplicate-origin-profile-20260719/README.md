# Glaurung cold duplicate-clause origins — 2026-07-19

Status: accepted fixed-population diagnostic; one follow-on experiment selected

ADR-0260 preregistered the exact first-origin/duplicate-origin matrix and its
50% / 10-query / 50% selection rule before artifact-v36 implementation or
observation. The implementation was committed before the measurement as clean
detached Axeyum revision
`1bce10fd5eb6b96fc6eff692434e7d8e7d79a14b`.

## Population and gates

- corrected-wide-v3 representative manifest SHA-256
  `7818686bc26c56646775eb2f557e1e4edb36e4e8254a8c410fe0333da1ba2064`;
- 162 raw QF_BV queries: 88 SAT and 74 UNSAT;
- exact family counts: arithmetic 36, comparison 12, mixed 7,
  register-slice 52, slice-partial 54, trivial 1;
- 162/162 manifest agreements, 162/162 in-process Z3 agreements, 88/88 SAT
  original-model replays, and zero Unknown/unsupported/error/disagreement; and
- all construction, origin-matrix, owner-relation, length, literal, aggregate,
  family, and outcome identities true.

The retained files are:

- [`artifact.json`](artifact.json), SHA-256
  `aeba00c5defb4a32264e0d711775720040212671ab53234018e2b16f0eb47f15`;
- [`analysis.json`](analysis.json), SHA-256
  `17134ac51497b024303435b42884a3817e1654fcb3a88ba9b5668786447c0066`.

Artifact identity is version 36, config hash `3031046d19deeb81`, and corpus hash
`23932b876da74bd1`.

## Exact result

All 119,260 ADR-0259 duplicates and their 229,651 canonical literals are
attributed. They partition as 11,997 unit clauses, 107,117 binary clauses, and
146 clauses of length four or greater; there are no empty or ternary duplicate
clauses.

Exactly one matrix cell passes the preregistered rule:

| First origin | Duplicate origin | Owner | Duplicates | Share | Queries | Largest-query share |
|---|---|---|---:|---:|---:|---:|
| `root/and_tree/forward/parity` | same | same | 107,000 | 89.7199% | 29 | 9.9738% |

All 107,000 are binary clauses and contain 214,000 canonical literals. The
cell partitions into 83,172 slice-partial SAT, 14,894 register-slice SAT, and
8,934 register-slice UNSAT duplicates. No other family/outcome contributes.

The next largest cells are same-owner root AND-tree literal emission (11,309,
9.4826%) and cross-owner root AND-tree literal emission (675, 0.5660%). No
other cell reaches 0.13% of all duplicates.

## Decision and limits

ADR-0260 selects no production optimization. Its fixed rule authorizes one
separately preregistered experiment: ADR-0261 will eliminate only repeated
semantically identical private parity leaves within one positive direct-root
AND tree, before generating their clauses. The existing global clause index
already drops the clauses, so the candidate must preserve byte-identical final
CNF, roots, lift maps, verdicts, and replay.

Counts remain diagnostic. Avoiding 89.7199% of duplicate attempts does not
imply a comparable wall-time improvement. ADR-0261 requires repeated unprofiled
end-to-end evidence and permits a clean rejection.

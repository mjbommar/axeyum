# SMT-COMP repaired P0 combined comparison

Status: complete, bounded repaired-P0 comparison

This is a correctness and decision-coverage map, not an official
SMT-COMP result or a cross-scope performance ranking.

## Artifact identity

- JSON file SHA-256: `265c9176dc3fde4b1fac6d1633ac415bdec6f2a206f9a507dff6f066b5c5e1a9`
- JSON record SHA-256: `68b12c47ea852720bedd4161bac37058e779dee0668125a48194c1dabb1ad2dc`
- preparation completion SHA-256: `8d9145b2673ee10bf7c38990c20301f13323cfe4ab02c9946b403d0d2e4f4261`

## Native cell scopes

| Solver | Rows | Decisions | `sat` | `unsat` | `unknown` | No verdict | Known contradiction |
|---|---:|---:|---:|---:|---:|---:|---:|
| axeyum | 1,810 | 914 | 450 | 464 | 280 | 616 | 0 |
| cvc5 | 1,810 | 1,513 | 672 | 841 | 0 | 297 | 0 |
| bitwuzla | 1,305 | 1,221 | 432 | 789 | 0 | 84 | 0 |

Bitwuzla's rows are exactly the 1,305-row FP-family subset. The other
505 rows are exactly QF_AUFLIA and are compared only between Axeyum and cvc5.

## Per-logic decision coverage

| Logic | Solver | Rows | Decisions | `sat` | `unsat` | `unknown` | No verdict |
|---|---|---:|---:|---:|---:|---:|---:|
| QF_ABVFP | axeyum | 525 | 194 | 58 | 136 | 62 | 269 |
| QF_ABVFP | cvc5 | 525 | 401 | 87 | 314 | 0 | 124 |
| QF_ABVFP | bitwuzla | 525 | 521 | 97 | 424 | 0 | 4 |
| QF_AUFLIA | axeyum | 505 | 253 | 128 | 125 | 134 | 118 |
| QF_AUFLIA | cvc5 | 505 | 503 | 262 | 241 | 0 | 2 |
| QF_BVFP | axeyum | 505 | 375 | 203 | 172 | 44 | 86 |
| QF_BVFP | cvc5 | 505 | 440 | 216 | 224 | 0 | 65 |
| QF_BVFP | bitwuzla | 505 | 500 | 226 | 274 | 0 | 5 |
| QF_FP | axeyum | 275 | 92 | 61 | 31 | 40 | 143 |
| QF_FP | cvc5 | 275 | 169 | 107 | 62 | 0 | 106 |
| QF_FP | bitwuzla | 275 | 200 | 109 | 91 | 0 | 75 |

## Pairwise decision projections

Only `sat` and `unsat` count as decisions. `unknown` is an observed
response but remains a non-decision.

| Population | Solvers | Rows | Both agree | Left only | Right only | Neither | Disagree |
|---|---|---:|---:|---:|---:|---:|---:|
| all 4 logics | axeyum / cvc5 | 1,810 | 862 | 52 | 651 | 245 | 0 |
| FP-family | axeyum / bitwuzla | 1,305 | 659 | 2 | 562 | 82 | 0 |
| FP-family | cvc5 / bitwuzla | 1,305 | 1,007 | 3 | 214 | 81 | 0 |
| QF_AUFLIA | axeyum / cvc5 | 505 | 253 | 0 | 250 | 2 | 0 |

## Three-solver FP-family projection

| Rows | Three decide | Two decide | One decides | None decide | Disagree |
|---:|---:|---:|---:|---:|---:|
| 1,305 | 609 | 448 | 169 | 79 | 0 |

Sole decider counts: axeyum 2, cvc5 3, bitwuzla 164.
Sole non-decider counts: axeyum 398, cvc5 50, bitwuzla 0.

## Bounded verdict

All exact populations account completely, with zero known-status
contradictions and zero cross-solver `sat`/`unsat` disagreements.
The data supports per-scope capability comparison only. It does not
support combining the 1,305-row and 1,810-row populations into one
score or claiming general SMT-COMP parity.

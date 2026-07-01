# Checks

## `category_witnesses`

Replays representative category/program rows:

- `resident` and `in_state` applicants in `emergency_housing` receive priority;
- `nonresident` applicants in `emergency_housing` do not;
- local applicants in `standard_benefit` do not receive priority.

Evidence: finite witness replay.

## `equivalent_categories_same_priority`

Asks for `resident` and `in_state` to be equivalent while the same
`emergency_housing` priority function returns different results. The intended
QF_UF/Alethe route should reject this by congruence.

Evidence today: explicit proof gap with source-linked QF_UF SMT-LIB artifact
[`smt2/equivalent-categories-same-priority-qf-uf-conflict.smt2`](smt2/equivalent-categories-same-priority-qf-uf-conflict.smt2).

## `implementation_equivalence_qf_uf_gap`

Asks for the formal model and implementation to disagree after both respect
the same category equivalence. This is the rules/law implementation-equivalence
shape that needs QF_UF/Alethe rather than only Bool/QF_LIA or QF_LRA/Farkas.

Evidence today: explicit proof gap with source-linked QF_UF SMT-LIB artifact
[`smt2/implementation-equivalence-qf-uf-conflict.smt2`](smt2/implementation-equivalence-qf-uf-conflict.smt2).

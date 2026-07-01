# Checks

## `allocation_witnesses`

Replays representative allocation triples, including the exact floor split
`1/2, 1/4, 1/4`, a clinic-heavy compliant split, and malformed low-shelter,
over-admin, and over-budget rows.

Evidence: finite witness replay.

## `total_budget_respected`

Asks for the same total allocation to equal both `1` and `5/4`. The source
formula requires exact balance, so the obligation is inconsistent.

Evidence: checked QF_LRA/Farkas fixture
[`smt2/total-budget-respected-farkas-conflict.smt2`](smt2/total-budget-respected-farkas-conflict.smt2).

## `shelter_minimum_respected`

Asks for a shelter share fixed at `1/4` while the source floor requires
`shelter_share >= 1/2`. The obligation is inconsistent.

Evidence: checked QF_LRA/Farkas fixture
[`smt2/shelter-minimum-respected-farkas-conflict.smt2`](smt2/shelter-minimum-respected-farkas-conflict.smt2).

## `clinic_minimum_respected`

Asks for a clinic share fixed at `0` while the source floor requires
`clinic_share >= 1/4`. The obligation is inconsistent.

Evidence: checked QF_LRA/Farkas fixture
[`smt2/clinic-minimum-respected-farkas-conflict.smt2`](smt2/clinic-minimum-respected-farkas-conflict.smt2).

## `admin_cap_respected`

Asks for an administrative share fixed at `1/2` while the source cap requires
`admin_share <= 1/4`. The obligation is inconsistent.

Evidence: checked QF_LRA/Farkas fixture
[`smt2/admin-cap-respected-farkas-conflict.smt2`](smt2/admin-cap-respected-farkas-conflict.smt2).

## `implementation_equivalence`

Asks for a mismatch between the formal model and the executable interpretation
when both encode the same rational allocation rule. The mismatch is
inconsistent.

Evidence: checked QF_LRA/Farkas fixture
[`smt2/implementation-equivalence-farkas-conflict.smt2`](smt2/implementation-equivalence-farkas-conflict.smt2).

# Notes: 385-l0-s3-semantic-controls

Detail moved out of [`../status/385-l0-s3-semantic-controls.md`](../status/385-l0-s3-semantic-controls.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

1. The numerics detector matched the literal `NEGATIVE CONTROL` and reported
   two in-tree scripts as carrying none. Both carry several, spelled
   `GENUINELY FAILS`. 0 → 14 and 0 → 6 once fixed. A gate manufacturing a
   finding about its own subject.
2. `drop-congruence-check` reported `survived` because it never removed the
   guard it names. Now killed at 1,174 instances. A survivor is as easily a
   broken mutation as a weak guard.
3. `test_a_fixture_that_executed_nothing_is_refused` needed a second fixture
   with a nonzero count, or the pack-total clause covers for a deleted
   per-fixture clause and the mutation survives.

## Handoff — what I did NOT do, and what is a hypothesis

Everything below is what my route did not reach, not a claim that it is hard.

- **I did not audit the 84 undemonstrated controls one by one.** I sampled
  them (34 `cas-certificate`, 17 `smt-term-level`, 16 `kernel-lean`, 10
  `smt-clausal`, 7 `search-certificate`) and read a handful. Whether any is
  vacuous is open; treating the 84 as a vacuity count would be exactly the
  crude-classifier error this phase exists to name.
- **I found no fact I can demonstrate is vacuous.** The one I expected to be —
  `F:nat-totient-dvd-totient-mul-prime`, whose family produced the vacuous
  composite control — turns out to be honest: its evidence explicitly names the
  **transposed** direction, failing at 142 pairs, as the control that
  discriminates. The repair had already landed there. That is a real answer,
  not an absence of looking, but it is one fact.
- **The pack does not reach a proof term.** These are semantic checks over
  small domains. S4's Lean replay and S5's kernel differential are the checks
  that reach the term, and nothing here substitutes for them.
- **The `vacuous` class is judgement.** Both vacuous fixtures are controls that
  really shipped here; nothing asserts they are the only two.
- **I did not run `scripts/check-fast.sh` or any cargo gate.** The gate I added
  is pure Python and runs in about two seconds; the aggregate re-run is the
  coordinator's.

## Paths owned by this lane

`scripts/semantic_control_fixtures.py`,
`scripts/check-semantic-control-fixtures.py`,
`scripts/tests/test_semantic_control_fixtures.py`,
`artifacts/semantic-controls/`, ADR-0752, this file. One registration line each
in `scripts/check.sh`, the `justfile`, and `scripts/tests/mutation_controls.py`.

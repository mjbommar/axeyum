# 385 — L0/S3: automatic semantic falsification

<!-- plan-section: lane-status -->

Lane: `l0-s3-semantic-controls`
Phase: ADR-0717 L0, roadmap phase **S3** — complete.
Decision: [ADR-0752](../../research/09-decisions/adr-0752-semantic-controls-are-a-retained-fixture-pack-not-a-review-step.md)

## Status

S3's exit is met and gated. `scripts/check-semantic-control-fixtures.py`
executes the retained fixture pack in
`scripts/semantic_control_fixtures.py`, pins its shape in
`artifacts/semantic-controls/fixture-pack.json`, and is registered in **both**
`scripts/check.sh` and the justfile.

    fixtures=13|executed=9742|mutations=19|killed=18|also_true=1|survived=0
    load_bearing=8|semantic_falsification=91|proved=2117
    AUTOGENESIS_HOLDOUT_ISOLATION|held_out=116|files_scanned=1109|
      settled=0|references=0|verdict=PASS

**No fact was edited.** Not `epistemic_status`, not `proof_route`, not
`axiom_footprint`, not `formal.statement`.

## The pack

13 fixtures, each a real defect this session produced and caught, or the valid
control one line away from it: the coprimality-independence claim false at
26/26 non-coprime pairs; the composite totient control vacuous by mathematics;
the least-number-principle control that passed on a sort mismatch; the Pratt
certificate for 91 that only completeness rejects; the CRT certificate (9, 24)
that only leastness rejects; the NRA bound recording a constant but not
strictness, over a satisfiable query.

Three classes. `false` must be refuted. `vacuous` must produce **zero**
discriminating instances — the fixture asserts the zero, not its own
greenness. `valid` must be accepted, must discriminate, and must kill at least
one mutation. **Zero executed cases is failure** per fixture, for the pack, and
for an empty pack.

An unfalsified mutation declared `also_true` is classified for review, never
failed. One such: `eq-to-le` on the totient identity, where the weakened
statement is true.

## The honest count

**8 of 2,117** proved facts have a control this gate demonstrated would fail if
the property failed. 91 is the upper bound — S0's `semantic_falsification`
column, which counts facts carrying a semantic evidence row whether or not it
discriminates. 1,992 is what `kind` would give, and the census never reads
`kind`: it reads S0's generated column, which classifies from `supports`.

The 84-fact difference between 91 and 8 is **not** 84 vacuous controls. It is
84 controls not demonstrated either way, and the summary keeps those apart.

## Mutation kill sets

21 mutations through `scripts/tests/mutation_controls.py
semantic-control-fixtures`, against 28 controls. **Every one `killed 1`,
naming a distinct test. No survivors, nothing unmeasured.**

## Three defects found in the tools, not the subject

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

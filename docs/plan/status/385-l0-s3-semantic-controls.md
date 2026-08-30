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

Detail moved to [`../notes/385-l0-s3-semantic-controls.md`](../notes/385-l0-s3-semantic-controls.md).


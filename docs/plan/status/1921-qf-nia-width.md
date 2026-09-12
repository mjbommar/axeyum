# Lane: qf-nia-width — is QF_NIA's `overflowed at width 32` an escalation problem?

<!-- plan-section: lane-status -->

**DO NOT BUILD the width escalation, sized (`DONE`, qf-nia-width, 2026-09-12).**
[ADR-1921](../../research/09-decisions/adr-1921-the-int-blast-width-escalation-is-measured-and-not-shipped.md)
· [measurement](../../research/03-measurements/qf-nia-is-not-a-width-problem-2026-09-12.md)
· data `bench-results/qf-nia-width-20260912/`.

The gap log's QF_NIA row said half of a 14-file sample was one cap. Over **all
110** winnable files the width family is **26 (24%)**, behind the preprocessed
dispatch timeout (41) and the CNF clause budget (30). An interleaved one-binary
A/B (arms alternating per file, 220 solves) gives the escalation **0 gains, 0
losses, 0 disagreements, +4.6% wall** — and it turns 23 precise `overflowed at
width 32` diagnoses into uninformative `Timeout`/`Watchdog`. Not a clock problem
either: at **150 s** the escalation decides 3 of the 23 and the **baseline at the
same 150 s decides the same three files with the same three verdicts**, so the
escalation contributed zero; **14 of the other 20 overflow at width 64**, the
blaster's hard ceiling. 128 is unreachable without replacing the `i128` model
read-back.

Landed anyway: the *ability* to re-run this on another population without a
rebuild (`AXEYUM_INT_BLAST_ESCALATION_MAX_WIDTH`), shipped equal to the existing
ladder top so behaviour is byte-identical, clamped to what the blaster accepts,
with four tests pinning the shipped sequence and the append-only property.

**Where a QF_NIA lane should go next**: the *preprocessed dispatch timeout* (41
of 110). The CNF clause budget (30) already has a measured negative — lifting it
by the estimator's own 9.4x slack decides 0 of 49
([notes](../notes/118-nia-diagnosis.md)). One unmeasured hypothesis this lane
leaves standing: `blast_integers` emits a no-overflow constraint for `int_mul`
and for **nothing else**, so the replay failures that survive are additive
wraparound, and the analogous additive constraint is sound by the same argument.

<!-- plan-section: landed-changes -->

| 2026-09-12 | `57f1363e0` | QF_NIA width escalation made measurable: `int_blast_ladder_widths` extracted, `INT_BLAST_ESCALATION_MAX_WIDTH` shipped equal to the existing ladder top, `AXEYUM_INT_BLAST_ESCALATION_MAX_WIDTH` lever, clamp to `MAX_INT_BLAST_WIDTH`, four tests. Zero behaviour change. |

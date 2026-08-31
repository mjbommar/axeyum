# Lane: trust-closure-equivalent — the L0 trust-closure EQUIVALENT-IN-CLOSURE failure

<!-- plan-section: lane-status -->

**Done (`trust-closure-equivalent`, 2026-08-31).**
`scripts/check-trust-closure.py` is green again, resolved the way the gate's own
message directs — the disclosed backlog with the duplicate acknowledged — and
the direction rule that was silently violated is now a guard rather than a
sentence in an ADR. Decision:
[ADR-1265](../../research/09-decisions/adr-1265-canonicity-follows-the-proof-not-the-date.md).

`Rat.int_right_distrib` and `Int.add_mul` are one proposition under two names.
ADR-1170's shape-duplicate repair made the Rat declaration forward to
`Int.add_mul`, which moved the pair out of ADR-0790's INDEPENDENT bucket
(canonical = earlier `provenance.date`) into its DISCLOSED bucket (canonical =
the member REACHED IN the other's closure) — inverting the canonical
designation without touching either fact. So canonicity moved to
`F:ml430-int-add-mul-66aa025b` and `F:rat-int-right-distrib` now carries
`equivalent_to`. The declaration stays (14 consuming call sites); the FACT is
the duplicate. Nothing deleted, nothing retracted (ADR-0542); `retracted=0`
before and after.

**Neither headline number moves**, which is the point: FACTS SETTLED 2253,
facts carrying `equivalent_to` 20, DISTINCT PROPOSITIONS ESTABLISHED 2233 —
identical before and after. The pair was already collapsing to one proposition;
only which fact id a reader is pointed at changed, and it now points at the one
whose proof term does the work.

*The gap a disclosure row alone would have left.* ADR-0790 states the
canonical-direction rule and nothing enforced it.
`guard_unlabeled_duplicate_pair` counts canonical members and cannot see a
direction; `check-trust-closure.py`'s `guard_alias_occurrence` never reads
`equivalent_to`, so the disclosure silences it whichever way canonicity points.
Both gates were green on the inverted state. New guard
`canonical_is_the_dependency` (`check-proposition-duplication.py`) reads the
transitive closure of the admitted term and rejects a canonical member that
reaches a marked class-mate. Measured over all 15 identity classes: 14 have a
REACHES relation, 13 put canonicity on the reached member, and this was the
only inversion.

*Proof the gate still fires,* against the shipped tree with a captured
projection of 2,711 declarations — removing the new row reports
`EQUIVALENT-IN-CLOSURE` for `F:rat-int-right-distrib`; removing a different
pre-existing row reports it for THAT pair and not this one; a row that no longer
occurs reports `STALE-DISCLOSURE`. The new guard, run against the pre-fix ledger
reconstructed from `HEAD~1`, rejects with `CANONICAL-IS-NOT-THE-DEPENDENCY`
while every other guard stays at 0. Controls: proposition-duplication 11 cases /
10 mutations, trust-closure 17 cases / 15 mutations, each killing exactly one.

**`unresolved=90` — reported, not fixed, and it is ONE away from firing.**
These are kernel-route settled facts whose declaration `subject_of` cannot
identify; they count toward `kernel_facts` but are not SUBJECTS, so three of
trust-closure's four guards never examine them. Only **9 of the 90** are
deliberately unresolvable (7 explicit `"kernel_theorem": null`, 2 umbrella
facts). The other **81 are under-annotated**, and mechanically so — sampled
facts carry evidence rows whose `id` spells the declaration
(`kernel-CPoint.cauchy_schwarz`) while `kernel_declaration` is `null` and
`formal.kernel_theorem` is absent. It IS indirectly enforced: `resolved /
kernel_facts` is 0.958430 against `min_ratio` 0.9579, which permits at most
**91** unresolved. So 90 is not drift — it is 90 of a permitted 91, and the next
kernel-lean fact landing without naming its declaration turns an L0 gate red
with a message reading as a population-floor breach rather than a missing
annotation. ADR-1005 already did this binding work for 660 subjects; the same
treatment for these 81 is the queue item.

*Also found, out of scope, recorded so it is not rediscovered:*
`crates/axeyum-lean-kernel/src/creal/sqrt.rs` carries a private local
`fn int_right_distrib` re-deriving the same chain inline — a THIRD copy of this
proposition that no identity class can see, because it declares nothing
(CLAUDE.md's hiding place 2). And `check-trust-closure.py --update` rewrites
`artifacts/trust-closure/population.json` while DROPPING its hand-written
`ratio_floor_note`, the paragraph telling the next lane not to lower that floor;
that file was deliberately restored to `HEAD` rather than committed.

<!-- plan-section: landed-changes -->

| 2026-08-31 | `1669fab4` | trust-closure: canonicity moved to the dependency; disclosed pairs 13 -> 14; the fact's call-site count corrected to 14, all in `rat_prelude/` |
| 2026-08-31 | | `guard_canonical_is_the_dependency` + its control case and mutation; ADR-1265 |

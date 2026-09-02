# Lane: partition-gates-green — close the two red partition gates, or size what is left

<!-- plan-section: lane-status -->

**partition-gates-green (`DONE`, partition-gates-green, 2026-09-02).**
One of the two red partition gates is green and the other has a smaller, truer
subject. [ADR-1563](../../research/09-decisions/adr-1563-the-bootstrap-lemma-is-not-a-leak-and-the-stale-exemption-is-retired.md)
carries the reasoning; the numbers are below. Exactly one gate in the whole
partition table changed state against a `main` snapshot, and it changed the
right way.

**The bootstrap lemma is not a leak — baseline 198 -> 153.** 45 of the 198
baselined crossing edges point INTO `F:nat-zero-add` (23) or `F:nat-mul-one`
(22), which ARE the whole `longitudinal` partition, pinned to exactly those two
by `check-autogenesis-nursery.py:426`. A new per-edge amendment class
`depends-on-longitudinal-bootstrap` covers them. Three properties keep it from
being ADR-1546's growing exemption at a finer unit: the class is **re-derived**
by `class_complaint` from the live manifests (an amendment claiming it for a
non-longitudinal target is reported and NOT honoured, as is an unrecognised
class name); it is **direction-specific**, so `longitudinal -> evaluation` — a
drawn result pulled into the regression chain — can never carry it; and
`--record-baseline` now **excludes** honoured amendments, without which the
edge would sit in both lists and deleting the amendment would change nothing
observable. `check-autogenesis-nursery.py` contracts the same amendments out of
its component adjacency through the edge gate's OWN loader, not a second
hardcoded rule — a hardcoded rule would have made its longitudinal-overlap
check structurally unable to fail.

**Two exemptions retired — 7 -> 5.** The 274-member cross-population entry
ADR-1546 measured growing 228 -> 230 -> 258 -> 274 (already stale on `main`),
and an 11-member v1 entry whose component crossed train/development only
because the two bootstrap lemmas fused it; contract them out and the
nine-member residue does not cross at all. Deletions only, both files
round-tripped byte-identically first.

**The count of crossing components rose 3 -> 5, and that is the honest
direction.** The 305-member blob was fusing two dev/train crossings (4 and 2
members) through the bootstrap lemmas and hiding them — "a stable number can be
stably wrong", with a catch-all absorbing items nobody counted. The mass is the
number that fell: largest component 305 -> 287, facts in a crossing component
319 -> 307, violation TYPES in the cross-population arm 3 -> 1, and the v1 arm
is green.

**The producer violation could not be retired, and the reason is mechanical.**
`check-autogenesis-fact-operation.py` pins `operation_sha256 = digest(operation)`
inside the evidence of all three facts `authoritative-mathlib-nat-modeq-
remainder-family-v1` admitted — live `cc868669…`, exactly what the facts
record, and adding one `lifecycle` key moves it to `d610b146…`. A contract is
prospective and can be retired; an operation is a **receipt** (ADR-0602) and is
immutable by construction. So: a dated grandfather as a CLOSED LIST IN SOURCE,
with both its properties re-derived (`grandfather_holds`) — every covered
development fact SETTLED, and every one of them pinning THIS operation. A new
operation still fails, driven by its own control.

**Two corrections to the handoff, measured.** The operation landed `9943ae6bd`
(2026-08-26), not 2026-08-27; and it was NOT "before any rule forbade it" —
`check-development-partition.py` shipped `50307d833` on 2026-08-22, four days
earlier and already in `check.sh` and the `justfile`, with all three facts
already `partition: development`. The gate was red and it landed anyway.

**THE REFUSAL: the remaining 153 crossings are not amended.** The brief's
premise that "train is the non-evaluation partition" contradicts the committed,
`before-target-outcomes` split policy —
`required_evaluation_partitions: [train, development, held-out]` and
`EVALUATION_PARTITIONS = {"train", "development", "held-out"}`. Writing 64
`development -> train` amendments would be amending the gate to disagree with
the preregistered split, at a finer unit than the exemption ADR-1546 refused,
which is the same act rather than a better one. The 6 held-out-endpoint
crossings are refused a second, independent way: they are **structurally
un-amendable**, because an amendment names its endpoints in plain text and
`partition-edge-amendments-v1.json` is inside
`check-autogenesis-holdout-isolation.py`'s scan set (verified by enumerating
`scan_targets()`: 1121 files, the amendments file and the baseline among them).
ADR-1550 already paid for this — its first baseline was six such breaches.

**Two findings outside the brief.** `nursery-v1.json` is a GENERATED file whose
generator emits no `component_split_exemptions` key at all, so
`create-autogenesis-mathlib-nursery-split.py --check` — a registered `check.sh`
step — has been red on `main` since the first exemption was added; deleting one
made the diff smaller and did not fix it. And `nursery-v2-extension.json` seals
itself: the deletion broke `extension_sha256` and took
`gen-autogenesis-nursery-refill.py --check` from exit 0 to exit 1 until it was
recomputed with the generator's own `digest`. Found by running the whole
partition-gate table against a `main` snapshot rather than only the two gates
in scope.

**Mutation: every new guard dies alone.** `partition-edges` 25 tests, M12/M13/
M14 one kill each, M1–M11 unchanged at one apiece.
`nursery-split-exemption-guards` 14 tests, N1/N2/N3 one kill each — N2 does not
delete the contraction, it makes it *undirected*, which is the mutation that
would clear the leaking direction along with the benign one.
`development-partition` 15 tests, all three grandfather mutants one kill each;
two PRE-EXISTING mutants had regressed to 2–4 kills and both causes are fixed
rather than documented away (`dev_only` hoisted out of the mutated branch; the
`committed tree passes` test deleted, since a live-ledger test dies under every
mutant of every guard). `development-without-train rule` still kills five, and
that one is structural — three of the five ARE the grandfather controls, and a
grandfather has no meaning outside the rule it excuses.
`check-control-registration.sh`: `controls=52 orphans=0`, exit 0.

**Gate table (every partition gate, `main` snapshot vs here).** One row
changed:

| gate | main | here |
| --- | --- | --- |
| `check-development-partition` | 1 | **0** |
| `check-partition-edges --baseline` | 0 | 0 (baseline 153, not 198) |
| `check-autogenesis-nursery` | 1 | 1 (3 violation types -> 1) |
| `gen-autogenesis-nursery-refill --check` | 0 | 0 (regressed and repaired mid-lane) |
| `check-autogenesis-holdout-isolation` | 0 | 0 |
| `check-holdout-closed-evaluation` / `-adjacency` / `-adjacency --self-test` | 0 | 0 |
| `check-autogenesis-holdout-contamination` | 0 | 0 |
| `nursery-components --check` | 0 | 0 |
| `mathlib-nursery-review --check` | 0 | 0 |
| `validate-facts`, `validate-autogenesis-operations` | 0 | 0 |
| `mathlib-nursery-split --check` | 1 | 1 (pre-existing, see findings) |
| `nursery-dispatch-baseline --check` | 1 | 1 (pre-existing) |
| `propose-nursery-refill` | 1 | 1 (pre-existing) |
| `attest-nursery-surface` | 1 | 1 (pre-existing, a Lean attestation) |
| `tests/test_check_autogenesis_nursery` | 1 | 1 (pre-existing; its `LiveManifestTests` reads the committed manifests) |
| `tests/test_check_autogenesis_holdout_isolation` | 1 | 1 (pre-existing) |
| every other control suite listed in `check.sh` | 0 | 0 |

**What is left for the next lane.** The 153 baselined crossings are ADR-1546
option 1's work — the re-partition — and ADR-1551 already recorded why it is
hard. Nothing here moved a row between partitions, named a held-out row's
outcome, or touched a held-out fact.

<!-- plan-section: landed-changes -->

| 2026-09-02 | partition-gates-green | `depends-on-longitudinal-bootstrap` amendment class; partition-edge baseline 198 -> 153 |
| 2026-09-02 | partition-gates-green | two component exemptions retired (7 -> 5); nursery v1 arm green, cross-population 3 violation types -> 1 |
| 2026-09-02 | partition-gates-green | `check-development-partition.py` green via a re-derived, dated grandfather; retirement refused as mechanically impossible |
| 2026-09-02 | partition-gates-green | ADR-1563; 9 new controls, 6 new mutants, two pre-existing multi-kill regressions repaired |

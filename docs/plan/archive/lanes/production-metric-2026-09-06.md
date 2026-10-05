# Lane: production-metric — a production number that can see the producer channel

<!-- plan-section: lane-status -->

**Your lane's block (`DONE`, production-metric, 2026-09-06).** ADR-1679. The
"hand proofs retired" total read **67** for three days while roughly two hundred
proved facts landed and zero retirement commits touched the kernel crate. The
cause is structural: the work moved into producers that EMIT theorems nobody
ever wrote by hand, so there is no hand proof to retire and a metric defined as
"hand proofs deleted" is blind to the channel that replaced it. The rule this
lane records is that **a production metric must be able to see every channel
that produces, or it will read flat while the system accelerates.**

**The new number.** `scripts/measure-producer-channel.py`, three layers, each
printing its own coverage line and its blind spots on every run:

| Layer | Measured 2026-09-06 |
| --- | --- |
| L1 site census | 38 EMIT, 50 ASSIST, 44 CONFIG producer entry-point calls in the kernel crate; **0 unclassified** (an unclassified entry point is an ERROR, not an "other" bucket) |
| L2 name resolution | 3,735 field→leaf bindings EXTRACTED, never guessed — 1,808 (48.4%) have a leaf differing from the field; **92.1%** of EMIT sites resolve |
| L3 ledger join | **21** proved facts whose `formal.kernel_theorem` a producer emitted, against 2,455 proved facts carrying that field |

L3 is a lower bound by construction: ambiguous leaves dropped, ASSIST not
joined, bridge-routed producers attributed to the bridge.

**What it cannot see, and the one field that would fix it.** The ledger's
`provenance.established_by` names the PRELUDE BUILDER
(`axeyum-lean-kernel build_nat_prelude`) on all 2,963 facts, never the producer,
so L3 has to reach through Rust source text to answer a ledger question. One
field on one path closes it: **`fact.provenance.produced_by : string | null`**,
`null` meaning hand-authored as an assertion rather than an absence, written
where a lane already fills in `formal.kernel_theorem`. `provenance` is
`additionalProperties`-open, so a lane can start recording it today; a later ADR
should make it required.

**Held-out family price.** `scripts/price-holdout-family.py`. Blind population
**20 families / 206 rows**; **9 families spent in 14 days** (0.64/day, ~31 days
of runway); **one family costs 10 propositions = 4.9% of remaining rows**, with
no partial spend — naming ONE row costs what proving all ten costs. Two of the
nine spends were exactly that: an id in a producer contract's `non_examples`
list. The script never prints a held-out id and guards its own output for one.
Population derived by the isolation gate's own rule and cross-checked against
it: 206 = 206.

**Two derivation traps, measured.** Amendments OVERRIDE the manifests'
preregistered `family_partitions` — `natural-elementary-bounds` and
`discrete-step-and-counting-bounds` still read `held-out` there and are
`development` by amendment, so the preregistration overcounts by two families.
And `check-holdout-adjacency.py`'s 20 rows are one per DRAW, not an inventory of
what is held out; they coincide at 20 today and nothing makes them coincide in
general.

**Retiring the old number.** Four in-tree quotes (three lane status files,
ADR-1589) are dated records, so each keeps its figure and gains a forward note:
correct on its date, not a rate, not comparable, pointer to the channel metric.
`docs/math-department/11-applied-and-computational.md` (rows 219, 226) and
`docs/math-department/12-the-chair.md` (lines 127, 318) carry the other two;
another session owns that directory and this lane reports rather than edits.
The chair's line 318 already asks for a derived, gated number — that is now
`measure-producer-channel.py`.

**Evidence.** Both new checkers have a control suite where each guard has ONE
control asserting on that guard's OWN finding text, and a `--guard-deletion`
mode: producer-channel 6 guards / 6 controls / exactly 1 death each;
holdout-price 5 testable guards / 5 controls / exactly 1 death each, with
`empty-family` reported UNTESTED rather than implied (a zero-row held-out family
is not constructible from the manifests). The suites found four real defects in
their own subjects, one of which — a moved `ROOT` making four of five deletions
blame the wrong control — would have read green under a suite that only asserted
"the mutant fails".

**Not done, with the obstruction.** ASSIST sites are not joined to the ledger:
the theorem name is not at the call site, and resolving it needs the enclosing
declaration, which is a heuristic this lane declined to ship as a number.
Instrumenting the prelude build for a runtime emission count is the honest
measurement and is out of scope — this lane may not touch a crate.

<!-- plan-section: landed-changes -->

| 2026-09-06 | production-metric | `scripts/measure-producer-channel.py` + baseline: the three-layer producer-channel census, fail-closed on an unclassified entry point (`94545a516`) |
| 2026-09-06 | production-metric | `scripts/tests/test-producer-channel-controls.sh`: 6 guards, 6 controls, guard deletion kills exactly one (`5d9bf340f`) |
| 2026-09-06 | production-metric | `scripts/price-holdout-family.py` + `scripts/tests/test-holdout-price-controls.sh`: one family = 10 propositions = 4.9% of the remaining blind rows (`00ce1744c`) |
| 2026-09-06 | production-metric | ADR-1679; the retirement metric retired as a rate in four dated records, each keeping its figure and gaining a forward note |

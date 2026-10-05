# Lane: lra-dense — pricing the `QF_LRA` offline dense engine

<!-- plan-section: lane-status -->

**Lane block (`DONE`, lra-dense, 2026-09-14).** [ADR-2055] prices both
allocations [ADR-2045] named, ships one, **refuses the other because it is a
loss**, and corrects the handoff twice.

**Where the memory goes, profiled at all 74 rows of the route.** The
`lra.rs:944` round trip is **real** and it is **14.0 %** of the two allocations
(12.2 % as measured RSS growth), 30.2 % of the bytes an *aborting* process
actually held. It is not the 5.07 GiB. **The tableau is**: `m × (nvars+m)`,
median **19,198,877 cells against `MAX_TABLEAU_CELLS = 4,000,000`** — over by a
median **69×**, max **1140×**, on 46 of 74 rows — holding a median **34,555
nonzeros**, i.e. **0.0288 % dense**. The abort half is building tableaux needing
a median **10.53 GiB** against an 8 GiB ceiling; the clock half needs **0.20
GiB** and is not memory-bound at all. **15 of the 40 aborts die inside the
round-trip loop** — the lever's best case — and re-run under the sparse arm they
need a **median 228.83 GiB** tableau: **0 of 15 fit**.

**A/B over the whole board**, one binary under five env values, arms back to
back per file on a pinned core, base re-deriving **107 of 200** exactly.
**Sparse rows: net +0, gains 0, losses 0, flips 0, 0 new aborts**, against a
**row-level noise floor of 0 of 200** measured in the same run by a repeated
base arm; soundness 0 at a comparable denominator of 97; **0 gains, so the
authority check has a comparable denominator of 0**, printed. **They ship, and
ship as the only path** — a lever defaulting `Off` leaves the new path exercised
by no gate, which is what makes the fuzzes' 5 / 1 / 1 mean something.

**The cell cap does NOT ship, and not for the pre-registered reason.** R11
allowed "belongs there, buys 0 verdicts". Measured: net **−1** and **18 rows
that terminate cleanly become `rc=134` aborts**, one answering `sat`. Mechanism
measured: base builds **11 tableaux** and spends **20,086 ms of 24,000** in them
and exits 0; the cap arm builds **0**, declines **once**, and dies allocating.
One entry, not thousands — not a runaway loop. **The unpriced allocation was
accidentally load-bearing: the tableau was a sink absorbing the budget a worse
route then spends.**

Control `QF_S` **186 → 186** and exposure `QF_UFLRA` **148 → 148**, both run,
both zero, both shown non-vacuous — the changed function executes **559 times
across 12 `QF_UFLRA` rows** and **0 times** in `QF_S`.

**Two corrections to the handoff, both its own finding one level down.** Its
clock bucket is **26 of 34 dense-engine-bound, not 34 of 34**: 7 rows are bound
by the **Boolean skeleton** (on `sc-7`, `cube_simplex_ms` is 13.7 % of the
budget and `skeleton_ms` is 84.2 %), because a **call counter says a thing
happened, not that it dominated**. And the named capability wall is **two
failures behind one sentence**: over its 23 rows, **16 are a model that WAS
built and does not replay**, 6 are no model reconstructed (all 6 the simplex
declining), and **0** are the `i128` witness boundary that was the leading
hypothesis.

**Next lane on this division starts here:** stop working on allocations inside
the offline dense engine — both are priced, one is 14 % and decides nothing, and
capping the other costs clean exits. The work is **model REPLAY, not model
RECONSTRUCTION**: `add_boolean_leaf_values` and what the encoding omits from the
reconstructed model. `AXEYUM_LRAMODELPROBE=1` is in the tree to re-measure it.
The `sc-*.base.cvc` skeleton family is a separate lane.

**Method warning worth more than the result:** before capping or declining
anything on a budget-bound route, **measure the exit-status channel**. A verdict
count reports the cap as `losses=1`; the damage is 18 rows wide and almost all
of it is invisible there.

<!-- plan-section: landed-changes -->

| 2026-09-14 | `7158ae5ee` | lra-dense: pre-registered rules before any measurement existed; R11 names "the cap buys 0 verdicts" as an acceptable outcome in advance |
| 2026-09-14 | `4abc994a0` | lra-dense: sparse simplex entry + a measurable cell cap + the RSS probe, both levers off, equivalence tested not asserted |
| 2026-09-14 | `00cbc3fbc` | lra-dense: the memory is the TABLEAU (0.0288 % dense, 69× past its own cap); the handoff's clock bucket is 26 of 34, not 34 of 34 |
| 2026-09-14 | `15ba818f4` | lra-dense: clippy clean at 887/887; the three z3 fuzzes re-run with the lever ON, because off-by-default gates test the old path |
| 2026-09-14 | `af574a840` | lra-dense: ship the sparse rows as the only path; the cell cap CREATES 18 aborts and does not ship (ADR-2055) |

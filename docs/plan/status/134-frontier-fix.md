# Lane: frontier-fix — autogenesis frontier selector diagnosis

<!-- plan-section: lane-status -->

**Frontier admissibility diagnosis (`done-for-now`, frontier-fix, 2026-08-27).**
Re-measured doc 262's `fact-frontier.py --json` result on today's 776-fact
ledger: ready 141→132, admissible unchanged at 0. Root-caused it precisely,
against the validator rather than by inference: `validate-autogenesis-
operations.py`'s `ADMISSION_CONTRACTS` is a closed set of exactly two tuples,
both requiring `epistemic_status: "proved"` — so no operation can be
registered for a fact whose proof does not already exist somewhere,
independently checked. Confirmed empirically that all 27 currently-registered
operations name already-proved facts, and that zero orphaned
"candidate-checked-not-admitted" manifests exist for any open fact (nothing
free to wire in). Of 776 facts ledger-wide, exactly one open fact
(`F:fp16-add-monotone-rne`) is in a decidable SMT fragment; the other 125
ready-but-unregistered facts need a genuinely new kernel proof via the
s5-hosted Mathlib/lean4export pipeline. Did not fabricate an operation
claiming `proved` for unproved work — that is the exact "checker that cannot
fail" defect this project repeatedly finds and repairs. Full writeup:
`docs/autogenesis/288-admission-precedes-registration.md`.

**Landed.** A purely additive `diagnostics` key in `fact-frontier.py --json`
(`ready_count`, `admissible_count`, `unregistered_by_route_class`) so the
decidable/proof-route-only/no-route split doesn't have to be reconstructed by
hand every time; 8/8 existing `test_fact_frontier.py` cases still pass
unmodified. No change to `artifacts/autogenesis/operations.json`,
`nursery-v1.json`, or any fact — `check-autogenesis-holdout-isolation.py`
still passes (`held_out=37|verdict=PASS`), confirming the partition is
untouched.

Detail moved to [`../notes/134-frontier-fix.md`](../notes/134-frontier-fix.md).

<!-- plan-section: landed-changes -->

| 2026-08-27 | `PENDING` | Diagnosed why `fact-frontier.py --json` reports `admissible: 0` over 132 dependency-ready facts: operation registration requires a completed, independently-checked proof (`ADMISSION_CONTRACTS` allows only `proved`), and none exists for any open fact. Added a purely additive `diagnostics.unregistered_by_route_class` split to `fact-frontier.py`; declined to fabricate an operation over unproved work. `docs/autogenesis/288-admission-precedes-registration.md`. |

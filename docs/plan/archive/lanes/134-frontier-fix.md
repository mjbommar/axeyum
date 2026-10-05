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

**Curriculum.** Did not edit `docs/curriculum/curriculum.toml`. This week's
~30 new `proved` `CReal`/`Complex` facts (uniform convergence, alternating
series, polynomial evaluation, Complex factor-quotient/Horner form) map onto
`sequences-and-limits`/`calculus`/`complex` — three nodes that already exist,
currently `status = "lean-horizon"` on the SOLVER axis (no `axeyum-scenarios`
family). Adding finer nodes would each need a real `gen-foundational-
concepts.py` `CURRICULUM_MAP` entry naming an EXISTING example pack, which
none of the plausible finer topics has yet; asserting one without a pack
risks exactly the "asserts coverage it cannot demonstrate" defect
`check-curriculum-coverage.py` exists to catch. Recorded as a finding in doc
288 instead of a curriculum.toml edit.

**Next, for whoever has s5/Mathlib iteration time.** Doc 288 names four
sibling `Int.ModEq` facts already dependency-ready
(`F:ml430-int-modeq-add-left-6e17c69a`, `-neg-f649f6c5`, `-of-dvd-b9c41fce`,
`-sub-3148f130`) as the best next candidate for a genuinely general
multi-target operation, since the shape-generic checker
(`modeq_family_operation`, declines by typed `UnsupportedRecursorShape`/
`UnsupportedIffShape` rather than fixed theorem names) already exists and
only needs new s5-side Lean exports for these four targets. Separately,
`F:fp16-add-monotone-rne` is the one open fact reachable by pure compute (no
new proof needed) — worth a bounded, explicitly-timed attempt at the existing
`smtcomp_cli` route.

<!-- plan-section: landed-changes -->

| 2026-08-27 | `PENDING` | Diagnosed why `fact-frontier.py --json` reports `admissible: 0` over 132 dependency-ready facts: operation registration requires a completed, independently-checked proof (`ADMISSION_CONTRACTS` allows only `proved`), and none exists for any open fact. Added a purely additive `diagnostics.unregistered_by_route_class` split to `fact-frontier.py`; declined to fabricate an operation over unproved work. `docs/autogenesis/288-admission-precedes-registration.md`. |

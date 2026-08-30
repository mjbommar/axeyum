# Lane: gate-rot-triage — three RED gates from `scripts/check.sh`: stale, stale-but-real, and quietly broken

<!-- plan-section: lane-status -->

**Your lane's block (`DONE (all three gates fixed; the third was not what it
looked like)`, gate-rot-triage, 2026-08-29).**

Verdicts, one line each: **1) STALE** (`check-fact-depends-derived.py`) —
the ledger, not the checker, was behind. **2) STALE FIXTURE, GUARD SOUND**
(`test_check_autogenesis_nat_fib_gcd_premise_selection_policy.py`) — real
proof work advanced the chain the fixture assumed was frozen. **3) BROKEN
SCANNER, DISGUISED AS A STALE BASELINE** — this is the one worth reading
carefully, because the naive fix (lower the number to match a fresh count)
would have been actively wrong.

## 1. `check-fact-depends-derived.py` — STALE, and by a lot

Reproduced before touching anything: `missing_edges=1054` across 306 facts
(kernel_facts=1808, graph=1770), not the small drift a "~30 facts landed
today" framing suggested. 182 commits touched `artifacts/facts/` since this
gate was last green (`233331935`, 2026-08-25). This checker needs a
`--release` build of `theorem_dependency_inventory`, which is the expensive
step every lane has been skipping while re-verifying narrowly — exactly the
mechanism CLAUDE.md's flywheel section warns about.

Spot-checked one failure before trusting the bulk fix:
`F:cassini-identity-over-constructed-integers` already `depends_on`
`F:ml430-nat-fib-add-two-b86e0c82` (an ADR-0603 mirror fact) for the same
underlying theorem `Nat.fib_add_two`, but not `F:nat-fib-add-two` — the
native fact whose evidence actually names that kernel theorem via
`theorem_dependency_inventory`, which is the one this checker's
theorem-to-fact map resolves to. Real gap, not a checker artifact.

Detail moved to [`../notes/279-gate-rot-triage.md`](../notes/279-gate-rot-triage.md).

<!-- plan-section: landed-changes -->

| 2026-08-29 | `237c1abdd` | Re-derive 1054 missing `depends_on` edges across 306 facts; `check-fact-depends-derived.py` was genuinely stale (182 commits since last fix), not broken. |
| 2026-08-29 | `166e789d1` | Repair the premise-selection proved-prefix control's stale fixture (the chain it mutated is now genuinely all-`proved`); guard itself confirmed sound by delete-and-recount. |
| 2026-08-29 | `2bd5d391c` | Fix `check-control-tests-reachable.py`'s false-credit bug: `control-optout.tsv`'s bare (non-`#`) exclusion rows were vouching for modules they name as unrun. `ORPHAN_BASELINE` 14 -> 16 (corrected measurement, not new rot). |

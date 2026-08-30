# Notes: 149-fact-refresh

Detail moved out of [`../status/149-fact-refresh.md`](../status/149-fact-refresh.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

**Sample execution results:**
- `nat_axiom_inventory --require-axiom-free rat`: exit 0 (rat is axiom-free, as expected)
- `nat_axiom_inventory --require-axiom-free axreal`: exit 1 (axreal has 30 axioms, as expected)
- `theorem_dependency_inventory -- Rat.abs_zero`: exit 0 (theorem exists)
- `theorem_dependency_inventory -- Rat.abs_zero_WRONG`: exit 1 (theorem does not exist)

**Demonstration of failure modes:** All four tests behaved as expected. The two axiom_inventory checkers showed the expected difference between an axiom-free prelude (exit 0) and one with axioms (exit 1). The two dependency_inventory checkers demonstrated that name-based selection works correctly, failing on non-existent names and passing on real ones.

This directly shows the checkers are NOT vacuous — they have observable failure modes tied to the facts they check.

## Other findings

None. The generator performed as designed. No defects found in validate-facts.py or the audit gate.

## Scope of changes

**Committed in this lane:**
- New: 429 `artifacts/facts/F-*.json` files (all six preludes)
- Modified: `artifacts/ledger-coverage.json` (coverage regenerated)
- No edits to: `scripts/gen-kernel-facts.py`, `validate-facts.py`, `PLAN.md`, or `docs/plan/global/`

**Left on shared checkout (to be synced later):**
Generator itself operates on the shared checkout's `artifacts/` directory; all new facts are already committed in this lane's worktree copy.

## Next steps

- Merge this lane's work to main
- The two remaining unregistered theorems should be investigated (likely edge cases in PRELUDE_CONTRACT or axiom-footprint filtering)
- Consider the curated counter enhancement mentioned in ADR-0607 §6 as a follow-up

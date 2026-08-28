# Lane: decidable-frontier — settle the three DECIDABLE open facts named by scripts/fact-frontier.py

<!-- plan-section: lane-status -->

**Your lane's block (`WIP`, decidable-frontier, 2026-08-28).** IN PROGRESS.

Findings so far:
- `F:rado-r4-a5-b3` and `F:rado-r4-a5-b4` were ALREADY SETTLED before this lane
  started (commits `04f480b52`, `061f8e634`/`b8be40096`) — `epistemic_status:
  computed`, evidence attached, checkers re-run here and pass (`validate-claims.py`
  0 errors; `akb2_frontier verify` witness-verified; `check-claim-certificates.py`
  0 errors). No action needed — the brief was stale on these two, per CLAUDE.md's
  "verify a blocker still exists" rule. `validate-facts.py` confirms both under
  NOVEL.
- `F:fp16-add-monotone-rne` is the real open item. In progress: attempting the
  symbolic decide + evidence route per the fact's own extensive prior
  measurement (decide ~11.5s, evidence/DRAT-check previously did not terminate
  in 3+ hours; search itself is ~24s producing a ~193MB proof, and check_drat +
  LRAT elaboration is the wall).

<!-- plan-section: landed-changes -->

| 2026-08-28 | decidable-frontier | lane started; confirmed both rado facts already settled (no edit needed); fp16 attempt in progress |

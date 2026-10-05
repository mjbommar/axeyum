# Lane: decidable-frontier — settle the three DECIDABLE open facts named by scripts/fact-frontier.py

<!-- plan-section: lane-status -->

**Your lane's block (`DONE`, decidable-frontier, 2026-08-28).** The brief named
three facts as the entire DECIDABLE-open frontier; only one of the three was
actually open.

- `F:rado-r4-a5-b3` and `F:rado-r4-a5-b4` were ALREADY SETTLED before this lane
  started (commits `04f480b52`, `061f8e634`/`b8be40096`) — `epistemic_status:
  computed`, evidence attached. `fact-frontier.py` prints "DECIDABLE --
  dispatch it" on their rows because that annotation is a fragment-routability
  label printed across several sections, not an open/closed signal — the rows
  sit under "ESTABLISHED HERE, NOT IN THE LITERATURE", not under an open
  section. Confirmed by re-running their own checkers here
  (`validate-claims.py`, `akb2_frontier verify`, `check-claim-certificates.py`
  — all 0 errors) and by `validate-facts.py`, which lists both under NOVEL.
  **Neither file was edited by this lane** (`git diff` on both is empty for
  the whole session).
- `F:fp16-add-monotone-rne` is the one genuinely open item, and it stays
  `open` — no evidence was added, only its `notes` gained a corroborating
  2026-08-28 re-measurement (decide-only reconfirmed at 11.09s unsat; search
  stage reconfirmed at 424,601 conflicts / ~24-27s / 827,048 proof steps /
  ~193MB; and NEW — a direct measurement of the checking stage's own
  throughput, previously known only as "doesn't finish in 3+ hours":
  `drat_check` runs ~95 steps/sec against 827,048 total steps, extrapolating
  to ~2.4h for that sub-stage alone before `elaborate_drat_to_lrat` even
  starts). `validate-facts.py` still reports 0 errors, `open=171` unchanged.
  A precisely measured obstruction, not a settlement.

<!-- plan-section: landed-changes -->

| 2026-08-28 | decidable-frontier | confirmed F:rado-r4-a5-b3 and F:rado-r4-a5-b4 already settled, no edit made; added a corroborating 2026-08-28 re-measurement to F:fp16-add-monotone-rne's notes (drat_check throughput ~95 steps/s, ~2.4h extrapolated), fact stays `open` |

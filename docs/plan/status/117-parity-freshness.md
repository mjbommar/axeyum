# Lane: agent-parity-gate — the headline can go stale loudly, and then it got re-measured

<!-- plan-section: lane-status -->

**The parity ledger has a gate, it is ENFORCING in both aggregate gate sets, and
the board behind it has been re-measured** (`WIP`, agent-parity-gate,
2026-08-21). `bench-results/PARITY.md` is the declared headline — external list
pinned by sha256 before each run, `DISAGREEMENTS > 0` voids an entry — and
`scripts/parity-run.sh`, the only thing that writes it, was invoked by **no
gate**: not `just check`, not `scripts/check.sh`, not CI. So the board froze on
2026-08-06 for fifteen days, through UF 32 → 85 and QF_RDL 10 → 105, and nothing
went red.

`scripts/check-parity-freshness.py` derives a per-logic as-of date from each
entry's own header and fails past **14 days** (warn at 10). 14 is not a round
number: any budget ≥ 15 days would have sat green through the whole episode the
gate exists for, and below it the binding constraint is cost — the ledger's own
2026-08-06 sequence puts a division at 68–170 minutes. The budget is **per
logic**, so a red costs one sweep, not a board refresh. The population comes
from the append-only ledger, never from `bench-results/parity-lists/`: a list
can be deleted, so anchoring there would let a logic be dropped from the tracked
set to go green.

Detail and older landed rows moved to [`../notes/117-parity-freshness.md`](../notes/117-parity-freshness.md).

<!-- plan-section: landed-changes -->

| 2026-08-21 | `da314781b` | QF_NIA post-fix: 39/83 = 47.0%, **+6** on its own pre-fix sweep four hours earlier. Which corrects the batch note: `40a1ab969` — one file in `dpll_lia.rs` — moved FOUR divisions (QF_UFLIA +18, QF_NIA +6, QF_SLIA +2, QF_RDL +1), one of them strings and one nonlinear, where it was expected to move QF_UFLIA. Scoped to the expected division, three of those rows would have been recorded at PRE-FIX values under today's date with the freshness gate green over them. |
| 2026-08-21 | `f2060eeb2` | The freshness gate runs in hosted CI too — the third place the gap analysis named. Held back deliberately until the board was green, because a gate that reds CI on landing over a multi-hour sweep is one people learn to override. Runs in the `fetch-depth: 0` job, which is load-bearing: the solver-currency column needs history and degrades to NO-GIT on a shallow clone (verified against a `.git`-less tree — reports NO-GIT, still exits 0). |

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

**Freshness is not correctness, and that nearly bit on day one.** Mid-sweep,
`40a1ab969` (ADR-0538) landed — one file, `dpll_lia.rs` — and the sweep tree did
not contain it. A `2026-08-21` entry carrying the pre-fix QF_UFLIA number would
have been *fresher-looking and more wrong* than the 2026-08-06 entry it
replaced, with this gate green over it. Every arithmetic division was re-swept
from a post-fix tree, and the gate now reports each entry's `solver commit`,
its ancestry, and `behind=N` commits touching `crates/` — advisory, because a
commit-count bound is red-by-construction during a burst and non-ancestry is
legitimate when a lane measures from its own branch.

**Two instrument defects fixed, both found by measuring.** `parity-run.sh`
claimed every ratio is a lower bound under contention; true of each solver's own
count, false of their quotient — QF_LRA read 70.1% at load 32 and 64.2% quiet,
because contention cost the reference ten files and cost us none. And
`docs/PROJECT-STATE.md` claimed the ledger held "eleven divisions" and named
QF_ABV as a parity cell; it holds nine and has never held a QF_ABV entry —
`parity-lists/QF_ABV.txt` is a committed list that was never run.

Controls: 16 cases, every guard mutation-verified by deletion, mutation map in
the suite's header. Two run against the real committed ledger, because a parser
never pointed at its subject returns the same empty answer as a strong negative.

**Next.** Wire the gate into `.github/workflows/ci.yml` (the third place the
gap analysis named) once the board is green; measure QF_ABV and QF_UF, whose
lists are committed and have never been run; and hand UF's reproducible
composition shift (both/only 77/8/14 → 60/23/33 across ~100 commits) to the UF
lane.

<!-- plan-section: landed-changes -->

| 2026-08-21 | `df30d9fa9` | `parity-run.sh` said every ratio is a LOWER bound under contention. True of each solver's own count, false of the quotient: QF_LRA measured 89/127 = 70.1% at load 32 and 88/137 = 64.2% quiet, so the loaded run read six points HIGHER because the reference lost ten files and we lost none. Also: the freshness gate now reports each entry's `solver commit`, ancestry and `behind=N` — QF_BV was 4.0 days fresh and 352 solver commits behind, the number nobody had. Advisory by design; making it fatal kills seven controls. |
| 2026-08-21 | `e7d8629c5` | `docs/PROJECT-STATE.md` said the parity ledger holds "eleven divisions" and named QF_ABV among its parity cells. It holds nine and has never held a QF_ABV entry — that list is committed and was never run. Two guards added to `check-parity-docs.py`, both derived from the ledger and both shown to fire on the real tree before the prose was fixed. |
| 2026-08-21 | `35f46112b` | `scripts/parity-run.sh` was invoked by NO gate, so the repository's declared headline froze on 2026-08-06 for fifteen days and nothing went red. `scripts/check-parity-freshness.py` fails past 14 days per logic (warn 10), wired into BOTH `scripts/check.sh` and the justfile's `check`. Parser classifies every `## ` header and exits 2 on one it does not recognise — a silently skipped entry is indistinguishable from an absent one, which is how a stale logic reads as fresh. 12 controls, every guard mutation-verified. |

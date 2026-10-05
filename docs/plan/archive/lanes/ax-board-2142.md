# Lane: ax-board-2142 — does the ADR-2142 target-phase snapshot fix move the 16-division board?

<!-- plan-section: lane-status -->

**AX-BOARD-2142 (`landed`, ax-board-2142, 2026-09-17).** Measured, not
argued: the ADR-2142 fix (`60e23fa39`) against its parent (`b11264ebe`),
one commit apart, two fresh hash-checked `smtcomp_cli` binaries, interleaved
per file on the same pinned core over all 16 divisions × 200 files of
`bench-results/parity-lists/` (3,200 rows, 4 shards on idle s5/s6, 2 h 43 m).
**2,424 → 2,432 (+8): raw 9 gains / 1 loss, and after 3× per-arm recheck 8
STABLE-GAIN / 0 STABLE-LOSS / 2 ambient; 0 sat↔unsat flips, 0 `:status`
disagreements over 4,380 comparisons, 0 exit-status differences.** The stable
gains are `QF_UFLIA` +5 (four `wisas/xs_*` sat, one `mathsat/Hash` unsat),
`QF_ABV` +1, `QF_BV` +1, `QF_NIA` +1; each was A at the 24 s budget and B at
8–23 s, the shape the ADR predicts (only clock-cut verdicts can move when
trajectories are identical). The raw `QF_UFLRA` loss and one raw `QF_UFLIA`
gain each decide 3/3 in both arms and were ambient. Twelve divisions moved by
zero. Wall on the 2,423 both-decided files fell 4,660 → 4,475 s (−4 %),
concentrated in `QF_ABV` (293 → 148 s; 30 files under half the old wall, 29 of
them `dwp_formulas`, all `sat`). Five files abort with 134 in BOTH arms
(pre-existing). Write-up, `board.tsv`, every row and the 3×-per-arm mover
rechecks: `bench-results/board-ab-20260917-adr2142/`. **Next:** a same-day
z3/cvc5 reference board on `parity-lists` (the 09-14 reference totals were on
the basename-reconstructed population, which differs on `QF_BV`, `QF_LIA`,
`QF_SLIA`, `QF_UF`); the coordinator's scoreboard rows for `QF_UFLIA` (+5),
`QF_ABV` (+1), `QF_BV` (+1) and `QF_NIA` (+1) should move by the stable
delta (`QF_UFLRA` does not move).

<!-- plan-section: landed-changes -->

| 2026-09-17 | ax-board-2142 | ADR-2142 board A/B (`bench-results/board-ab-20260917-adr2142/`): +8 of 3,200 (8 stable gains / 0 stable losses / 0 flips / 0 disagreements over 4,380), `QF_ABV` both-decided wall −49 %; scripts, shard rows, `board.tsv`, 3× mover rechecks. |

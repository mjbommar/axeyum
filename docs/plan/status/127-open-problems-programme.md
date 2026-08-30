# Lane: open-problems-programme — five end-to-end research targets

<!-- plan-section: lane-status -->

**WIP, open-problems-programme, 2026-08-26.** Five durable research packages now own the
Rado/Schur, GF(2) bilinear-rank, S-box optimality, SIMD-shuffle minimality, and optimization
bound-certification targets.  The Axeyum-side programme contract is
`docs/research/10-cas/open-problems-programme-2026-08.md`: pin current literature status,
generate deterministically, run untrusted search, independently replay/check, bind evidence,
and reconstruct formal identities into the kernel where applicable. Current focus stays on
`abz7`: deterministic detectable-precedence closure is complete and exhausted after one round,
and an exact checker-compatible FlatZinc/DRCP route is calibrated against both an independent
Rust checker and the Rocq-verified FznDrcpCheck. Sustained `abz7@655` proof production remains
live without a short wall-clock cutoff; the upper-bound search is closed by the replayed public
656 witness described below. The
settled-cell calibration is green for `R_3(x-y=z)=14` (42 variables,
356 clauses, 25 checked DRAT steps); a mutated DIMACS header fails closed, and the aggregate
claim sweep reports 104 claims re-checked / 0 errors / 25 rows explicitly not re-checked.
The SIMD brief's named byte-reversal target is now closed in its explicitly listed fixed
shuffle set; the other four headline targets remain open.

**S-box top-level semantic cell 8 checked, 2026-08-27.** The bounded whole-tree checker
accepted all 961 manifest-selected obligations beneath top-level Boolean-product cell 8:
931 leaf DRAT refutations and 30 covering proofs totaling 62,886,514,460 consumed bytes.
Every formula was reconstructed from the hash-bound exact-irredundant base and its typed cube
path; the terminal log and root manifest/cover are hash-bound in the sibling receipt. This
closes one of the 32 exhaustive semantic cells, not the remaining 31 and not the full MC<=7
formula, so the `[7,8]` interval and five-problem scoreboard do not move.

**S-box top-level semantic cell 4 checked, 2026-08-27.** The same bounded checker reached
`385/385` and terminal `unsat-checked`: 373 leaf DRAT refutations plus 12 covering proofs,
57,326,968,062 manifest-selected bytes. The base, typed cube, manifests, cover, checker binary,
terminal log, and counts are hash-bound in the sibling receipt. Cells 4 and 8 now close 2/32
exhaustive semantic cells. The other 30 remain open, so the `[7,8]` interval does not move.

Detail moved to [`../notes/127-open-problems-programme.md`](../notes/127-open-problems-programme.md).


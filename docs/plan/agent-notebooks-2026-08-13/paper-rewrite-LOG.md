# Paper rewrite notebook (append-only)

Repo: /home/mjbommar/projects/personal/axeyum-rado-paper
Branch tip at start: e0c9370 (a merge d69e118 from another lane landed at 22:34
while I was reading — ancillary artifacts + commands.tex macros; sections
untouched, so my lane is clear).

## Baseline (before any edit)

- `make pdf`: 12 pages, 0 overfull/underfull/undefined.
- `make check`: check_style OK (7 files, 0 advisory); check_refs OK;
  claims_complete OK (2 asserted values).
- Body files: 01_introduction, 02_preliminaries, 03_shell (402 lines, the
  whole mathematics), 04_results, 05_method, 06_limitations, 07_appendix.

## Numbers verified before use (not hand-typed)

- 932 = `wc -l crates/axeyum-cnf/src/drat.rs` in the sibling axeyum repo, the
  forward reference DRAT checker. The backward checker is
  `drat_backward.rs`, 2,098 lines.
- 1,640 comparisons = the three layers of
  `crates/axeyum-cnf/tests/colouring_encoding_parity.rs`, run just now:
  layer 1 = 35 stored ledger CNF artifacts, layer 2 = 1,599 sweep instances,
  layer 3 = 6 headline instances through the script's own CLI. 35+1599+6=1640.
  Test output kept in this scratchpad's task log; exit 0, 3 passed.
- Forward/backward agreement: `drat_backward.rs` carries five
  `agrees_with_the_reference_*` differential tests, and its own contract note
  says the two agree exactly on any proof the forward checker accepts (they
  differ only in that backward accepts a proof carrying unjustified dead
  weight). The appendix sentence is written to that precision.


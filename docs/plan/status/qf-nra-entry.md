# Lane: qf-nra-entry — put QF_NRA on the parity board

<!-- plan-section: lane-status -->

**Your lane's block (`WIP`, qf-nra-entry, 2026-09-06).** Task:
`docs/plan/families/smt-quantifier-free/qf-nra.md` says QF_NRA is rank 1 of the
cheap parity targets — same input format, same protocol, `scripts/parity-run.sh`
needs no changes. Entering is a measurement task: a committed 200-file list, a
pinned reference build, one ledger entry with zero disagreements, and a census
of the losses.

Benchmark list committed first, before any sweep, per protocol. Selection
recipe matches the one recorded for QF_LRA/QF_NIA/QF_UF/QF_BV (commits
`aaa2d7541`, `025f4ba9f`, `565284cf7`):

```
LC_ALL=C find <abs-div-dir> -name '*.smt2' | LC_ALL=C sort \
  | awk 'NR%stride==1' | head -200
```

QF_NRA population 12,154 files, stride 60 (12154 // 200), 200 selected,
sha256 `d645dd907edd60f62e4bbd815c2f420d3feaa88731e55ab4f63a7677705ef931`
(short: `d645dd907edd`).

Reference: `scripts/parity-run.sh` already routes `QF_NRA` to
`/nas3/data/axeyum/harness/bin/cvc5` (same arm as QF_LIA/QF_NIA/QF_IDL/QF_RDL —
the fallthrough would be unpinned `/usr/bin/z3` 4.13.3, which did not compete
in SMT-COMP 2025). Plain invocation, no portfolio flags.

Remaining steps this lane still owes: build the release `smtcomp_cli` via
`scripts/cargo-serialized.sh`, run the sweep on an idle host (s5/s6/s7,
`taskset -c 0-7`, 24s/8GiB), append the `PARITY.md` entry, census the losses
through the front door (`smtcomp_cli`, timed trace, `explain_corpus` excluded
as inadmissible per its own DIAGNOSTIC-ONLY banner), and update
`docs/plan/families/smt-quantifier-free/qf-nra.md` from "not entered" to the
measured numbers.

This file will be updated with the final ledger row and census result before
the lane closes out. `PLAN.md` is not touched — status only.

<!-- plan-section: landed-changes -->

| 2026-09-06 | qf-nra-entry | committed `bench-results/parity-lists/QF_NRA.txt` (200 files, sha256 `d645dd907edd`), selection recipe recorded above, no sweep run yet |

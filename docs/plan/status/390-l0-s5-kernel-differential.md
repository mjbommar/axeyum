# Lane: l0-s5-kernel-differential — ADR-0717 S5 kernel differential + mutation programme

<!-- plan-section: lane-status -->

**Your lane's block (`DONE for this slice`, l0-s5-kernel-differential,
2026-08-30).** S5's exit criteria are met for a first, real slice: a
32-case (4 per subsystem × 8 named subsystems) Axeyum-vs-pinned-Lean
differential corpus, gated, and an 8-mutation kernel-source kill table.
Full writeup: ADR-0780.

What landed:
- `crates/axeyum-lean-kernel/tests/kernel_differential.rs`: 32 cases, each
  authored twice independently (kernel term-builder API + plain Lean
  syntax). Classification is three-way (agree / P0 / registered
  incompleteness); `EXPLAINED_INCOMPLETENESS` has exactly one entry
  (`quotient::quot_sound_absent`, ADR-0456).
- `scripts/check-kernel-differential.py`: the gate, six independently
  mutation-verified guards (`scripts/tests/test-kernel-differential-gate.sh`).
- `artifacts/kernel-differential/mutant-kill-table.json` +
  `scripts/check-kernel-differential-mutants.py`: 8 hand-run kernel-source
  mutations (one per subsystem), 4 killed / 4 survived. The ratchet checks
  the artifact's internal consistency, not a live re-mutation (that needs
  ~8 kernel rebuilds mutating tracked source, which is a by-hand act, not a
  CI-suitable one -- see ADR-0780's alternatives section).
- Registered in `justfile` (`kernel-differential` recipe, added to `check`)
  and `scripts/check.sh` (three `step`s); `scripts/check-lean-gate.sh`'s
  suites table and `CHECK_FLOOR` (229 -> 261) updated -- `check-kernel-
  suites.sh --list`'s auto-discovery had correctly flagged the new suite as
  unregistered before this.

Full run against pinned Lean 4.30.0: 32/32 cases, zero P0, zero unexplained
incompleteness. Two real construction bugs were caught and fixed while
building the corpus itself (a de Bruijn depth error in a parametric
inductive; a `close_pi`-for-a-value confusion in a quotient case) -- see
ADR-0780's evidence section.

Detail moved to [`../notes/390-l0-s5-kernel-differential.md`](../notes/390-l0-s5-kernel-differential.md).

<!-- plan-section: landed-changes -->

| 2026-08-30 | l0-s5-kernel-differential | ADR-0717 S5: 32-case kernel differential vs pinned Lean 4.30.0 (0 P0, 1 registered incompleteness), gated in justfile/check.sh, 8-mutation kernel-source kill table (4 killed / 4 survived), ADR-0780 |

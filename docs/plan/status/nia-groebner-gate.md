# Lane: nia-groebner-gate — does raising the ideal-refuter admission gate decide any QF_NIA file?

<!-- plan-section: lane-status -->

**Lane nia-groebner-gate (`IN PROGRESS`, nia-groebner-gate, 2026-09-15).**
ADR-2112's Part F handed-forward probe: our Gröbner route
(`cas_ideal_refutation`, `crates/axeyum-solver/src/cas_poly.rs:640`) is
reached on 115 of 200 `QF_NIA` T1 rows and decides 0, refused by an 8/8/8
admission gate (`MAX_IDEAL_GENERATORS`, `MAX_IDEAL_ATOMS`,
`MAX_IDEAL_INEQUALITIES`, all `cas_poly.rs`) on 114 of 116 undecided rows.
Three env levers already exist (`AXEYUM_MAX_IDEAL_{GENERATORS,ATOMS,INEQUALITIES}`,
wired in `c734c45f9`). This lane measures whether raising the gate decides
anything, and at what cost, at 24 s / 8 GiB.

Evidence in progress:
[`bench-results/nia-groebner-gate-20260915/README.md`](../../bench-results/nia-groebner-gate-20260915/README.md).

**Gate read.** All three levers protect COMPLETENESS only
(`Protects::Completeness`, `OnExceed::DeclineRoute` in `config_registry.rs`):
every candidate the route finds is independently re-derived by
`check_cas_ideal_certificate` before acceptance, so raising them can only cost
time, never soundness. Below the admission gate, four FIXED step ceilings
(`ideal_limits()`) bound the Buchberger search itself. Smoke-tested on one
undecided row: at lever 8/16/32 the decline is the admission-ceiling message;
at 64/unbounded it moves to the `basis-size ceiling` message, confirming the
lever is reached and that raising it degrades to a step-ceiling decline rather
than a hang, as ADR-2112 predicted.

**Sweep design.** Ladder shipped(8) / 16 / 32 / 64 / unbounded (1,000,000 — no
sentinel exists for the `usize` lever), each interleaved shipped-vs-gateN over
the 116 undecided `QF_NIA` T1 rows, 24 s / 8 GiB, `--trace`, through
`scripts/ledger-run-one.sh`. Cores: s7 physical pairs `1,9` and `3,11`, rungs
serial per shard. Binary: release `smtcomp_cli` at commit `3c3ba0eb2`
(sha256 `340bdd11053cac94aaece2281a24a46cd79546ae26013e1b5724f3815ce2cf1d`).
Driver scripts committed in `bench-results/nia-groebner-gate-20260915/scripts/`
(also run from a copy on `server7:~/nia-groebner-gate-20260915/`, since s7
does not share this worktree's filesystem).

**Status at last update:** sweep launched on s7, in progress. README table
and verdict TODO until it completes; ADR-2123 and the config_registry change
are conditional on the ship criterion (0 stable losses across QF_NIA/QF_NRA/
UFNIA, ≥ 1 stable gain) — not yet evaluated.

**Next action:** poll the s7 sweep to completion, re-check every mover 3x,
run the QF_NRA/UFNIA cross-check with the best arm, write the verdict, and
either register a dated `config_registry.rs` change + ADR-2123 + full gate
suite (if the ship criterion is met) or stop at the README with the numbers
(if not).

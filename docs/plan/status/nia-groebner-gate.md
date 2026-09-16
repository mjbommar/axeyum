# Lane: nia-groebner-gate — does raising the ideal-refuter admission gate decide any QF_NIA file?

<!-- plan-section: lane-status -->

**Lane nia-groebner-gate (`DONE`, nia-groebner-gate, 2026-09-15).**
ADR-2112's Part F handed-forward probe: our Gröbner route
(`cas_ideal_refutation`, `crates/axeyum-solver/src/cas_poly.rs:640`) is
reached on 115 of 200 `QF_NIA` T1 rows and decides 0, refused by an 8/8/8
admission gate (`MAX_IDEAL_GENERATORS`, `MAX_IDEAL_ATOMS`,
`MAX_IDEAL_INEQUALITIES`, all `cas_poly.rs`) on 114 of 116 undecided rows.
Three env levers already exist (`AXEYUM_MAX_IDEAL_{GENERATORS,ATOMS,INEQUALITIES}`,
wired in `c734c45f9`). This lane measured whether raising the gate decides
anything, and at what cost, at 24 s / 8 GiB.

Evidence:
[`bench-results/nia-groebner-gate-20260915/README.md`](../../../bench-results/nia-groebner-gate-20260915/README.md).

**Answer: no.** Ladder shipped(8) / 16 / 32 / 64 / unbounded (1,000,000),
each interleaved shipped-vs-gateN over the 116 undecided `QF_NIA` T1 rows, 24 s
/ 8 GiB, `--trace`, through `scripts/ledger-run-one.sh`, on s7 physical core
pairs `1,9` and `3,11`. **Gains are 0 at every single level, including
unbounded.** The route is reached on 74 of 116 (42 never qualify as a
candidate — `CasOutcome::NoCandidate`, no lever touches this). As the gate
opens, the route stops REFUSING at admission and starts SEARCHING
(2 → 8 → 17 → 33 → 73 of 74 reached across the ladder), and every search
**completes and fails on its own merits** ("no combination of the asserted
equations collapsed to a constant of the refuting sign" dominates at every
level, not a step-ceiling cutoff). One file at gate ≥ 64 has its own
internal watchdog fire mid-search (partial trail, no verdict consequence) —
the one measured cost, denying downstream routes their turn on that file.

**Cross-division check.** QF_NRA (200/200, complete) and UFNIA (182/200,
completed denominator — this lane closed out on the coordinator's
instruction to report what was on disk rather than relaunch) both hold 0
gains / 0 losses / 0 flips at the unbounded arm against shipped. QF_NRA
already decides 1 file through `cas-ideal-refuter` at the shipped default,
unchanged at unbounded; UFNIA never reaches the route in either arm across
182 sampled files.

**Ship decision: no lever ships ON.** The bar (0 stable losses across all
three divisions, ≥ 1 stable gain) fails on the gain half alone, at every
rung. No `config_registry.rs` change; no ADR-2123 (the lane's own rule: no
ADR unless a lever ships ON).

**Landed:** launcher + README skeleton (`c58f79310`), analysis/recheck
tooling (`c9d0ad98d`), the full QF_NIA ladder result + registered ledger rows
(`2517d176d`), and this close-out (cross-division numbers, status, PLAN.md,
merge to `b4d0f2c33`).

**Next action:** none — the probe ADR-2112 handed forward is answered and
closed. A future lane should not re-open the admission gate on this evidence
without a new reason to expect a different corpus shape.

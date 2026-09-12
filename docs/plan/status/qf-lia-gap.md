# Lane: QF-LIA-GAP — the QF_LIA addressable gap, censused and diagnosed

<!-- plan-section: lane-status -->

**QF_LIA's 55-file gap censused in full for the first time; the top cause was
the dispatcher, not the solver; fixed, and it converts ONE file (`DONE`,
qf-lia-gap, 2026-09-12).**
Census + A/B rows: [`bench-results/qf-lia-gap-census-20260912/`](../../../bench-results/qf-lia-gap-census-20260912/README.md).
Diagnosis: [the measurement note](../../research/03-measurements/qf-lia-the-second-dispatch-rung-ate-the-budget-2026-09-12.md).
Method rule: [ADR-1936](../../research/09-decisions/adr-1936-a-gap-census-reports-attempts-and-marks-an-unfinished-dispatch-unclassified.md).

All 55 winnable files at a 24 s budget with `--trace`, a 120 s wrapper (no
`wrapper-killed` row) and `attempts=` checked against the ladder length
**before** any reason was ranked. That check is what the census turned on: a
completed `QF_LIA` dispatch records `attempts=16`, and **30 of the 55 files
record 5 or fewer** — 23 of them exactly 2. `perf` leaf profiles on three of
those 23, from three `nec-smt` directories, put **99.81 / 97.43 / 95.38 %** of
the run in `term_identity::identity_normal_form`: the second rung of
`check_auto`, no deadline, no route attempt, both `ite` branches, no memo.

Memoised and made iterative. Interleaved per-file A/B over all 200 files, arms
alternating: **+1 decided (116 → 117), 0 losses, 0 flips, wall −4.2 %**. The
convert (`prp-0-47.smt2`, 25.02 s `unknown` → 0.51 s `sat`) agrees with z3,
cvc5 and the declared `:status`, and reproduces on an isolated re-run.

**One convert out of 23 files the phase was eating.** What it also buys: 21 of
the 23 now return a first-class reason instead of a watchdog kill, so the
corrected census can say what the division needs. It says the 27-file `prp-*`
family is a **capability** gap, not a clock or an admission-constant one —
lifting `MAX_MODERATE_PRE_SAT_*` to a million decides 0 at 24 s and 0 at 60 s,
and `check_qf_lia_online_cdclt` run directly with the whole budget declines in
**6 ms** because its atom abstraction accepts `(= x (ite c a b))` and the model
then fails replay. Board arithmetic re-derived: axeyum 119, z3 172, cvc5 139,
**best-of 174**, ours-only 0 — gap 55 / 53 / 22 depending on the reference.

Named and not fixed: `auto::affine_in` (via `prove_int_box`) is the same
no-memo-over-a-DAG defect on a rung with no deadline — **81.66 %** of `RC-09` —
but it carries a depth cap, so memoising it widens which queries get a proven
box and needs its own A/B.

<!-- plan-section: landed-changes -->

| 2026-09-12 | `f20d4ea9f` | The first `QF_LIA` gap census, all 55 winnable files. Its own first finding is about itself: 30 of 55 rows are a picture of which dispatch rung hangs first, not of what the query needs (`attempts=2` against a 16-rung ladder on 23 of them). The hanging rung is `term_identity::identity_normal_form`, measured at 95–100 % of the run on three files. 0 rows with no reason; 0 `wrapper-killed`. |
| 2026-09-12 | `092c807b4` | Memoised `term_identity::identity_normal_form` (iterative + memo; the pure walk carries no depth cap, so this is denotation-identical). Interleaved per-file A/B over all 200 `QF_LIA` files, arms alternating on a pinned P-core pair: **116 → 117 decided, 1 gain, 0 losses, 0 flips, 0 missing verdicts, wall −4.2 %**. The convert `prp-0-47.smt2` (25.02 s `unknown` → **0.51 s `sat`**) agrees with z3, cvc5 and `:status`, and reproduces in isolation. Corrected census shows the `prp-*` family is a CAPABILITY gap (`Int`-sorted `ite`), not clock or admission: envelope-to-a-million decides 0 at 24 s and 0 at 60 s, and `check_qf_lia_online_cdclt` declines in 6 ms. Gates: solver `--lib --features full` 1720 passed/0 failed, `corpus_regression` 2/0, five z3 differential fuzzes 5/1/1/4/4 passed. |

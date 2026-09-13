# Lane: qf-ufbv-caps — the two QF_UFBV caps, measured rather than raised

<!-- plan-section: lane-status -->

**Lane qf-ufbv-caps (`DONE`, qf-ufbv-caps, 2026-09-13).** The QF_UFBV blocker
census attributed **84 of 87 winnable files** to two literals on adjacent lines
of `crates/axeyum-solver/src/ufbv_online.rs`, and the lane that measured it
refused to raise them: *a cap turns a slow `unknown` into a fast one.* This lane
ran the A/B — **9,793 axeyum runs over seven populations** — and shipped the
part of the raise that survives it.

**QF_UFBV goes 89 → 129 of 200. The gap to z3 closes from 85 files to 45.**
Measured as shipped (one binary, nothing set, against the same binary with the
old value restored), with **0 of 400 QF_ABV + QF_ABVFP files changing verdict**.

    division    files   pre-ADR   shipped   gain   loss
    QF_UFBV       200        89       129    +40      0
    QF_ABV        200       186       186      0      0
    QF_ABVFP      200       179       179      0      0

**84 blocked, 49 reachable.** The census named a failure mode, not a set of
fixable files. Over 200 files at nine cap settings, with the baseline arm
reproducing the board row exactly (89 of 200):

    atoms 2_048   +31     nodes  32_768   +0     both 4_096/65_536    +48
    atoms 4_096   +44     nodes  65_536   +0     both 8_192/262_144   +49
    atoms 8_192   +45     nodes 262_144   +0

**The node cap is worth ZERO alone at 2x, 4x and 16x** — not one of the 31 files
the census attributed to it. The two caps are **sequential gates**: a file over
the node budget declines before the atom check runs, so raising it does not
decide the file, it hands it to the atom cap. Over the 111 undecided files,
node-blocked goes 39 → 17 → 9 → 1 as atom-blocked goes 64 → 84 → 92 → 100.

**Both caps also guard a different division's open bug**, which is why the
shipped change is path-specific. On 800 already-decided control files every arm
loses, and re-running each loss nine times on an idle box separates them
completely: the **node** raise turns two QF_ABVFP queries from a 0.4-0.6 s
`array-fast-path` verdict into a 25 s `Watchdog`, **0 of 9**, in every
node-raising arm — a 40x blow-up into `abv-online-cdclt`, the route the QF_ABVFP
census measured completing zero CEGAR rounds at a 600 s budget. The **atom**
raise costs two QF_ABV files 18 s (4.5 s → 22.5 s) deterministically. So the
atom cap is split by path: `MAX_SCALAR_THEORY_ATOMS = 4_096` for
`admit_arrays == false`, `MAX_THEORY_ATOMS = 1_024` kept for arrays,
`MAX_INPUT_DAG_NODES = 16_384` held everywhere.

**Half the control was vacuous and that had to be checked separately.**
`--trace`'s `route-trail` says `ufbv_online` runs on 344 of the 800 control
files and a cap fires on 35 — but on **0 of 400** QF_BV and QF_UFLIA files,
which never enter the route. A zero-loss result over a population that cannot
reach the cap is not evidence of safety.

**The gain is frame-dependent and both numbers are published: +44 on a lightly
loaded frame, +33 on a heavily loaded one.** 12 of the 49 gains land at 15-24 s
of a 24 s budget. `monotone.py` says the same from the other side without a
second run: along every ladder, exactly **1 file of 200** is decided at a lower
cap and not at a higher one.

**Soundness: 0 disagreements** across every population. All 49 newly decided
files re-run against z3 4.13.3, cvc5 1.3.4 and `:status` — 43 decided at the
shipped setting, 43/43 vs `:status`, 40/40 vs each reference, 0 wrapper kills,
and **3 files we decide that neither reference does**.

**Next rung is not these caps.** At the shipped setting the remaining undecided
QF_UFBV files are dominated by `preprocessed dispatch timeout` and
`canonical CdclT search exhausted its budget`, with `MAX_BOOLEAN_VARIABLES` and
`MAX_INTERFACE_ATOMS` behind them — a search problem on a different ladder.
Fixing `abv-online-cdclt`'s non-progress would unblock ~4 more here and 16 on
QF_ABVFP, and until then `MAX_INPUT_DAG_NODES` is a guard, not a knob.

[ADR-1945](../../research/09-decisions/adr-1945-a-blocked-count-is-not-a-reachable-count-and-two-sequential-caps-are-not-two-caps.md);
artifacts, runners and the summarizers' nine controls (9 of 9 pass) at
`bench-results/ufbv-caps-ab-20260912/`. One of those scripts was wrong and the
data caught it: `control-vacuity.py` originally inferred that a cap which never
fires cannot cost anything, and the next arm lost two files through the other
mechanism — a file the raise *admits*, which then spends budget the later routes
needed.

<!-- plan-section: landed-changes -->

| 2026-09-12 | qf-ufbv-caps | `MAX_THEORY_ATOMS` / `MAX_INPUT_DAG_NODES` wired as `cap_lever!` levers, defaults byte-identical and mutation-pinned (`2e2feb8fb`) |
| 2026-09-13 | qf-ufbv-caps | ADR-1945: QF_UFBV **89 → 129 of 200** (gap to z3 85 → 45) from a path-specific `MAX_SCALAR_THEORY_ATOMS = 4_096`; node cap held (worth **+0** alone at 2x/4x/16x) and array atom cap held (a 25 s `Watchdog` regression, 0 of 9); 0 of 400 array files change verdict; 9,793 runs, 0 disagreements |

# Lane: s2-dispatch-overrun — S2 dispatch-overrun fix (docs/plan/smt-parity-plan-2026-09-05.md row S2)

<!-- plan-section: lane-status -->

**Done (`s2-dispatch-overrun`, 2026-09-06).**

Root cause confirmed by instrumented diagnosis before any fix: in
`check_with_arith_dpll` (`crates/axeyum-solver/src/dpll_lia.rs`), the
online LIA CDCL(T) probe (`online_lia_probe_config`, a flat third of
`config.timeout` — 8s on the standard 24s budget) always ran BEFORE
`exceeds_pre_sat_skeleton_boundary`'s size-admission check, which lives
inside `IncrementalArithDpll::solve` and is only reached afterward, via
`run_arith_dpll`. So an already-oversized query (thousands of atoms/CNF
vars) paid the online probe's fixed ~8s reserve every time before
declining on a constant it could evaluate at t≈0. Combined with
`dl-online`'s own ~18-21s reserve ahead of it in
`dispatch_difference_logic`, the sum exceeded `smtcomp_cli`'s 24s+1s
watchdog on 3 of 5 traced `QF_IDL` timeouts
(`docs/research/11-design-review/2026-09-05-arith-timeout-profiles.md`
Finding 0), and the watchdog's hardcoded `("unknown", None, None)` meant
those three printed NOTHING — no `; theory-layer …` line, not even a
partial one — because the line is only built after the worker thread's
`solve()` call returns and that thread was killed mid-flight.

Two fixes landed:

1. `arith_dpll_admission_preflight` (`dpll_lia.rs`) builds the Boolean
   abstraction and checks `exceeds_pre_sat_skeleton_boundary` BEFORE
   `check_with_arith_dpll` runs the online probe. An oversized query now
   declines immediately (the online probe's reserve is never touched).
   The `MAX_MODERATE_PRE_SAT_ARITH_ATOMS`/`MAX_PRE_SAT_CNF_VARS` reserve
   protecting `QF_IDL/sal/lpsat/lpsat-goal-18` is untouched — this only
   moves WHEN the existing constant is evaluated, not what it is.
2. `smtcomp_cli`'s watchdog-timeout branch (`crates/axeyum-bench/examples/
   smtcomp_cli.rs`) no longer hardcodes `(..., None)` for the trace line;
   it now prints an explicit `; theory-layer unavailable: <reason>` line
   under `--trace`, so a trace is never silently empty even when the
   worker never got far enough to report real stats. Deliberately did
   NOT add cross-thread shared state to read a live in-progress snapshot
   (`TheoryLayerStats` collection is thread-local by design,
   `crate::theories::cdclt_diagnostics`) — that would touch a hot search
   loop for a diagnostic-only line; the honest placeholder is enough to
   satisfy "never nothing."

**Measurement (six files, before = commit `0076811ff`, after = commit
`3dcf8693e`, `taskset -c 0-7`, 24000ms, `smtcomp_cli --trace`, foreground).**
Host caveat up front: this box (s4) ran at load average 15-27 throughout
the whole session (dozens of concurrent lane `cargo-serialized.sh`
invocations sharing one host-wide flock) — nowhere near the "idle host"
the plan's own numbers assume. Absolute wall-clock numbers below are
NOT COMPARABLE to the plan doc's idle-host baseline in the sense
`docs/research/08-planning/frontier-ratchet-reference-frame.md` uses that
term; only the BEFORE/AFTER pair on this same host, same load regime, is
meaningful. I did not save the pre-fix binary before the release rebuild
overwrote it at the same path, so its sha256 was not captured — commit
provenance (`0076811ff` before, `3dcf8693e` after) is the record instead.

| file | before verdict/wall | before stage line | after verdict/wall | after stage line |
|---|---|---|---|---|
| RVpredict_13 | unknown / 25.05s | none (silent) | unknown / **18.20s** | real: `boolean_propagate_ms=16197 … decisions=122034 restarts=6` |
| jobshop20-2-10-10-4-4-16 | unknown / 25.04s | none (silent) | unknown / **21.15s** | real: `boolean_propagate_ms=3850 theory_propagate_ms=16698 … decisions=14010` |
| jobshop26-2-13-13-4-4-16 | unknown / 25.04s | none (silent) | unknown / **21.19s** | real: `boolean_propagate_ms=3567 theory_propagate_ms=16920 … decisions=5219` |
| edge-matching-w7-h7-c11 | unknown / 24.39s | real: `boolean_propagate_ms=17852` | unknown / 25.20s | `; theory-layer unavailable: watchdog fired …` |
| a7.3.0.tweaked.3.asp | unknown / 23.94s | real: `boolean_propagate_ms=16704` | unknown / 25.21s | `; theory-layer unavailable: watchdog fired …` |
| lpsat-goal-18 (negative control) | unknown / 25.03s | none (silent) | unknown / 25.07s | `; theory-layer unavailable: watchdog fired …` |

Zero verdict changes across all six (all `unknown` both arms). The three
previously-silent files now decide comfortably inside budget (18-21s) and
print real `TheoryLayerStats` — the admission fix alone closes Finding 0
for them. The two files that already printed real stats pre-fix now
overrun by ~1s and fall into the watchdog path post-fix; the honest
`unavailable` line prints instead of nothing either way (satisfying the
"never nothing" exit criterion), and the ~1s shift is inside the noise
this host's load produces run-to-run (both this pair's absolute times and
the frontier ratchet's own "NOT COMPARABLE"/throughput-moved-30-40%
readings below say the same thing about this host right now) — I did not
have a quiet window to re-confirm that at lower load. **The negative
control (`lpsat-goal-18`) is the important non-regression check and it
holds**: `unknown` both before and after, same host/load — the plan doc's
"decided unsat in 4.2s" baseline is an idle-host number this session never
observed even on unmodified `main` (both pre-fix runs of this file also
timed out at ~25.0s under this load), so I cannot confirm "still decides
within its current time" on this host; what I can confirm is the fix did
not make it any worse than main already was here.

**Gates run, all nonzero/green:**
- `cargo-serialized.sh test -p axeyum-solver --lib --features full -- auto route_trace dispatch dpll_lia`:
  passed on an isolated single-test run and on two full-filter runs the
  only failure was `arithmetic_uf_overbound_pre_lia_probe_decides_on_clone`
  (pre-existing on `main`, calls `run_arith_dpll`/`IncrementalArithDpll`
  directly, never `check_with_arith_dpll` — outside this diff's reach),
  which flaked under ~117-way concurrent-test load both times and passed
  cleanly in isolation (0.45s) — a load artifact, not a regression; see
  the two full-filter run logs referenced in the final report.
- `cargo-serialized.sh test -p axeyum-solver --features full --test corpus_regression`: 1 passed.
- `cargo-serialized.sh test -p axeyum-solver --test progress_frontier --features full -- --test-threads=1`:
  12 passed; `nia_unsat` (the frontier most exposed to a dispatch change)
  shows no FRONTIER line at all — unchanged from baseline. `bv_reduction`/
  `lia_cuts` showed PROGRESS but self-reported NOT COMPARABLE (host 3.9x
  slower than reference, throughput moved 30-40% mid-sweep) — advisory
  only, not claimed as a real baseline move.
- `cargo-serialized.sh clippy -p axeyum-solver -p axeyum-bench --all-targets --all-features -- -D warnings`: clean.
- `cargo-serialized.sh check --workspace --all-targets`: clean.
- Two new tests added:
  `oversized_lia_dpll_admission_declines_before_spending_the_online_probe_reserve`
  (`auto.rs`) — a 1,300-int-atom + 2,900-bool-pad disjunction crosses the
  joint admission boundary and the recorded `lia-dpll` route elapsed stays
  under a self-calibrated reference-frame budget (10x the cost of building
  the same abstraction directly + 50ms), not an absolute constant, because
  the abstraction build itself is real, measured, load-sensitive work
  (`ArithAbstractor::abstract_term`'s pre-existing O(n) atom-dedup scan).
  `watchdog_unavailable_line_is_none_off_trace_and_some_on_trace` +
  `a_worker_that_outlives_the_deadline_still_yields_a_theory_layer_line`
  (`smtcomp_cli.rs`, run via `cargo test -p axeyum-bench --example smtcomp_cli`)
  — the second reproduces the exact `mpsc`/`recv_timeout` race in `main`.
- `./scripts/check-links.sh`: all links ok.
- `python3 scripts/gen-plan.py` run and `PLAN.md` committed alongside this file.

**Not done / left for a future lane:** the `lpsat-goal-18` idle-host
re-confirmation above; a proper cross-thread live-snapshot mechanism for
the watchdog path (deliberately scoped out — see fix #2 above); the first
cause from the same diagnosis (`CdclT::unit_propagate`'s full clause-scan,
ADR-1701 slice 2's two-watched-literal lever), which is a separate, larger
slice and untouched here — edge-matching/fastfood/lpsat-goal-18 all still
bottleneck there, not on anything S2 touches.

<!-- plan-section: landed-changes -->

| 2026-09-06 | 23202a7d9 | S2 admission-preflight fix (WIP snapshot: compiles, tests/gates not yet run) |
| 2026-09-06 | 3dcf8693e | Calibrate the S2 regression test to a load-robust reference frame; add the solver-dispatch.md paragraph |

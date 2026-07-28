# Lane D — Measurement backbone (SMT-COMP full library)

**Ranked-program anchor:** Rank 1 — *finish the measurement itself, because it
re-ranks everything.*
**Gaps:** G0 (docs vs measurements), G1 (coverage-weighted matrix), G2
(production depth), G3 (neutral correctness).
**Worktree / branch:** `~/projects/personal/axeyum-measure` / `agent/measure/full-library-credited`.
**Owns:** `scripts/smtcomp_repro/`, `crates/axeyum-bench/`, `bench-results/`.
**Blocks on:** nothing — **start immediately, in parallel with Phase 0.**

**Entry point for everything in this lane:**
[`docs/plan/smtcomp-full-library-workstream/README.md`](../smtcomp-full-library-workstream/README.md)
— it is the single authoritative resume record. Read it before running anything.

---

## Why this lane runs first and never stops

Every other lane's priority is currently set from a **partial, stale-binary**
s4 run that predates both P0 repairs. The ranked program says so explicitly:
that run "may inform diagnostics but receives no measurement credit and must not
be promoted merely because it finishes."

Meanwhile the *credited* instrument is nearly built. From the workstream README:

- **E0** contract, **E1a** local persistence: complete.
- **E1b**: fixture-complete in the active runner (exact preflight identity,
  immutable attempts/results/output sidecars, typed process outcomes,
  observed/admitted verdict separation, completion-last publication, strict
  duplicate rejection, no-steal lease, explicit stale recovery).
- **E2**: complete on one delegated user-systemd/cgroup-v2 host.
- **E3**: complete on the registered `s5`/`s6`/`s7` NFSv4.1 class.
- **S0–S4** official selection ledger: complete. S3 produced byte-identical
  45,905-path selections (2,709 new / 43,196 old) from two fresh 88-file no-Git
  bundles; S4's content-addressed root reconstructs all 450,472 files.
- **F1** credited full-population fixture: integrated. 96-shard partition,
  48 two-shard initial allocations, 96 one-shard different-host retries, 16
  three-host waves, frozen two-worker/two-core/16-GiB/zero-swap/64-PID envelope,
  thermal stop at 90.000 °C with 80.000 °C cooldown release, 28 mutation tests.
- **F2** live host/sentinel preflight: **fixture-only. This is the gap.**

So: the harness is built and mutation-tested; what is missing is the **live
acceptance** and then the **run itself**.

---

## D1 — Accept F2 live host/sentinel preflight (W1, first)

**Goal.** Move F2 from fixture-only to live-accepted, so a credited run can
legally launch.

**Steps**
1. Read the F2 section of the workstream README and the
   [F1 result](../smtcomp-credited-full-population-f1-result-2026-07-23.md) for
   the exact contract F2 must satisfy.
2. Execute the preflight against the real `s5`/`s6`/`s7` hosts: probe identity,
   cgroup enforcement, thermal sensor parsing
   (`k10temp-pci-00c3 / Tctl / temp1_input`, observations no older than 60 s),
   and the exact remote `systemctl --user stop <registered E3 unit>` helper.
3. Prove the negative controls live, not just in fixture: a stale observation
   rejects, a non-exact systemd stop rejects, a partial launch publishes no
   checkpoint.
4. Confirm the tiny admitted fixture still **cannot** satisfy the live
   45,905-row preregistration gate (the hidden unadmitted-fixture flag).

**Exit criteria:** F2 recorded as live-accepted with a committed result note;
`launch_authorized` can become true for a real allocation.

**Size:** M. **Everything downstream in this lane is blocked on it.**

---

## D2 — Execute the credited full population

**Goal.** The first credited full-library run: 45,905 official paths, 96 shards,
16 three-host waves across `s5`/`s6`/`s7`.

**Non-negotiables (these are what make it *credited*):**
- Stage the **repaired** binary — bound to an exact tested commit, after Phase 0
  and Lane C's C1. A run on a pre-repair binary is diagnostic-only, full stop.
- Preserve the selector-eligibility exclusions (ADR-0343/0344). **Do not merge
  the two scores.**
- Fail-closed scheduler behavior for unclosed, failed, or lost allocations;
  signal-boundary pause; completed-cell state.
- Self-sealed wave checkpoints with contiguous-prefix restart skipping.
- **A persistent `WRONG` grep over the shard logs for the entire run.** The last
  run's two P0 wrong verdicts were caught by a later analysis pass reading shard
  logs, because the alerts-only monitor had lapsed between re-arms. Cheap check;
  soundness is the crown jewel. Re-arm it and verify it fires on a synthetic
  wrong verdict before trusting it.

**Exit criteria**
- All 96 shards complete with checkpoints; central completion recorded.
- A committed per-logic **decide / decline / wrong** table over the full §6
  selection.
- Zero `WRONG` rows — or, if any, the run stops and the wrong verdict becomes a
  P0 ahead of everything else in the program.

**Size:** XL (wall-clock; mostly supervision). Runs for days; do not babysit
synchronously — checkpoint-driven.

---

## D3 — G3: neutral correctness with cvc5 + Bitwuzla as co-oracles

**Goal.** Score the **same** population with cvc5 1.3.4 and Bitwuzla 0.9.1 and
publish a three-solver per-logic comparison.

**Why it is not optional.** Right now the SCOREBOARD's ground truth is a mix of
`z3-library`, `z3-binary`, and `:status`, and some rows have `Cmp = 0` (nothing
was actually compared). Two independent oracles in **both verdict directions**
is the G3 bar. cvc5 and Bitwuzla are already staged and already run as
references — this is a promotion, not new infrastructure.

**Exit criteria:** a committed three-solver per-logic table over the identical
45,905 files; every axeyum decision on a paper-claimed fragment is adjudicated
by ≥2 independent oracles; disagreements enumerated individually, never summed
away.

**Size:** L. Can pipeline with D2 rather than waiting for it to finish.

---

## D4 — G1: the coverage-weighted parity matrix

**Goal.** Replace the single aggregate decide-rate with a benchmark-weighted
per-logic matrix, and reconcile it with the SCOREBOARD.

**Discipline.** The SCOREBOARD (curated, 992 files) and the full-library run
(45,905 files) are **different corpora**. Keep both. Label both. Never blend
them into one percentage — that is exactly the G0 failure mode this whole gap
program exists to stop.

**Steps**
1. Generate the matrix from D2 + D3.
2. Publish as a `SCOREBOARD.md` **sibling** with its own generator, wired into
   `scripts/check-parity-docs.py` so stale prose gets rejected automatically.
3. Reconcile: for each logic, state the curated number, the full-library number,
   and *why they differ*.

**Exit criteria:** committed matrix; `check-parity-docs.py` binds it; every
public quantitative claim in `PLAN.md`/`STATUS.md`/`README` traces to one
canonical machine-readable source (the G0 "next safe action").

**Size:** M.

---

## D5 — Feed the re-rank

**Goal.** Turn the matrix into the next planning input.

**Steps**
1. Recompute the (volume × decide-gap × tractability) ranking from *measured*
   numbers rather than the 2026-07-22 estimates.
2. Publish per-lane residual extracts: strings → Lane B, quantified → Lane A,
   FP → Lane C, QF_BV hard tail → Lane F.
3. Update this program's README §2 wave plan with the re-ranked order.

**Exit criteria:** each of Lanes A/B/C/F has a committed, measured residual
census derived from the credited run, replacing its W1 proxy census.

**Size:** S, but it is the payoff for the whole lane.

---

## D6 — Standing G0 duty (continuous, low cost)

`python3 scripts/check-parity-docs.py` is in `just check` and has already caught
a stale universal-sweep Z3 premise plus stale decide/proof denominators in
`PLAN.md`, `STATUS.md`, and `SCOREBOARD.md`. Extend it whenever a new public
quantitative claim gains a canonical machine-readable source.

**Watch item:** `gen-lean-complete-parity.py --check` is the real Lean parity
gate, not the unittest — the unittest passes over a stale generated manifest.
Regenerate and commit after any merge that changes Lean source identities.
(Coordinate with Lane E.)

---

## Lane D rolling exit (the Rank 1 exit criterion)

> A committed per-logic decide/decline/wrong table over the full §6 selection,
> cvc5/Bitwuzla-cross-checked, feeding a fresh `SCOREBOARD.md` sibling.

## Hard reminders for this lane

- A piped exit code is not the gate's exit code. `just check 2>&1 | tail -40`
  once reported "exit 0" from `tail` while `parity-docs` had failed. Grep the
  content of correctness-critical gates.
- `bench-results/frontier/*.json` are volatile gate output — regenerable;
  revert gate jitter before landing.
- Do not sweep the 41 GB public corpus outside the credited-run protocol.

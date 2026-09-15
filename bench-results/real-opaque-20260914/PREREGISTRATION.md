# REAL-OPAQUE — pre-registration

Lane `real-opaque`, ADR-2065. Written and committed **before any number in this
directory was produced**, and before the A/B binary was built. Branch base
`git merge-base main HEAD` = `30e2a670720a10e302f53555f12709a92002b9c3`, which
**is** local `main`'s HEAD at the time of branching.

## What preceded this file

The code landed first, at `7df00fd82` — the `Sat`-exit enumeration and its three
closures (§1 below). That ordering is deliberate and is stated so nobody has to
guess: **the soundness work is not conditional on the measurement**, and the
measurement rules are fixed before the measurement. Nothing under `ref/` or
`ab/` existed when this file was committed.

## The subject

ADR-2050 cause (A): `lra.rs::linearize` refused the WHOLE query on meeting a
real subterm it could not linearize. In `AUFLIRA` those subterms are
applications of *declared* `log` / `divide` and array reads `(select a i)` —
plain opaque reals. Six of eleven `CAPABILITY-LIMIT` rows, one site.
Wilson 95 % on 6 of 11 is **[31.3 %, 83.2 %]**; that interval, not a point
estimate, is what n = 11 supports.

**ADR-2050's +6 is a SIMULATION run outside the solver** (`opaqueatom.py`
rewrote the skeleton file and fed it back). It is not a measurement of shipped
code and is not quoted as one anywhere in this lane. The A/B below replaces it.

## 1. The `Sat`-exit enumeration is the deliverable, not the lever

Pre-registered before writing the collector: **if the `Sat` exits cannot be
closed, this lane ships the enumeration and no lever.**

Method — **mechanical, by construction site, not by `?`-scan** (ADR-1966 found a
`?`-only scan under-reports refusal propagation by half):

- **E1.** Enumerate every construction site of `lra::Collector` in the
  workspace. The flag is `false` on `Collector::default`, so a site that does
  not name it cannot reach the abstraction.
- **E2.** Enumerate every caller of the one collection function that can set it.
- **E3.** Enumerate every `Decision::Sat` / `CheckResult::Sat` construction
  reachable from those callers.
- **E4.** Enumerate the consuming routes in `dpll_lia` (the route that refuses).

Recorded in `ref/sat-exits.md` with the exact commands. A derived test
(`lra_sat_exit_sites_are_the_enumerated_ones`) re-derives E3's count from the
source rather than from a literal, so a new `Sat` site fails the suite.

## 2. Decision RULES, fixed now

Not a conversion rate — ADR-2050's 6/6 was a simulation and predicting it here
would be predicting the instrument.

- **R1** Population is the **pinned, pre-existing** `bench-results/parity-lists/AUFLIRA.txt`
  (200 files, full-span, committed at `3320c7136` before this lane existed). It
  is not re-sampled, filtered, or sorted by this lane. **A prefix is never
  read** — the list is path-sorted, and a prefix cannot show the effect.
- **R2** **Interleaved per file, one binary, two env values.** Both arms run
  back to back on the same file on the same pinned core, arm order alternating
  per file. Never two builds.
- **R3** **POLARITY.** `AXEYUM_LRA_OPAQUE_APPS` is a **KILL SWITCH** (`=0`
  disables); the rung ships ON. So the BASE arm is `AXEYUM_LRA_OPAQUE_APPS=0`
  and the LEVER arm is `env -u AXEYUM_LRA_OPAQUE_APPS`. This is inverted
  relative to a normal opt-in flag, exactly as ADR-2025's is, and is stated in
  the runner's header. A preflight asserts the two arms differ by MECHANISM on
  at least one file before any measuring starts; if they do not, the run is
  void.
- **R4** **EXIT-STATUS channel, not just verdicts.** Every run records its own
  outcome (`ok` / `wrapper-killed` / `rc134` address-space cap / `sigkill` /
  other rc). ADR-2045's arm was `losses=0` by verdict count while creating five
  new aborts on files that terminated cleanly in the base; a verdict count
  cannot see that. **A base-`ok` row that is non-`ok` in the lever arm is a
  LOSS even when both verdicts read `unknown`.**
- **R5** **Every moved row re-run 3× per arm**, classified STABLE-GAIN /
  STABLE-LOSS / UNSTABLE / FLIP. A row is counted only if STABLE.
- **R6** **Noise floor on a whole division, same arm, repeated.** Assume the
  band is not zero until measured. The gain must exceed it.
- **R7** **Control division that must not move**: `QF_LRA` (200, pinned).
  Non-vacuity is a REQUIREMENT, not a hope, and is discharged by MECHANISM:
  the control's rows execute `lra::decide_within_with_options`,
  `Collector::index_of`, `variable_count` and `simplex_fallback` — every
  function this change edits — while the opaque arm structurally cannot fire
  (no real UF application, no array). So it is the division where the
  column-space refactor (`vars.len()` → `variable_count()`, and
  `simplex_fallback`'s model keying) would show up if it were wrong. The route
  binding its undecided rows is named and verified to execute in
  `ref/control-nonvacuity.tsv`.
- **R8** **Authorities, comparable denominator beside any zero** (ADR-1957).
  Every NEW verdict is re-checked against `z3` and `cvc5`, **no-opinion counted
  separately from agreement**, using
  `bench-results/dt-exactness-20260913/verify-new-verdicts.sh`.
  `z3 -T:` is SECONDS, `cvc5 --tlimit` is MILLISECONDS. References measured on
  an IDLE host (ADR-2045's first reference pass read z3 = 155 against the
  board's 166 because it ran six concurrent shards).
- **R9** **A sat-side reference control is vacuous** (ADR-1976). The rewrite is
  controlled on the **unsat** half. For any `sat`, the evidence is model replay
  against the ORIGINAL assertions — and ADR-2010 found the front door's replay
  does not cover parser-level rewrites, which is one more reason this
  abstraction is confined to the solver and never rewrites the query.
- **R10 SHIP GATE.** Ship ON only at: **≥ 4 net rows**, **0 losses** (verdict
  OR exit status), **0 flips**, every moved row STABLE-GAIN over 3 passes per
  arm, **0 authority disagreements**, control at **0** and shown non-vacuous,
  and the gain above the measured noise floor. Missing any of these, the
  default flips to OFF and the lever ships `Off` with the measurement attached.
- **R11** **The A/B measures THIS BRANCH.** The post-merge value is predicted
  in the ADR before the merge.
- **R12** Freshness by `find -newer`, not exit status. Snapshot/target paths are
  reused; a fast build with an old binary mtime means force a rebuild.
- **R13** No waiter greps for a process by a pattern its own command line
  contains.
- **R14** Any unfinished check is reported as **"did not run"**, never as a
  zero and never as an intention.
- **R15** `ulimit -v` on every run. Not because it makes anything finish — it
  converts a crash into a bounded failure, and a global OOM from a lane's
  expander killed a session on this box.

## 3. Predictions, recorded now

| | prediction |
|---|---|
| **P1** | The `Sat` exits ARE closable, and the enumeration is **small** — under 10 sites — because the flag is `false` by `Default` and only one function can set it. |
| **P2** | The integer precedent's soundness argument **transfers verbatim** (both are relaxations); the difference will be in the CONSUMERS, not in the argument. |
| **P3** | **Fewer than 6 of the 6 `AUFLIRA` witnesses convert on the shipped code.** The simulation fed the ground checker a rewritten *skeleton*; the shipped path must reach it through the quantifier rung, and ADR-2050 cause (D) is precisely a case where the rung does not hand the ground checker what the census's abstraction describes. |
| **P4** | The control moves **0**, and `QF_UFLRA` (not a control — reported as a secondary) moves by a **nonzero** amount, because real UF applications are its defining feature. |
| **P5** | At least one **loss** somewhere in `AUFLIRA`: admitting an atom stops `lira-dpll` refusing, which takes the query away from a LATER route that could have decided it. This is the risk the ladder makes real and the reason the exit-status channel is mandatory. |

## 4. Hosts

At most **4 pinned pairs**, named here: `s5` cores 2,3 · `s6` cores 2,3 ·
`s7` cores 2,3 — three hosts, two cores each, so no more than 6 slots are ever
live and the reference passes get an idle host. Announced because s5/s6/s7 are
shared with two concurrent lanes.

# Agent Program — 2026-07-28

**Purpose.** Turn the current measured state into a set of *discrete, parallel,
exit-criteria'd task queues* that independent sub-agents can pick up and run
without colliding. This folder is a **dispatch layer**, not a new roadmap: every
task here points back to an existing phase in
[`docs/plan/track-*/`](../README.md) and inherits that phase's semantics.

Authority order (where these conflict, the earlier wins):

1. [`bench-results/SCOREBOARD.md`](../../../bench-results/SCOREBOARD.md) — generated, measured, authoritative for decide-rate.
2. [`PLAN.md`](../../../PLAN.md) — the single live tracker, current focus, and
   ordered work queue.
3. [`docs/plan/full-library-gap-closing-plan-2026-07-22.md`](../full-library-gap-closing-plan-2026-07-22.md) — the ranked program (Rank 0–8) this dispatch layer implements.
4. This folder — sequencing, ownership, and per-agent briefs.

Base commit for the whole program: **`ffc466b4`** on `main`.

> ## Phase 0 is COMPLETE (2026-07-30). Read this before the tables below.
>
> `just check` is **green on `main`**, content-verified — and it was **red before
> this program started**, for two independent pre-existing reasons.
>
> **The §1 table below is the 2026-07-28 snapshot and is now stale in three
> places.** Corrected:
>
> | Axis | Was stated | Actually measured |
> |---|---|---|
> | Curated decide-rate | 753 / 992 | **762 / 992**, DISAGREE = 0 |
> | QF_SLIA curated | 18 / 50 = 36 % | **25 / 50 = 50 %** |
> | QF_S curated | 87 / 134 = 65 % | **93 / 134 = 69 %** |
> | QF_SEQ curated | 26 / 33 = 79 % | **22 / 33 = 67 %** (baseline was *over*-stating) |
> | Noetzli 1,880 | "not on `main`" | **on `main`**, 1,880/1,880 |
> | `string_bound` frontier | 8 | **12** (baseline 8) |
>
> **The single most important correction is to fact 2 in §1.** It assumed the
> stale SCOREBOARD hid gains the Phase 0 strings work would reveal. Re-measuring
> at both `ffc466b4` and current `main` gave **identical** numbers on all three
> curated rows, so the Noetzli work moved them by **exactly zero** — the gains and
> the QF_SEQ regression both predate it. **Lane B must be re-scoped against the
> measured residual, not against the Noetzli figure**: QF_SLIA 21 unsupported + 4
> unknown, QF_S 32 + 9, QF_SEQ 10 unknown concentrated in the P2.7 A.2
> bounded-unsat gate. Full record:
> [`strings-remeasurement-2026-07-29.md`](../strings-remeasurement-2026-07-29.md).
>
> Landed beyond the two live lanes: **ADR-0374** (quantified-BV skolemized
> negated universals now carry a witness certificate — an *evidence*-coverage
> gain, not decide-rate), **ADR-0373** (source FP prefix refuter, with its
> parse-time `2^k` blowup bounded), and the **qfslia regex-membership half**
> (credited at zero movement / zero loss; its Kaluza/PyEx claims are
> [deliberately uncredited](../string-corpus-provenance-2026-07-30.md)).
>
> Defects found and fixed that nothing was catching: one **P0 wrong-`unsat`**
> introduced by the Phase 0 merge itself; one **pre-existing uncertified
> quantified-BV `sat`**; a `gen-scoreboard.py --check` that was a **silent
> no-op**; three **generated views drifted from their own sources**; a harness
> oracle **adjudicating the bounded encoding instead of the source**; and **two
> flaky gates**. Worktrees 21 → 5.
>
> Rules 6–8 in §4 were rewritten from these failures. Read them before running
> anything.

---

## 1. Where we actually are (measured, 2026-07-28 — see the correction above)

| Axis | Committed number | Source |
|---|---|---|
| Curated decide-rate vs z3 4.13.3 | **753 / 992 = 76 %**, 35 baselines, 24 logics | SCOREBOARD |
| Soundness floor | **DISAGREE = 0** over 680 oracle-compared | SCOREBOARD |
| Strings — QF_SLIA (curated cvc5-regress) | **18 / 50 = 36 %** | SCOREBOARD |
| Strings — QF_S (curated cvc5-regress) | **87 / 134 = 65 %** | SCOREBOARD |
| Strings — Noetzli fixed population | **1,880 / 1,880 = 100 %** (26 SAT / 1,854 UNSAT) | `agent/solver/uflia-main-next` @ `e6f393d8` — **not on `main`** |
| Strings — PyEx fixed selection | **1,730 / 2,535** at 250 ms / 750 ms | STATUS 2026-07-26 |
| Quantifiers — UFLIA cvc5-UNSAT gap (765 rows) | **133 UNSAT**, zero retained loss | STATUS 2026-07-26 |
| Quantified logics in SCOREBOARD (UF, LIA-quant) | **0 %** | SCOREBOARD |
| QF_BVFP ESBMC hard tail | **34 / 34**, DISAGREE 0 | STATUS 2026-07-27 |
| QF_FP custom `binary79` (15,64) | **8 / 8** (4 SAT / 4 UNSAT) vs Z3 | ADR-0368/0369/0370 |
| QF_FP 108-family diagnostic | 88 correct / 18 unknown / 2 outer timeouts / **0 wrong** | STATUS 2026-07-27 |
| Lean full conjunction | **259 / 327** decided-UNSAT carry the complete evidence chain | STATUS |
| Official-Lean fail-closed gate | **70 / 70** local, remote attestation **open** | `official-lean-ci-gate-audit-2026-07-21.md` |
| Full-library selection | 45,905 official paths, 96 shards, hosts `s5`/`s6`/`s7` | `smtcomp-full-library-workstream/README.md` |

### The three facts that drive this program

1. **There is completed, unmerged capability sitting in worktrees.** The
   1,880/1,880 Noetzli QF_SLIA slice is seven commits on
   `agent/solver/uflia-main-next` and has never touched `main`. Nothing else
   should start until it lands — it edits `crates/axeyum-smtlib/src/parse.rs`
   (+1,845 lines), which a second live lane also edits (+417 lines).
2. **The measured scoreboard and the lane reports describe different
   populations.** Lane work reports 100 % on Noetzli and 68 % on PyEx; the
   authoritative SCOREBOARD still reads 36 % QF_SLIA / 65 % QF_S because those
   rows have never been re-measured with the landed mechanisms. Until they are,
   *we do not know* what strings actually cost us.
3. **The library is weighted where we are weakest.** QF_SLIA (84,395) + QF_S
   (18,940) is ~24 % of the library; the quantified block (AUFLIRA 20,011 +
   UFNIA 13,464 + AUFDTLIRA 11,043 + UFLIA 10,128 + …) is >100k benchmarks at
   ~0 % decide, where cvc5 decides 57 % of UFLIA. Those two blocks are Ranks 2
   and 3 of the ranked program and they are where the agents go.

---

## 2. Lane map

Seven work units. **Phase 0 is serial and blocking**; Lanes A–F run in parallel
after it, one agent per lane, one worktree per agent.

| Lane | Title | Ranked-program anchor | Phases | Blocks on | Brief |
|---|---|---|---|---|---|
| **0** | Integration & tree hygiene | — | — | nothing | [phase-0-integration.md](phase-0-integration.md) |
| **A** | Quantifiers — the capability gap | Rank 3 | P2.6, T2.6.1/2/5 | Phase 0 | [lane-a-quantifiers.md](lane-a-quantifiers.md) |
| **B** | Strings — the volume gap | Rank 2 | P2.7, P2.7a | Phase 0 | [lane-b-strings.md](lane-b-strings.md) |
| **C** | Floating point | Rank 0 residual + P2.8 | P2.8 | Phase 0 | [lane-c-floating-point.md](lane-c-floating-point.md) |
| **D** | Measurement backbone | Rank 1 (G0–G3) | P4.5, S0–S4, E1–E3, F1–F2 | nothing | [lane-d-measurement.md](lane-d-measurement.md) |
| **E** | Lean parity & certified evidence | Rank 7 (G5/G6/G7) | P3.x, TL x.y | nothing | [lane-e-lean-evidence.md](lane-e-lean-evidence.md) |
| **F** | Engine keystone & QF_BV hard tail | Ranks 4 + 6 | P1.1, P1.2, P1.5 | Phase 0 | [lane-f-engine.md](lane-f-engine.md) |

### Dependency graph

```
Phase 0 (integration, serial, blocking)
   |
   +--> Lane F ---- F1 CDCL(T) default dispatch ADR ----+
   |                                                     |
   |                                          (unblocks) v
   +--> Lane A (quantifiers) <---------------------------+
   +--> Lane B (strings)     <---------------------------+
   +--> Lane C (floating point)

Lane D (measurement)  -- independent, starts immediately, RE-RANKS A/B/C/F
Lane E (Lean/evidence) -- independent, starts immediately
```

Lanes A and B can start their *census and mechanism* tasks before F1 lands; only
their deep CDCL(T)-resident work is gated on it. Lane D's output is what
re-ranks A/B/C/F after wave 1 — treat its per-logic table as the next planning
input, not as a nice-to-have.

### Wave plan

| Wave | Runs | Gate to exit |
|---|---|---|
| **W0** | Phase 0 alone | `main` green under `just check`; live lanes merged; stale worktrees pruned |
| **W1** | A1, B1, C1, D1, E1, F1 (all census / ADR / validation tasks) | each lane has a *measured* residual census committed as an artifact |
| **W2** | A2–A3, B2–B3, C2, D2–D3, E2–E3, F2–F3 | capability increments landed, each with its own no-loss gate |
| **W3** | re-rank from Lane D's per-logic table, then A4+, B4+ | fresh SCOREBOARD sibling + coverage-weighted matrix |

---

## 3. Ownership map — the anti-collision contract

One writer per crate-area. If your task needs a file outside your column, **stop
and hand off through the integrator (Phase 0 owner)** rather than editing it.

| Lane | Owns (write) | May read, must not write |
|---|---|---|
| A | `crates/axeyum-solver/src/quant_*.rs`, `crates/axeyum-egraph/`, quantifier tests | `axeyum-strings`, `axeyum-fp` |
| B | `crates/axeyum-strings/`, string tests, `axeyum-smtlib/src/parse.rs` **string regions** | FP regions of `parse.rs` |
| C | `crates/axeyum-fp/`, FP routes in `axeyum-solver/src/`, `axeyum-smtlib/src/parse.rs` **FP regions** | string regions of `parse.rs` |
| D | `scripts/smtcomp_repro/`, `crates/axeyum-bench/`, `bench-results/` | all solver crates |
| E | `crates/axeyum-lean-kernel/`, `crates/axeyum-lean-import/`, `crates/axeyum-alethe/`, `axeyum-solver/src/evidence.rs` | all theory crates |
| F | `crates/axeyum-cnf/`, `crates/axeyum-bv/`, `crates/axeyum-aig/`, `axeyum-rewrite/` preprocess, solver dispatch | theory-specific routes |

**`crates/axeyum-smtlib/src/parse.rs` is the known hot file.** Lanes B and C both
legitimately extend it. Rule: B and C must each announce the *function-level*
region they are editing in their lane brief's "in-flight" section before the
first commit touching it, and rebase on `main` before every push. If both need
the same function, C yields (B carries more volume).

**Shared mutable file.** Root `PLAN.md` is the only project-level mutable
tracker and is integration-owner managed. Topic lanes record detail in owned
result notes and propose a bounded PLAN update at handoff; they do not append
competing live queues. `bench-results/
frontier/*.json` is **volatile gate output** — the benchmark gates rewrite it;
revert gate jitter before landing (see Phase 0 T0.4).

---

## 4. Standing rules for every agent in this program

These are the project's Hard Rules restated as a pre-commit checklist. A task is
not done until every applicable line is true.

1. **No wrong verdict, ever.** `unknown` is a first-class result. Every new
   `sat` route replay-checks the lifted model against the *original* term;
   every new `unsat` route carries an independent checker or an explicit,
   ledgered trust note.
2. **Underspecified operators carry a fuzz seed-class that generates the
   degenerate argument.** A corpus sweep plus a fuzz that avoids the corner is
   not a soundness gate (precedent: `a946f925` div-by-constant-zero,
   `ba0d9149` string escapes).
3. **Bounded or it does not ship.** Every path degrades to `Unknown` under a
   deterministic resource bound. Add the bound before the feature.
4. **No-loss gate.** Every capability increment re-runs its population and
   proves *zero retained decisions lost and zero verdict flips*, not just a net
   gain. Report the conservative floor across runs, never the best run alone.
5. **Pathspec-only commits.** `git add <files>` then `git commit -m … -- <files>`;
   verify with `git show --stat`. Never `git stash`, never `cargo fmt`
   (use `rustfmt --edition 2024 <file>`), never touch a dirty file you do not own.
6. **Pre-merge gates** (all foreground, owned by the agent that runs them):
   ```sh
   cargo test -p axeyum-solver --test corpus_regression   # ~6s, any string-route change
   cargo test --workspace --lib                            # ~30s, any solver change
   cargo test -p axeyum-solver --test progress_frontier    # ~60s, any decider/dispatch change
   just check-scope                                        # scoped gate vs main
   just check                                              # REQUIRED before a merge to main
   ```
   **The first three are not sufficient for a merge.** They are change-class
   gates. `cargo test --workspace --lib` covers **lib targets only**, so every
   integration test under `crates/*/tests/` is invisible to it — and on
   2026-07-28 exactly that gap let a merge land on `main` that broke
   `string_replace_over_cap_declines` in `crates/axeyum-smtlib/tests/smtlib.rs`.
   Run the full `just check` **before** the merge, not after.
7. **Verify gate output by content, never by exit code.** A piped exit code is
   the pipe's, not the gate's — `just check 2>&1 | tail -40` once reported
   success from `tail` while `parity-docs` had failed. A backgrounded wrapper's
   exit code is likewise the wrapper's: on 2026-07-28 a task notification
   reported "exit code 0" for a `just check` that had actually failed with 101.
   Write the real status into the log (`echo "EXIT=$?" >> log`) and grep the log
   for `^error`, `test result: FAILED`, and `panicked`.
8. **Build caps on this host:** `CARGO_BUILD_JOBS=1`, `--jobs 1`, and **one
   cargo invocation at a time**. `CARGO_BUILD_JOBS` bounds parallelism *within*
   a single cargo, not across two — running a `just check` and a test build
   concurrently OOM-killed this host on 2026-07-28. Run anything that might blow
   up under `MEM_LIMIT_GB=<n> scripts/mem-run.sh …` so it aborts cleanly at the
   cap with a usable diagnostic instead of taking the machine.
9. **ADR before public surface.** New operator, rewrite class, encoding,
   backend, evidence artifact, or logic fragment ⇒ an ADR in
   `docs/research/09-decisions/` first. Decisions are not made silently in code.
10. **Record the result.** Every increment lands a dated result note under
    `docs/plan/` and updates the owned row/current evidence in root `PLAN.md`.
11. **Do not sweep the 41 GB public corpus to "make progress."** Measure once on
    a committed slice, then stop.

---

## 5. Worktree and branch assignment

The integration checkout `~/projects/personal/axeyum` stays on `main` and is
owned by the Phase 0 / integrator role. **No topic agent works in it.**

| Lane | Worktree | Branch |
|---|---|---|
| A | `~/projects/personal/axeyum-quant` | `agent/quant/mbqi-sat-direction` |
| B | `~/projects/personal/axeyum-strings` | `agent/strings/qf-slia-breadth` |
| C | `~/projects/personal/axeyum-fp` | `agent/fp/binary79-residual` |
| D | `~/projects/personal/axeyum-measure` | `agent/measure/full-library-credited` |
| E | `~/projects/personal/axeyum-lean` | `agent/lean/evidence-closure` |
| F | `~/projects/personal/axeyum-engine` | `agent/engine/cdclt-dispatch` |

Create after Phase 0 lands, from the *new* `main`:

```sh
cd ~/projects/personal/axeyum && git fetch origin
git worktree add ../axeyum-quant -b agent/quant/mbqi-sat-direction origin/main
# … one per lane
```

Full model and discipline:
[`docs/contributor-guide/multi-agent-worktrees.md`](../../contributor-guide/multi-agent-worktrees.md)
and
[`multi-agent-operations.md`](../../contributor-guide/multi-agent-operations.md).

---

## 6. Definition of done for the program

This program is complete when all of the following are committed and green:

- A **credited** full-library run over the 45,905-path official selection, with
  a per-logic decide/decline/**wrong** table and cvc5 + Bitwuzla as co-oracles
  (Lane D → G1/G3).
- Strings: QF_SLIA and QF_S SCOREBOARD rows re-measured with the landed
  mechanisms, and the s4-selection decide-rate within 10 points of the measured
  cvc5 baseline, DISAGREE = 0 (Lane B, Rank 2 exit).
- Quantifiers: UFLIA/AUFLIA/AUFLIRA decide-rate off the floor with a measured
  fraction approaching cvc5's on the same selection, zero wrong (Lane A, Rank 3
  exit).
- FP: the complete selected QF_FP / QF_BVFP / QF_ABVFP slices re-run on the
  repaired binary at DISAGREE = 0 — the outstanding Rank 0 exit criterion
  (Lane C).
- Evidence: the 58 uncertified audit-row occurrences are either closed or
  explicitly ledgered with a mechanism, and the official-Lean gate has a remote
  attestation (Lane E).
- `main` green under `just check` with no lane's work stranded in a worktree.

---

## 7. Provenance

Synthesized 2026-07-28 from `main` @ `ffc466b4`: `PLAN.md`, `STATUS.md`,
`bench-results/SCOREBOARD.md`,
[`full-library-gap-closing-plan-2026-07-22.md`](../full-library-gap-closing-plan-2026-07-22.md),
[`gap-analysis-z3-lean-2026-07-21.md`](../gap-analysis-z3-lean-2026-07-21.md),
[`smtcomp-full-library-workstream/README.md`](../smtcomp-full-library-workstream/README.md),
[`lean4-complete-parity-roadmap-2026-07-22.md`](../lean4-complete-parity-roadmap-2026-07-22.md),
[`docs/contributor-guide/gap-ownership.md`](../../contributor-guide/gap-ownership.md),
plus a direct audit of all 21 live worktrees and their unmerged commits.

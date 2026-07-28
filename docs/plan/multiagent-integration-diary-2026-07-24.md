# Multi-Agent Integration Diary — 2026-07-24

Integrator log for the three concurrent codex lanes (SMT / Lean / CAS) working in
`~/projects/personal/axeyum`. Companion to
`docs/contributor-guide/multi-agent-operations.md`. Newest entry at top.

---

## 2026-07-24 — Major consolidation + agent reset

### Macro (what changed on `main`)
`main` advanced `2be1e688 → 08af3665` (pushed to `origin`), verified green by a full
`just check`. One holistic fast-forward carrying the whole backlog:

- **SMT full-library-resume batch** (29 commits): admission/coordinator/execution/
  population/readiness/multi-host harness for the credited full-library run. The
  readiness gate (`origin revision is not integrated`) resolved itself when the batch
  was merged into a `main`-based branch — the merge makes `main` an ancestor, which is
  exactly the `_is_ancestor(origin, head)` condition; no manual re-record was needed.
- **`resume_fs` de-duplication**: the lean lane had *vendored* a fork of the SMT
  filesystem primitives (`lean_vendored_resume_fs.py`) to break a self-sealing
  whole-file-hash coupling that re-broke lean parity on every SMT `resume_fs.py` edit.
  Replaced the fork with a single lane-neutral `scripts/axeyum_fsprims.py` that both
  lanes import; `canonical_bytes`/`ContractError` come from the one `resume_contract`
  authority, so lean and SMT are *guaranteed* to agree on canonical form. Proven with a
  decoupling probe (mutate `resume_fs.py` → lean seal stays green). Vendor fork deleted.
- **Gate-ergonomics fix** (see friction note below).
- **CAS wave-24 handoff doc**, the captured **frontier bench WIP** (both worktrees'
  sets backed up to the job scratch; one committed), and a regenerated
  `docs/plan/generated/lean-complete-parity.json`.
- **Branch/worktree hygiene**: 55 fully-merged branches deleted; 15 stale/scratch
  worktrees pruned (per-milestone lean rounds, ADR/profiling detached scratch, `/tmp`
  verify copies). Down to `main` + the 3 live session worktrees.

### Friction fixed (the crawl)
Diagnosed why iteration felt glacial: every change ran the full 13-gate `just check`
over the whole workspace, single-threaded, plus a ~40-min GitHub CI babysat in a poll
loop — and the two **order-255 certified-moment proofs (~15 min each)** were plain
`#[test]`s in the hot path. Fixes (all on `main`):
- `#[ignore]` the two moment proofs → `cargo test -p axeyum-cas` **~30 min → ~21 s**
  (565 passed / 2 ignored). New `just moment-proofs` runs them and is wired into the
  `check` chain, so full CI coverage is unchanged.
- `scripts/check-scope.sh` + `just check-scope`: gate only what changed vs `main`.
- Guide §3b "Iterate fast": scoped gating, `just test-guarded` (parallel, 64 GiB-capped)
  over single-thread, and *don't babysit GitHub CI*.

### Micro (lessons worth keeping)
- **A piped exit code is not the gate's exit code.** `just check 2>&1 | tail -40`
  reported "exit 0" from `tail` while `parity-docs` had actually failed on a stale
  generated file. Caught it by grepping the *content*, not trusting the status. Always
  verify content for correctness-critical gates.
- **`gen-lean-complete-parity.py --check` is the real parity gate**, not the unittest —
  it catches the stale generated manifest that the unittest passes over. Regenerate +
  commit after any merge that changes lean source identities.
- **`bench-results/frontier/*.json` are volatile gate output** — the benchmark gates
  rewrite them, so they show "dirty" across worktrees. Preserve (don't wipe) but treat
  as regenerable; revert gate-jitter before a clean landing.

### Agent reset
Confirmed the three session branches are all fully in `main` (nothing strands), worktrees
clean, WIP + review docs + corpus preserved. Stopped the old monitors and re-armed a fresh
worktree-event monitor (auto-discovers the restarts). Cleared to restart all three from
`08af3665`.

### Long-term vision + competitive tracking (to deepen each cycle)
North star: a **proof-carrying solver + CAS that is certified-or-declines, never wrong** —
parity with z3/cvc5 on the hard subsets while retaining independently-checkable evidence.
Benchmark to track: **SMT-COMP 2025** (results published) is the reference for our
quantifier (UF/UFLIA, MBQI decide-rate) and hard **QF_*** parity — QF_NRA, QF_BV, QF_NIA.
Current internal signal: the quantified-UFLIA differential decide-rate and the
`disagree=0` soundness gate (parity-docs shows `disagree=0`, `wrong=0`, 35 rows / 24 logics).
**Next cycle:** pull the per-division SMT-COMP 2025 rankings (UF single-query, NRA
single-query) to set concrete parity targets vs z3/cvc5, and record the delta here.
See `https://smt-comp.github.io/2025/results/`.

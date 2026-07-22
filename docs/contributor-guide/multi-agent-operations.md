# Multi-Agent Operations — Safe Concurrent Work

Operational companion to
[`multi-agent-worktrees.md`](multi-agent-worktrees.md) (which defines the
worktree *model*). This file records the *operating discipline* that keeps that
model from going wrong, hardened by a real multi-agent session where several of
these were learned the hard way (2026-07-22).

**One-line rule:** one worktree per agent, one branch per worktree, one
integration owner for `main`, and **nothing merges to `main` unless it is
green**.

---

## Why: what actually breaks when agents share a checkout

These are real failure modes observed when SMT-COMP + Lean-kernel + FP work all
happened inside the shared integration checkout on one feature branch:

| Failure | Root cause | Fixed by |
|---|---|---|
| Every agent's commits landed on *one* feature branch, diverging far from `main` | one checkout = one branch = one HEAD, shared by all | worktree per agent (own branch/HEAD) |
| Could not switch the checkout to `main` | `main` was checked out in another worktree (git forbids the same branch twice) | that's the model working — leave `main` where it lives |
| A merge put a **non-compiling tree on `main`** | a broken in-flight commit rode along; no build gate before merge | the **green-before-merge gate** (below) |
| `cargo fmt` / shared-index / "who owns this dirty file" | one working tree + one index shared by N writers | separate index + working tree per worktree |
| Dozens of uncommitted files from 3 lanes tangled together | everyone's WIP in one tree | isolated WIP per worktree |
| Solver processes ran unbounded and cooked a host | `pkill -f compete.py` orphaned children with non-firing timeouts | the clean-stop procedure (below) — not a git issue |

Worktrees fix the first five. The last two are **cross-worktree** and need
separate discipline (see §4).

---

## 1. The worktree layout (separate folders under `~/projects/personal/`)

One integration checkout stays on `main` and **no topic agent works in it**.
Each agent gets a sibling folder + its own branch, all sharing one `.git`:

```sh
cd ~/projects/personal/axeyum          # integration lane — on main, owned by the integrator
git fetch origin
git worktree add ../axeyum-quant   -b agent/quant/mbqi-sat-direction origin/main
git worktree add ../axeyum-strings -b agent/strings/qf-slia-decode   origin/main
git worktree add ../axeyum-smtcomp -b agent/smtcomp/full-library-run origin/main
```

```
~/projects/personal/axeyum/            # integration lane, on main, untouched by topic agents
~/projects/personal/axeyum-quant/      # topic agent, on agent/quant/...
~/projects/personal/axeyum-strings/
~/projects/personal/axeyum-smtcomp/
```

Each agent works **only** inside its own folder, on its own branch, editing
**only its own files**, committing often. No agent runs git in another agent's
folder or in the integration checkout. Clean up with `git worktree remove`.

Branch naming: `agent/<lane>/<task>` (e.g. `agent/quant/mbqi-sat-direction`).

---

## 2. Rules that still apply *inside* each worktree

Worktrees remove working-tree collisions, not object-store or format collisions:

- **Pathspec commits only:** `git add <files>` then `git commit -m … -- <files>`.
  Verify with `git show --stat`. A bare `git commit` still sweeps everything in
  *that* tree.
- **`rustfmt --edition 2024 <file>`, never `cargo fmt`** (still workspace-wide
  within a tree — it reformats files you don't own).
- **Separate `target/` per worktree.** This is the cost: each worktree builds
  its own `target/` (disk-heavy). **Do NOT** share one `CARGO_TARGET_DIR` across
  concurrent worktrees — parallel `cargo build` on a shared target corrupts it.
  For shared *compile cache* (safe), use `sccache`, not a shared target.
- **Never** `git stash` / `checkout` / `restore` / `reset` / `branch -f` on
  anything you did not create — another lane's uncommitted WIP or live worktree
  is there.

---

## 3. The green-before-merge gate (the piece whose absence broke `main`)

The red-`main` incident was **not** a git problem — it was merging a branch that
**did not compile** (a match arm was missing for a newly added enum variant).
git merged it cleanly because there was no textual conflict; the break was
semantic.

**Integration-owner rule — a branch that is not green does not merge:**

1. Preview conflicts without touching a worktree:
   `git merge-tree --write-tree --name-only main agent/<lane>/<task>`.
2. Verify the *branch* builds green — check it out in a scratch worktree (or the
   integration lane if it's yours) and run **`just check`**
   (fmt + clippy + `cargo test --workspace` + doc + link check), or at minimum
   `cargo check --workspace --all-targets`.
3. Only then merge. **One integrator decides merge order**; topic agents push
   branches and do not merge to `main` themselves.
4. After merging, re-run `just check` on `main` before the next merge — catch
   semantic merge breaks (an enum variant on branch A, a match on branch B) that
   are invisible to `git merge-tree`.

This single gate turns a divergent merge onto a live `main` from a landmine into
routine.

---

## 4. Cross-worktree resource discipline (git can't help here)

Multiple agents share more than the object store — they share the NAS corpus,
the compute hosts, and the thermal envelope. These bit us this session:

- **Compute hosts run HOT.** `s4`/`s5`/`s6`/`s7` reach **92–99 °C** under full
  core load (`s4` also runs the project `llama-server`). Run **s4 only, N≈8,
  thread-pinned** (`RAYON_NUM_THREADS=1` so workers == active cores). Never
  full-load a host; watch temps (`sensors`) and back off at ~90 °C. See the
  SMT-COMP work stream's gotchas:
  [`../plan/smtcomp-full-library-workstream/README.md`](../plan/smtcomp-full-library-workstream/README.md).
- **Orphaned solver runaways.** `pkill -f compete.py` kills the *parent* runner
  but orphans its `axeyum-smtcomp` children, whose internal `--timeout-ms` does
  **not** fire on some hard inputs → they run unbounded and accumulate across
  launch/kill cycles, saturating and overheating the host. **Always stop
  background solver fleets with `scripts/smtcomp_repro/stop_run.sh`** (kills the
  children first, then sweeps). Never leave a run stoppable only by killing
  parents.
- **Don't hammer another lane's host/worktree.** `main` and other lanes live in
  worktrees on shared hosts (`/nas4/...`, `/home/.../.cache/codex/...`); running
  a heavy build or job there competes for CPU and heat with that lane.
- **Shared NAS paths are append-mostly.** The corpus (`/nas3/data/axeyum/corpus/`)
  is read-only in practice; run outputs go under a run-specific dir. Don't
  overwrite another run's output dir.

---

## 5. Fallback: if you must share one checkout

Lightweight collaboration in one tree (e.g. a human + one agent) is sometimes
fine. Minimum safe procedure:

1. **One writer per file-area at a time** — divide by crate/dir; never two
   agents in the same file.
2. **Pathspec add/commit only**; `git show --stat` after every commit.
3. **Never** `stash`/`checkout`/`restore`/`reset`/`branch -f` on files you did
   not create.
4. **No `cargo fmt`, no workspace `cargo test`/`check`** while another agent has
   uncommitted WIP that may not compile — you'll build their broken tree (the
   red-`main` story, locally).
5. Keep the checkout on **one agreed branch**; do not fork feature branches
   inside it (that's how a shared checkout silently drifts off `main`).

---

## Quick checklist

- [ ] Working in **my own worktree folder**, on **my own `agent/*` branch**?
- [ ] Editing **only my files**; pathspec commits; `git show --stat` verified?
- [ ] `rustfmt <file>` (never `cargo fmt`); my own `target/` (no shared `CARGO_TARGET_DIR`)?
- [ ] Branch **green (`just check`)** before asking the integrator to merge?
- [ ] Background solver runs stoppable via `stop_run.sh`; host temps watched; not full-loading a shared host?
- [ ] Not touching another lane's worktree, WIP, or `main`?

---

*See also: [`multi-agent-worktrees.md`](multi-agent-worktrees.md) (the model),
[`gap-ownership.md`](gap-ownership.md) (who owns what).*

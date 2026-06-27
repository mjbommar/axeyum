# Multi-Agent Worktrees

This note records the operating model for multiple agents or humans working on
Axeyum at the same time.

The short version: use separate git worktrees, use separate topic branches, and
keep one integration owner for `main`.

## Why

Axeyum has a few high-conflict files:

- `PLAN.md`
- `STATUS.md`
- `Cargo.toml`
- solver core files such as `crates/axeyum-solver/src/incremental.rs`
- broad planning docs under `docs/plan/` and `docs/research/08-planning/`

Two agents editing the same checkout or both pushing directly to `main` can
silently overwrite context, duplicate work, or force noisy conflict resolution
in exactly the files that carry session state. Worktrees keep filesystem state
separate while still sharing one local object database.

## Recommended Layout

Keep one checkout as the integration lane and create one worktree per agent or
task:

```text
axeyum/                    # integration checkout; main owner works here
axeyum-codex-rules/         # topic worktree for a docs/rules task
axeyum-agent-solver/        # topic worktree for solver work
axeyum-agent-bench/         # topic worktree for benchmark work
```

Create worktrees from the same up-to-date base:

```sh
git fetch origin
git worktree add ../axeyum-codex-rules -b agent/codex/rules-docs origin/main
git worktree add ../axeyum-agent-solver -b agent/solver/warm-arrays origin/main
```

Use descriptive branch names:

```text
agent/codex/rules-docs
agent/solver/warm-arrays
agent/bench/qf-lia-scoreboard
agent/docs/proof-cookbook
```

## Roles

Use a simple hub-and-spoke workflow:

- **Integration owner:** owns `main`, resolves final conflicts, and decides merge
  order.
- **Topic agent:** works in its own worktree and branch, keeps changes small,
  pushes frequently, and does not edit unrelated files.
- **Reviewer / verifier:** can pull a topic branch into a separate worktree and
  run gates without disturbing either the topic agent or the integration lane.

If the team explicitly wants direct-to-`main` commits for a short stretch, make
that a named exception and coordinate file ownership before work starts.

## Daily Protocol

At the start of a task:

```sh
git fetch origin
git status --short --branch
git log --oneline --decorate -5
```

If you are on a topic branch:

```sh
git rebase origin/main
```

Before committing:

```sh
cargo fmt --all --check
git diff --check
# plus focused tests for the touched area
```

Before pushing a topic branch:

```sh
git status --short --branch
git push -u origin HEAD
```

Before merging to `main`:

```sh
git fetch origin
git rebase origin/main
# rerun focused gates after the rebase
git push --force-with-lease
```

The integration owner should merge or fast-forward in a clean integration
checkout, then run the relevant top-level gate before pushing `main`.

## File Ownership

Coordinate ownership before touching high-conflict files.

Good examples:

- "Agent A owns `crates/axeyum-solver/src/incremental.rs` for this slice."
- "Agent B owns `docs/rules-as-code/` and will not edit `STATUS.md` until merge."
- "The integration owner updates `PLAN.md`; topic branches update only their
  local docs and add a short STATUS entry after merge."

For `STATUS.md`, prefer lane-specific sections. Avoid two agents repeatedly
editing the same top-of-file paragraph. If a topic branch must update status,
keep the entry short and easy to rebase.

For `PLAN.md`, prefer stable links and short index updates. Detailed session
state belongs in `STATUS.md`; detailed design belongs under `docs/`.

## Push Policy

Do not push a shared branch if it is already ahead of `origin` with commits you
did not create unless the integration owner has said that is expected.

Check first:

```sh
git log --oneline origin/main..HEAD
git rev-list --left-right --count main...origin/main
```

If the current branch contains someone else's unpushed commits, either:

- ask the integration owner to push or merge them;
- move your work to a topic branch/worktree; or
- commit locally and clearly report that pushing would also publish the existing
  unpushed commits.

Use `--force-with-lease` only for topic branches that you own. Never force-push
`main`.

## Conflict Handling

When conflicts happen, preserve the newer intent instead of mechanically taking
one side.

Recommended sequence:

```sh
git fetch origin
git rebase origin/main
# resolve conflicts
cargo fmt --all --check
git diff --check
# rerun focused tests
git push --force-with-lease
```

For planning-doc conflicts, do not duplicate entries. Merge them into one
chronological note with the final current state.

For code conflicts, rerun the smallest focused test that proves the merged
behavior and then the broader gate appropriate to the touched crate.

## When To Split Repositories

Worktrees solve same-repo coordination. They do not decide project boundaries.

Keep work inside the Axeyum repo while it is tightly coupled to solver
semantics, proof routes, benchmarks, documentation, or CI. Split into a separate
repository only when the sibling has an independent release cycle, heavy
dependencies, a large corpus, or a standalone user audience.

Examples that should incubate inside Axeyum first:

- `docs/atlas/`
- `docs/proof-cookbook/`
- `docs/rules-as-code/`
- `artifacts/ontology/`

Examples that may deserve separate repositories later:

- an Axeyum visualizer web app;
- an EVM or WASM verification frontend;
- a large law/policy corpus;
- a public course site.

## Cleanup

List worktrees:

```sh
git worktree list
```

Remove a completed worktree after its branch is merged:

```sh
git worktree remove ../axeyum-codex-rules
git branch -d agent/codex/rules-docs
```

If a worktree was deleted manually:

```sh
git worktree prune
```


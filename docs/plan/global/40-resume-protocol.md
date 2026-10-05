## Resume protocol

1. Read this file first. Do not reconstruct priority from dated notes, archived
   lane files, branch names, or worktree age.
2. Verify live state (`git status --short --branch`, `git fetch origin`,
   `git rev-parse HEAD origin/main`, `git worktree list`). Re-derive any
   baseline you will score against; the boards quoted in Status are snapshots.
3. Pick the first unblocked item of the relevant track in **Next Actions**
   (P0 work preempts). Read its linked detail and the
   [foundational DAG](docs/research/08-planning/foundational-dag.md) before
   editing.
4. Open a lane file `docs/plan/status/<lane>.md` naming the item ID (e.g.
   `SOL-2`), with a `lane-status` block and landed rows
   ([format](docs/plan/status/README.md)). Work in an isolated worktree; one
   writer per branch.
5. Iterate on the narrowest relevant tests; run the aggregate gate once on the
   finished branch and confirm nonzero test counts. Commit with
   `scripts/lane-commit.sh`; merge and push per
   [multi-agent-operations](docs/contributor-guide/multi-agent-operations.md).
6. When the item meets its exit criterion (or is refuted), mark the lane `DONE`,
   **move the file to `docs/plan/archive/lanes/`**, update the item's line in
   the track here if its state changed, and run `python3 scripts/gen-plan.py`.
   Keep at most ~25 active lane files.

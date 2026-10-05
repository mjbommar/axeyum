# Lane: pre-push foreign-worktree isolation

<!-- plan-section: lane-status -->

**The persistent pre-push checkout no longer inherits the caller lane's Git
metadata (`DONE`, codex-autogenesis-prepush, 2026-08-20).** Git exports
`GIT_DIR` and related local variables to hooks; previously, `git -C` changed
the filesystem path but still detached and rewrote the caller's HEAD/index.
`prepare-prepush-worktree.sh` clears those variables at the foreign-worktree
boundary, checks out and cleans the exact target, then fails unless its
registered HEAD and status agree. The registered control preserves a caller
with staged and untracked work across fresh and reused gate checkouts and
rejects an unsafe root and nonexistent target.

The first post-repair Rust push checked exact topic SHA `24b16642e` in the
registered gate checkout, left it clean, and preserved the caller branch,
index, and status. The operational incident is closed; future changes remain
covered by the registered control and the live hook.

<!-- plan-section: landed-changes -->

| 2026-08-20 | `9eb81822f` | Isolate persistent pre-push worktree metadata from the caller lane and register the two-sided control |
| 2026-08-20 | `24b16642e` | Confirm the repaired hook against a live Rust push with unchanged caller state and a clean exact-SHA gate checkout |

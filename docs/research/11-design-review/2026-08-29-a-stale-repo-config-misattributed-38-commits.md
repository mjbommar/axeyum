# A stale repo-local config misattributed 38 commits over four days (2026-08-29)

**Measured in the shared checkout.** A lane reported that its first two commits
carried the wrong `Agent:` trailer. The blast radius is larger than it saw.

`hooks/commit-msg` resolved lane identity as

    agent="${AXEYUM_AGENT:-$(git config --get axeyum.agent 2>/dev/null || true)}"

An `fta-existence` lane set that repo-local config on **2026-08-25**. It was
never unset. Every commit since, in any worktree, whose shell had no
`AXEYUM_AGENT` exported fell through to it:

| date | commits stamped `fta-existence` |
| --- | --- |
| 08-25 | 15 (genuine — that lane's own work) |
| 08-26 | 7 |
| 08-28 | 1 |
| 08-29 | 15 |

The 08-29 fifteen come from **at least four distinct lanes** — `nat-lor-assoc`,
`nat-lor-ldiff-bit`, `nat-parity-lowbit`, `nat-assoc-dichotomy` — each
correctly exporting `AXEYUM_AGENT` in *some* shell invocations and not others.
`export` does not survive between separate Bash tool calls, so a lane that
exports once and commits in a later call silently inherits whatever the config
says.

## Why it reached other lanes at all

**Git worktrees share `.git/config`** unless `extensions.worktreeConfig` is
enabled, and it is not enabled here (verified). So a lane setting
`axeyum.agent` inside its own isolated worktree sets it for **every** lane in
the repository. The isolation that makes worktrees safe for *files* does not
extend to config.

CLAUDE.md already warned about this in the abstract — *"it is repo-local, so
the last writer silently renames every other lane's commits (this happened
within five minutes of the hook landing)"* — and the hook's own help text
repeats it. Prose did not prevent a four-day recurrence, because nothing in the
commit output shows which source the identity came from.

## Fix

1. Config unset.
2. The hook no longer takes the fallback silently. When `AXEYUM_AGENT` is
   absent and the repo-local config supplies the name, it prints a warning
   naming the value and saying the config is shared across worktrees. Verified
   both paths: env-var path writes **0 bytes** to stderr, fallback path writes
   the warning and still stamps (fail-loud, not fail-closed — refusing would
   break single-writer checkouts that legitimately use the fallback).

## What is NOT a defect, and I nearly filed it as one

While measuring this I found **33 of 33 merge commits carry no `Agent:`
trailer**, against 152 of 152 ordinary commits that do. That is not a hook bug:
`git merge`'s automatic commit does not run `commit-msg` at all. But CLAUDE.md's
claim that the hook "refuses an unidentified commit" is silently untrue for
merges, and a coordinator doing merge-heavy work produces unattributed history
by default. Worth knowing before reading `git log` attribution as complete.

## The general rule

**Per-lane identity belongs in per-process environment, never in shared
config** — the repository's own standing rule, which `.git/config` quietly
violates for worktrees. Any state a worktree does not isolate is shared state,
and shared state with a last-writer-wins policy will eventually be wrong.

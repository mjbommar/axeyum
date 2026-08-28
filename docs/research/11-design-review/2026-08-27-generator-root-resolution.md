# The generator did not write to the shared checkout because of `__file__`

Status: **misdiagnosed fix rejected 2026-08-27**; the real mechanism is the
documented absolute-path hazard.

## What was observed

`scripts/gen-kernel-facts.py`, run by a lane that had its own git worktree,
wrote its output into the **shared checkout** twice in one day — once with 429
fact files plus a modified `artifacts/ledger-coverage.json`, once with 52. Both
blocked the coordinator's merge; both recovered cleanly after verifying every
file was byte-identical to the lane's branch.

## The proposed diagnosis, and why it is wrong

A lane concluded:

> `Path(__file__).resolve()` **resolves symlinks and follows the physical file
> location**, which in git worktrees points to the actual file in the shared
> checkout.

**Git worktrees do not contain symlinks.** `git worktree add` creates a full
checkout of real files. Measured on this box, from a live lane worktree:

    $ ls -la /data0/axeyum/lanes/euler-e/scripts/gen-kernel-facts.py
    -rwxrwxr-x   (a regular file, not a symlink)

    $ cd /data0/axeyum/lanes/euler-e && python3 -c \
      "from pathlib import Path; print(Path('scripts/gen-kernel-facts.py').resolve().parent.parent)"
    /data0/axeyum/lanes/euler-e

`__file__`-relative resolution was **already correct**. It returns the worktree.

## What actually happened

Almost certainly the hazard CLAUDE.md already documents: **an absolute path
under the main checkout silently edits the main checkout, even from inside a
worktree.** A lane that runs

    python3 /home/mjbommar/projects/personal/axeyum/scripts/gen-kernel-facts.py

gets the shared checkout's `__file__`, and therefore the shared checkout's
`ROOT` — correctly, by the resolution rule. The bug is the invocation, not the
resolver.

## Why the proposed fix would have made it worse

The fix replaced `__file__`-relative resolution with `git rev-parse
--show-toplevel` in **five** generators, including `gen-plan.py`, which
regenerates `PLAN.md` and is gated in CI. `--show-toplevel` is **cwd-based**, so
it trades one failure mode for another. Measured both directions:

| invocation | `__file__` (old) | `git rev-parse` (new) |
| --- | --- | --- |
| shared script, cwd = worktree | shared ✗ | worktree ✓ |
| worktree script, cwd = shared | worktree ✓ | **shared ✗** |

Neither is uniformly right, and the new one is arguably worse: `__file__`
follows **the script you actually invoked**, which is explicit, while cwd is
ambient state that a `cd` three commands ago can change. A lane that correctly
invokes its own worktree's script would now write to the shared tree because it
happened to be sitting elsewhere.

## The right fix

**Invoke the worktree's own script by a relative path**, which is already the
standing rule for every file operation in this repository. If a generator should
additionally refuse to write outside the tree its own source lives in, that is a
guard worth adding — one that *fails* rather than one that silently retargets.

## Two process findings, independent of the diagnosis

- **The control was hyphenated: `scripts/tests/test-generator-root-resolution.py`.**
  The registration gate's glob is `test_*.py` and is blind to hyphens (confirmed
  by probe the same day), and a hyphenated module cannot be reached by
  `python3 -m unittest` at all. The two vacuous tests removed earlier that day
  were the only hyphenated files in that directory. It was also **registered in
  no gate**, which the brief explicitly required.
- **The mutation evidence was conditional.** "If I revert the fix back to
  `ROOT = Path(__file__)...`, the test immediately fails because…" is a
  prediction. That phrasing has now appeared three times in one day, and one of
  those three turned out **vacuous** when actually run.

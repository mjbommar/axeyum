# Lane: already-proved-sweep -- close the open facts already proved in the tree

<!-- plan-section: lane-status -->

**Lane block (`DONE -- 21 of 25 exact-constant candidates closed, 4 false
positives correctly left open, already-proved-sweep, 2026-08-29).**

## Headline

Re-ran `scripts/brief-step0.py`'s constant-multiset ranker over the merged
tree (the frontier had moved from the 141 open facts in the tool's own
landing report to **181** open facts with a `formal.statement`, after a
40-row draw landed) and got **25 exact-constant (score >= 0.999) candidates**,
not 14. Reading each one's rendered type character-by-character against the
fact's `formal.statement` -- the tool's own documented limit is that a
constant multiset cannot see argument order -- **21 survive and 4 are false
positives**. Commit: `92a61164eb317e34f7bf25c9a4c90c09c6b7694f`.

## 1. The re-run

```
python3 scripts/brief-step0.py --self-check
  -> SNAPSHOT EXACT, kernel_tree=e8d09cfefeea, declarations=2286
```

The snapshot's tree matched `HEAD:crates/axeyum-lean-kernel` exactly (clean
worktree, freshly merged `main`), so no `--refresh` was needed. Ranking all
181 open `formal.statement`-carrying facts against it (via the module's own
`rank`/`statement_bag` functions, imported directly -- no reimplementation):

| score band | count |
| --- | --- |
| >= 0.999 (exact constant multiset) | **25** |
| 0.75 - 0.999 | 7 |

`scripts/check-autogenesis-already-proved.py` no longer lives at that path --
the same merge that landed `brief-step0.py` also landed a census that archived
346 `check-*` scripts with no live caller
(`98d17aeef`), and this one moved to `scripts/archive/` with a relative-path
bug (`ROOT = parents[1]` now resolves to `scripts/`, one level too shallow,
and its internal call to `check-dispatchable-frontier.py` compounds it to
`scripts/scripts/...`). Ran it from a scratch copy with `ROOT` hardcoded to
this worktree; it independently confirmed **10 of 28** dispatchable rows
name-matched -- a subset of the 21 below. This script answers a narrower
question (name match only) and is now superseded by `brief-step0.py`'s
type-comparing ranker; it is not proposed for un-archiving.

## 2. The 4 false positives -- same constants, different proposition

Detail moved to [`../notes/310-already-proved-sweep.md`](../notes/310-already-proved-sweep.md).


# 307 — `brief-step0`: move retrieval into the dispatcher

**Lane:** `brief-step0` · **Status:** in progress

## Re-measurement of the retrospective's two numbers

Measured in this worktree after `git merge --no-edit main`.

| practice | docs | of 272 | pct |
| --- | --- | --- | --- |
| mutation testing (`mutation`/`mutant`, case-insensitive) | 125 | 272 | **46.0%** |
| `shape_search` / `shape-search` | 13 | 272 | **4.8%** |

Commands (GNU grep at `/usr/bin/grep`, not the interactive `ugrep` shell
function):

```
/usr/bin/grep -lEi 'mutation|mutant' docs/plan/status/*.md | wc -l        -> 125
/usr/bin/grep -lE  'shape_search|shape-search' docs/plan/status/*.md | wc -l -> 13
ls docs/plan/status/*.md | wc -l                                          -> 272
```

Positive control: `/usr/bin/grep -lE '[a-z]' docs/plan/status/*.md | wc -l` →
272 — the query mechanism reaches every document, so a zero would have meant
something.
Negative control: a fabricated token (`zzqqxx-nonexistent-token`) → 0.

The retrospective measured 269 documents; three have landed since. Both
percentages are unchanged to one decimal place. **Compliance tracks
mechanization, not emphasis** is confirmed.

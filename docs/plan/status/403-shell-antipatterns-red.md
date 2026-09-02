# Lane: shell-antipatterns-red — fix the five `grep -q`-in-pipeline sites flagged by check-shell-antipatterns.sh

<!-- plan-section: lane-status -->

**Your lane's block (`WIP`, shell-antipatterns-red, 2026-09-01).** In progress:
`scripts/check-shell-antipatterns.sh` was red on main (5 files, 11 sites, all
NEW against the baseline). Fixing each `echo … | grep -q… || { … }` site with
`[ "$(echo … | grep -c…)" -gt 0 ] || { … }`, then re-running the affected
mutation-control scripts in isolation (never the shared worktree) to confirm
each still kills exactly its own guard.

<!-- plan-section: landed-changes -->

| 2026-09-01 | shell-antipatterns-red | fix `grep -q` in pipeline under pipefail in 5 mutation-control scripts |

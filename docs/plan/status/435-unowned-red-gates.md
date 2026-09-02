# Lane: unowned-red-gates — diagnose the two red aggregate-gate steps and close the pre-push partition-gate hole

<!-- plan-section: lane-status -->

**Your lane's block (`WIP`, unowned-red-gates, 2026-09-02).** Started: diagnosing
`autogenesis-nursery-dispatch-baseline` (`--check`) and `propose-nursery-refill`,
both red on main and named "pre-existing, not mine" by lanes today. Also
auditing `hooks/pre-push` for the four partition gates ADR-1546 says it is
missing (`check-development-partition`, `check-holdout-isolation`,
`check-holdout-adjacency`, `check-draw7-frozen-families`), and running a census
of every 2026-09-01+ status doc's "pre-existing"/"not mine" gate mentions.

<!-- plan-section: landed-changes -->

| 2026-09-02 | unowned-red-gates | status stub opened; diagnosis in progress |

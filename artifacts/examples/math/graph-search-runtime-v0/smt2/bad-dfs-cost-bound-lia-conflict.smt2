; QF_LIA runtime-bound obstruction for graph-search-runtime-v0.
;
; On the length-four shortcut-tail graph, deterministic DFS visits six vertices
; before reaching t. The rejected resource claim says DFS reaches t in at most
; three visits, encoded here as dfs_visits <= claimed_upper_bound.
(set-logic QF_LIA)
(declare-fun dfs_visits () Int)
(declare-fun claimed_upper_bound () Int)
(assert (= dfs_visits 6))
(assert (= claimed_upper_bound 3))
(assert (<= dfs_visits claimed_upper_bound))
(check-sat)

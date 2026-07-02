; QF_LRA/Farkas obstruction for finite-shortest-path-v0.
; Exact potential replay computes potential_lower_bound = 5, but the malformed
; row claims an s-t path length upper bound of 4.
(set-logic QF_LRA)
(declare-const potential_lower_bound Real)
(declare-const claimed_upper_bound Real)
(assert (= potential_lower_bound 5))
(assert (= claimed_upper_bound 4))
(assert (<= potential_lower_bound claimed_upper_bound))
(check-sat)

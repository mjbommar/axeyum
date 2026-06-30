; QF_LRA/Farkas obstruction for finite-wolfe-line-search-v0.
; Exact replay computes curvature_violation = 2 for the malformed Wolfe row.
(set-logic QF_LRA)
(declare-const curvature_violation Real)
(assert (= curvature_violation 2))
(assert (<= curvature_violation 0))
(check-sat)

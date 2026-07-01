; QF_LRA/Farkas obstruction for convexity-rational-v0.
; Exact affine-threshold replay computes threshold_shortfall = 3/2 for the malformed threshold row.
(set-logic QF_LRA)
(declare-const threshold_shortfall Real)
(assert (= threshold_shortfall (/ 3 2)))
(assert (<= threshold_shortfall 0))
(check-sat)

; QF_LRA/Farkas obstruction for finite-line-search-v0.
; Exact replay computes armijo_violation = 1 for the malformed accepted trial row.
(set-logic QF_LRA)
(declare-const armijo_violation Real)
(assert (= armijo_violation 1))
(assert (<= armijo_violation 0))
(check-sat)

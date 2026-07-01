; QF_LRA/Farkas obstruction for finite-proximal-gradient-v0.
; Exact box-plus-L1 replay computes box_violation = 1/4 for the malformed prox row.
(set-logic QF_LRA)
(declare-const box_violation Real)
(assert (= box_violation (/ 1 4)))
(assert (<= box_violation 0))
(check-sat)

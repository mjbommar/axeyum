; QF_LRA/Farkas obstruction for finite-proximal-gradient-v0.
; Exact replay computes proximal_optimality_error = 3/2 for the malformed prox row.
(set-logic QF_LRA)
(declare-const proximal_optimality_error Real)
(assert (= proximal_optimality_error (/ 3 2)))
(assert (= proximal_optimality_error 0))
(check-sat)

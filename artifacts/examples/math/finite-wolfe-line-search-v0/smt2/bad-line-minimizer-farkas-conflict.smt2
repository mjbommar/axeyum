; QF_LRA/Farkas obstruction for finite-wolfe-line-search-v0.
; Exact replay computes minimizer_alpha = 1/2 for the malformed minimizer row.
(set-logic QF_LRA)
(declare-const minimizer_alpha Real)
(assert (= minimizer_alpha (/ 1 2)))
(assert (= minimizer_alpha 1))
(check-sat)

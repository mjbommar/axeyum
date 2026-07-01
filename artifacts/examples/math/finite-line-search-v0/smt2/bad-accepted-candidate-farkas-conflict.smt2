; QF_LRA/Farkas obstruction for finite-line-search-v0.
; Exact replay computes accepted_x = 0 for the malformed accepted-candidate row.
(set-logic QF_LRA)
(declare-const accepted_x Real)
(assert (= accepted_x 0))
(assert (= accepted_x (/ 1 4)))
(check-sat)

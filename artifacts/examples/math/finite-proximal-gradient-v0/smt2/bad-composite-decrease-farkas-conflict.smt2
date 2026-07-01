; QF_LRA/Farkas obstruction for finite-proximal-gradient-v0.
; Exact replay computes composite_decrease = 3/2 for the malformed decrease row.
(set-logic QF_LRA)
(declare-const composite_decrease Real)
(assert (= composite_decrease (/ 3.0 2.0)))
(assert (= composite_decrease 2.0))
(check-sat)

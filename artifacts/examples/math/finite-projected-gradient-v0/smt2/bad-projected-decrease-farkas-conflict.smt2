; QF_LRA/Farkas obstruction for finite-projected-gradient-v0.
;
; Exact replay computes projected_decrease = f(0) - f(1) = 4 - 1 = 3.
; The malformed row claims the same decrease is 4.
(set-logic QF_LRA)
(declare-const projected_decrease Real)
(assert (= projected_decrease 3))
(assert (= projected_decrease 4))
(check-sat)

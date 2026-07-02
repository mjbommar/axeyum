; QF_LRA/Farkas obstruction for finite-polar-decomposition-v0.
; Exact replay computes the positive polar factor diagonal P[1,1] as 5, while
; the malformed resource row claims it is 4.
(set-logic QF_LRA)
(declare-fun polar_p11 () Real)
(assert (= polar_p11 5))
(assert (= polar_p11 4))
(check-sat)

; QF_LRA/Farkas obstruction for finite-lu-decomposition-v0.
;
; Finite replay computes the elimination multiplier l21 as A[1,0] / A[0,0] = 4/2 = 2.
; This artifact checks the malformed claim that the same multiplier is 3.
(set-logic QF_LRA)
(declare-const lu_l21 Real)
(assert (= lu_l21 2))
(assert (= lu_l21 3))
(check-sat)

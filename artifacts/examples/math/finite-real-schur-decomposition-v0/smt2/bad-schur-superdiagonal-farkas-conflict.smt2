; QF_LRA/Farkas obstruction for finite-real-schur-decomposition-v0.
; Exact replay computes the Schur superdiagonal T[0,1] as 2, while the
; malformed resource row claims it is 3.
(set-logic QF_LRA)
(declare-fun schur_t01 () Real)
(assert (= schur_t01 2))
(assert (= schur_t01 3))
(check-sat)

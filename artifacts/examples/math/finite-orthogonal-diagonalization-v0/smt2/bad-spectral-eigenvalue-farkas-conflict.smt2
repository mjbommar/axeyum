; QF_LRA/Farkas obstruction for finite-orthogonal-diagonalization-v0.
; Exact replay computes the second listed eigenvalue as 4, while the malformed
; resource row claims it is 5.
(set-logic QF_LRA)
(declare-fun spectral_lambda_1 () Real)
(assert (= spectral_lambda_1 4))
(assert (= spectral_lambda_1 5))
(check-sat)

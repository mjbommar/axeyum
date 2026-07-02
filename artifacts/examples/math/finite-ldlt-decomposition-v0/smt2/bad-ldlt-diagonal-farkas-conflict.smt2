; QF_LRA/Farkas obstruction for finite-ldlt-decomposition-v0.
;
; Exact replay computes the second diagonal entry of D as 2.
; This artifact checks the malformed claim that the same diagonal entry is 3.
(set-logic QF_LRA)
(declare-const ldlt_d11 Real)
(assert (= ldlt_d11 2))
(assert (= ldlt_d11 3))
(check-sat)

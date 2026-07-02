; QF_LRA/Farkas obstruction for finite-gaussian-elimination-v0.
;
; Exact replay computes the eliminated second RHS entry as 7.
; This artifact checks the malformed claim that the same scalar is 8.
(set-logic QF_LRA)
(declare-const eliminated_rhs_1 Real)
(assert (= eliminated_rhs_1 7))
(assert (= eliminated_rhs_1 8))
(check-sat)

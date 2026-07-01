; QF_LRA/Farkas obstruction for matrix-invariants-v0.
;
; Exact replay computes trace([[2,1],[1,2]]) = 4.
; This artifact checks the malformed claim that the same trace is 5.
(set-logic QF_LRA)
(declare-const matrix_trace Real)
(assert (= matrix_trace 4))
(assert (= matrix_trace 5))
(check-sat)

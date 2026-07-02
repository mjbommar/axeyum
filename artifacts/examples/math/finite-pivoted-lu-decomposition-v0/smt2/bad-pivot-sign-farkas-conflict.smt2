; QF_LRA/Farkas obstruction for finite-pivoted-lu-decomposition-v0.
;
; Finite replay computes the row-swap permutation determinant as -1.
; This artifact checks the malformed claim that the same determinant is +1.
(set-logic QF_LRA)
(declare-const pivot_det Real)
(assert (= (+ pivot_det 1) 0))
(assert (= pivot_det 1))
(check-sat)

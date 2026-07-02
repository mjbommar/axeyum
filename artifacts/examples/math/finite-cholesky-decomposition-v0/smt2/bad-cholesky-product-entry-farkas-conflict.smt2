; QF_LRA/Farkas obstruction for finite-cholesky-decomposition-v0.
;
; Exact replay computes the bottom-right entry of L*L^T as 10.
; This artifact checks the malformed claim that the same entry is 9.
(set-logic QF_LRA)
(declare-const cholesky_product_11 Real)
(assert (= cholesky_product_11 10))
(assert (= cholesky_product_11 9))
(check-sat)

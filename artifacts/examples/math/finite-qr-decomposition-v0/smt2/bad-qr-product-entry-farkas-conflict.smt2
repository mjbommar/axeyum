; QF_LRA/Farkas obstruction for finite-qr-decomposition-v0.
;
; Exact replay computes the bottom-right entry of Q*R as 2/5.
; This artifact checks the malformed claim that the same entry is 1/2.
(set-logic QF_LRA)
(declare-const qr_product_11 Real)
(assert (= qr_product_11 (/ 2 5)))
(assert (= qr_product_11 (/ 1 2)))
(check-sat)

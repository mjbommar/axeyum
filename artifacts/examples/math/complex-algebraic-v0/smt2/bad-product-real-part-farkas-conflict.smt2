; QF_LRA/Farkas obstruction for complex-algebraic-v0.
;
; Exact real-pair replay computes (1 + 2i) * (3 - i) = 5 + 5i.
; This artifact checks the malformed claim that the real part is 4.
(set-logic QF_LRA)
(declare-const product_real Real)
(assert (= product_real 5))
(assert (= product_real 4))
(check-sat)

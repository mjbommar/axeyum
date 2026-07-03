; QF_LRA/Farkas obstruction for finite-interval-arithmetic-shadow-v0.
;
; Exact interval replay computes product_upper = 100020001/100000000.
; This artifact checks the malformed shortcut product_upper <= 5001/5000.
(set-logic QF_LRA)
(declare-const product_upper Real)
(assert (= product_upper (/ 100020001 100000000)))
(assert (<= product_upper (/ 5001 5000)))
(check-sat)

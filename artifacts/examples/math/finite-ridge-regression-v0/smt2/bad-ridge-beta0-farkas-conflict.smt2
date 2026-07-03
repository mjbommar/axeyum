; QF_LRA/Farkas obstruction for finite-ridge-regression-v0.
;
; Exact replay computes the lambda = 1 regularized normal equations:
;   4*beta0 + 3*beta1 = 7
;   3*beta0 + 6*beta1 = 10
; The malformed row claims beta0 = 1.
(set-logic QF_LRA)
(declare-const beta0 Real)
(declare-const beta1 Real)
(assert (= (+ (* 4 beta0) (* 3 beta1)) 7))
(assert (= (+ (* 3 beta0) (* 6 beta1)) 10))
(assert (= beta0 1))
(check-sat)

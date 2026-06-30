; QF_LRA/Farkas obstruction for calculus-riemann-sum-v0.
;
; Exact polynomial integration computes integral_0^1 x dx = 1/2. The malformed
; row claims the same integral is 3/4.
(set-logic QF_LRA)
(declare-const integral_value Real)
(assert (= integral_value (/ 1 2)))
(assert (= integral_value (/ 3 4)))
(check-sat)

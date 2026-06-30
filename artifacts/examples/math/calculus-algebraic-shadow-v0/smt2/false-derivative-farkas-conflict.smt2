; QF_LRA/Farkas obstruction for calculus-algebraic-shadow-v0.
;
; Exact polynomial replay computes the derivative of f(x)=x^2 at x=3 as 6.
; The malformed row claims the same derivative value is 5.
(set-logic QF_LRA)
(declare-const derivative_value Real)
(assert (= derivative_value 6))
(assert (= derivative_value 5))
(check-sat)

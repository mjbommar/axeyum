; QF_LRA/Farkas obstruction for multivariable-calculus-rational-v0.
;
; Exact polynomial replay computes the y-component of the gradient of
; f(x,y)=x^2+2xy+3y^2+x at (1,2) as 14. The malformed row claims the same
; component is 13.
(set-logic QF_LRA)
(declare-const gradient_y Real)
(assert (= gradient_y 14))
(assert (= gradient_y 13))
(check-sat)

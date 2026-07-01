; QF_LRA alternation-residual obstruction for finite-chebyshev-systems-v0.
;
; The finite replay row computes common residual magnitude 1/2 for
; r(x)=x^2-1/2 at x=-1,0,1. This artifact checks the malformed claim that the
; same alternating residual table has uniform error 2/3 after replay has
; reduced the row to exact rational linear arithmetic.
(set-logic QF_LRA)
(declare-const uniform_error Real)
(assert (= uniform_error (/ 1 2)))
(assert (= uniform_error (/ 2 3)))
(check-sat)

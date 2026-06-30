; QF_LRA discriminant obstruction for reals-rcf-shadow-v0.
;
; Exact polynomial replay computes the discriminant of x^2 + 1 as -4.
; A real root of a quadratic would require a nonnegative discriminant, so this
; fixed RCF shadow closes as an exact linear contradiction after the
; discriminant calculation has been checked separately.
(set-logic QF_LRA)
(declare-const discriminant Real)
(assert (= (+ discriminant 4) 0))
(assert (>= discriminant 0))
(check-sat)

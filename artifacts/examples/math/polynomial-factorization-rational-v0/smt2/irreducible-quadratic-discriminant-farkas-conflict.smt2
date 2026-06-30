; QF_LRA discriminant obstruction for polynomial-factorization-rational-v0.
;
; Exact polynomial replay computes the discriminant of x^2 + 1 as -4.
; A rational linear factorization of a monic quadratic would require a
; nonnegative discriminant, so this fixed row closes as an exact linear
; contradiction.
(set-logic QF_LRA)
(declare-const discriminant Real)
(assert (= (+ discriminant 4) 0))
(assert (>= discriminant 0))
(check-sat)

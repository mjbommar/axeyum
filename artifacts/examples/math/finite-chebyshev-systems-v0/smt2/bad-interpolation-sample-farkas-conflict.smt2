; QF_LRA interpolation-sample obstruction for finite-chebyshev-systems-v0.
;
; The finite replay row computes p(1)=4 for p(x)=2 - x + 3*x^2.
; This artifact checks the malformed claim p(1)=5 after the replay has
; reduced the row to exact rational linear arithmetic.
(set-logic QF_LRA)
(declare-const sample_at_one Real)
(assert (= sample_at_one 4))
(assert (= sample_at_one 5))
(check-sat)

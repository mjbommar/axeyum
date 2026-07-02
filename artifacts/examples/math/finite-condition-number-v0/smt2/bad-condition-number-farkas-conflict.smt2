; QF_LRA/Farkas obstruction for finite-condition-number-v0.
;
; Exact replay computes kappa_infinity(A) = 6.
; This artifact checks the malformed claim kappa_infinity(A) <= 5.
(set-logic QF_LRA)
(declare-const kappa_infinity Real)
(assert (= kappa_infinity 6))
(assert (<= kappa_infinity 5))
(check-sat)

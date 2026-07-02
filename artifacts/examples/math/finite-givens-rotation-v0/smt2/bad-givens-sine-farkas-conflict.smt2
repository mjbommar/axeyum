; QF_LRA/Farkas obstruction for finite-givens-rotation-v0.
;
; Exact replay computes the Givens sine coefficient as 4/5.
; This artifact checks the malformed claim that the same coefficient is 3/5.
(set-logic QF_LRA)
(declare-const givens_sine Real)
(assert (= givens_sine (/ 4 5)))
(assert (= givens_sine (/ 3 5)))
(check-sat)

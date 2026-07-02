; QF_LRA/Farkas obstruction for finite-gram-schmidt-v0.
;
; Exact replay computes the Gram-Schmidt projection coefficient r12 as 3/5.
; This artifact checks the malformed claim that the same coefficient is 4/5.
(set-logic QF_LRA)
(declare-const gram_schmidt_r12 Real)
(assert (= gram_schmidt_r12 (/ 3 5)))
(assert (= gram_schmidt_r12 (/ 4 5)))
(check-sat)

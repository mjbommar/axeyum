; QF_LRA/Farkas obstruction for finite-jordan-chain-v0.
;
; Exact replay computes the first component of (A - 2I)*v2 as 1.
; This artifact checks the malformed claim that the same component is 0.
(set-logic QF_LRA)
(declare-const nilpotent_image_0 Real)
(assert (= nilpotent_image_0 1))
(assert (= nilpotent_image_0 0))
(check-sat)

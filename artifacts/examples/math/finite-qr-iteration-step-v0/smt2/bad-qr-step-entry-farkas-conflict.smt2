; QF_LRA/Farkas obstruction for finite-qr-iteration-step-v0.
; Exact replay computes A1[0,0] = 7/5, but the malformed row claims 2.
(set-logic QF_LRA)
(declare-const qr_step_a00 Real)
(assert (= qr_step_a00 (/ 7 5)))
(assert (= qr_step_a00 2))
(check-sat)

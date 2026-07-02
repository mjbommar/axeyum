; QF_LRA/Farkas obstruction for finite-shifted-qr-step-v0.
; Exact replay computes A1[1,1] = 8/5, but the malformed row claims 2.
(set-logic QF_LRA)
(declare-const shifted_qr_a11 Real)
(assert (= shifted_qr_a11 (/ 8 5)))
(assert (= shifted_qr_a11 2))
(check-sat)

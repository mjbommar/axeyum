; QF_LRA/Farkas obstruction for finite-sdp-v0.
; Exact SDP replay computes gap_error = 1/2 for the malformed duality-gap row.
(set-logic QF_LRA)
(declare-const gap_error Real)
(assert (= gap_error (/ 1 2)))
(assert (= gap_error 0))
(check-sat)

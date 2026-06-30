; QF_LRA/Farkas obstruction for finite-sdp-v0.
; Exact SDP replay computes objective_error = 1 for the malformed objective row.
(set-logic QF_LRA)
(declare-const objective_error Real)
(assert (= objective_error 1))
(assert (= objective_error 0))
(check-sat)

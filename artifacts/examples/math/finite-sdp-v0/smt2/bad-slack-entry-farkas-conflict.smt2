; QF_LRA/Farkas obstruction for finite-sdp-v0.
; Exact SDP replay computes slack_11 = 1 for the dual slack matrix.
(set-logic QF_LRA)
(declare-const slack_11 Real)
(assert (= slack_11 1))
(assert (= slack_11 (/ 1 2)))
(check-sat)

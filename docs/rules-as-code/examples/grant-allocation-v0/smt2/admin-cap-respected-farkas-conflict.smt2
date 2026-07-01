; QF_LRA administrative-cap check for grant-allocation-v0.
(set-logic QF_LRA)
(declare-const admin_share Real)
(assert (<= admin_share (/ 1 4)))
(assert (= admin_share (/ 1 2)))
(check-sat)

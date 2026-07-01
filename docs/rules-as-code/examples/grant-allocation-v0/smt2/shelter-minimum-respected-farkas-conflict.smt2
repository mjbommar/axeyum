; QF_LRA shelter-minimum check for grant-allocation-v0.
(set-logic QF_LRA)
(declare-const shelter_share Real)
(assert (>= shelter_share (/ 1 2)))
(assert (= shelter_share (/ 1 4)))
(check-sat)

; QF_LRA clinic-minimum check for grant-allocation-v0.
(set-logic QF_LRA)
(declare-const clinic_share Real)
(assert (>= clinic_share (/ 1 4)))
(assert (= clinic_share 0))
(check-sat)

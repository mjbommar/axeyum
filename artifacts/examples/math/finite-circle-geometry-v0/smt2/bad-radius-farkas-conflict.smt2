; QF_LRA/Farkas obstruction for finite-circle-geometry-v0.
; Exact replay computes squared radius = 2 for the malformed unit-circle point.
(set-logic QF_LRA)
(declare-const radius_squared Real)
(assert (= radius_squared 2))
(assert (= radius_squared 1))
(check-sat)

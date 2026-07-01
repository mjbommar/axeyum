; QF_LRA/Farkas obstruction for incidence-geometry-v0.
;
; Exact line-intersection replay computes (2, 1).
; This artifact checks the malformed claim that the x-coordinate is 3.
(set-logic QF_LRA)
(declare-const intersection_x Real)
(assert (= intersection_x 2))
(assert (= intersection_x 3))
(check-sat)

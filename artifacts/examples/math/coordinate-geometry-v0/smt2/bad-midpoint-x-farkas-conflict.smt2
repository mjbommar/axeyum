; QF_LRA/Farkas obstruction for coordinate-geometry-v0.
;
; Exact midpoint replay computes midpoint((0,0),(4,2)) = (2,1).
; This artifact checks the malformed claim that the midpoint x-coordinate is 3.
(set-logic QF_LRA)
(declare-const midpoint_x Real)
(assert (= midpoint_x 2))
(assert (= midpoint_x 3))
(check-sat)

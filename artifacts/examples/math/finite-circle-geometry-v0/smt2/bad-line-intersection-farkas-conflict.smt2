; QF_LRA circle-line obstruction for finite-circle-geometry-v0.
;
; Finite replay computes the right intersection of the unit circle with y = 0
; as (1,0). This artifact checks the malformed claim that the same replayed
; right intersection has x-coordinate 2 after replay has reduced the row to
; exact rational linear arithmetic.
(set-logic QF_LRA)
(declare-const right_intersection_x Real)
(assert (= right_intersection_x 1))
(assert (= right_intersection_x 2))
(check-sat)

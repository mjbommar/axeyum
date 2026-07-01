; QF_LRA opposite-angle obstruction for finite-cyclic-geometry-v0.
;
; The finite replay row computes the angle dot product at B in the square
; A=(1,0), B=(0,1), C=(-1,0), D=(0,-1):
; (A-B) . (C-B) = 0. This artifact checks the malformed claim that the same
; replayed angle has dot product 1 after replay has reduced the row to exact
; rational linear arithmetic.
(set-logic QF_LRA)
(declare-const angle_b_dot Real)
(assert (= angle_b_dot 0))
(assert (= angle_b_dot 1))
(check-sat)

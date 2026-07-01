; QF_LRA/Farkas obstruction for metric-continuity-v0.
;
; Exact finite replay computes f(p2) = 1 and target value 0, so p2 is not
; in the open output ball of radius 1 around 0. This artifact checks the
; malformed preimage claim that p2 is in that open ball.
(set-logic QF_LRA)
(declare-const output_distance Real)
(assert (= output_distance 1))
(assert (< output_distance 1))
(check-sat)

; QF_LRA/Farkas obstruction for bounded-monotone-sequence-v0.
; Exact finite-tail replay computes tail_excess = 1/12 for the malformed epsilon-tail row.
(set-logic QF_LRA)
(declare-const tail_excess Real)
(assert (= tail_excess (/ 1 12)))
(assert (<= tail_excess 0))
(check-sat)

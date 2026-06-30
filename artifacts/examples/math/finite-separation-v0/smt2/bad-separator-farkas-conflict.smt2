; QF_LRA/Farkas obstruction for finite-separation-v0.
;
; Exact separator replay computes outside_score = 4 for the point (2,2)
; under normal (1,1). The malformed row also requires outside_score <= 1.
(set-logic QF_LRA)
(declare-const outside_score Real)
(assert (= outside_score 4))
(assert (<= outside_score 1))
(check-sat)

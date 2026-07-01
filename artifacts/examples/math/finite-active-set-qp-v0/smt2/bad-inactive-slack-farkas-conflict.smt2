; QF_LRA/Farkas obstruction for finite-active-set-qp-v0.
; Exact replay computes inactive lower-bound slack = 1 at the active-face candidate.
(set-logic QF_LRA)
(declare-const inactive_slack Real)
(assert (= inactive_slack 1))
(assert (<= inactive_slack 0))
(check-sat)

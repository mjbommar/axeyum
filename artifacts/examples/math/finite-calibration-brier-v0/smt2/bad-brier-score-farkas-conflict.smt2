; Source artifact for finite-calibration-brier-v0.
; Exact replay gives Brier score = 71/300, represented without division as
; 300*brier = 71. The malformed row claims Brier score = 1/5, represented as
; 5*brier = 1.

(set-logic QF_LRA)

(declare-const brier Real)

(assert (= (* 300 brier) 71))
(assert (= (* 5 brier) 1))

(check-sat)

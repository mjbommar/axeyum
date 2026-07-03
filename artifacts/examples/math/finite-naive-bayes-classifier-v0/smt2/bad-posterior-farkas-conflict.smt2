; Source artifact for finite-naive-bayes-classifier-v0.
; Exact replay gives P(positive | features) = 9/13, represented without
; division as 13*p_positive = 9. The malformed row claims p_positive = 2/3,
; represented as 3*p_positive = 2.

(set-logic QF_LRA)

(declare-const p_positive Real)

(assert (= (* 13 p_positive) 9))
(assert (= (* 3 p_positive) 2))

(check-sat)

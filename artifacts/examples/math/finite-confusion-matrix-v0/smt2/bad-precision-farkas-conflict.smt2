; Source artifact for finite-confusion-matrix-v0.
; Exact replay gives precision = 2/3 from TP=2 and predicted positives=3,
; represented without division as 3*precision = 2. The malformed row claims
; precision = 3/4, represented as 4*precision = 3.

(set-logic QF_LRA)

(declare-const precision Real)

(assert (= (* 3 precision) 2))
(assert (= (* 4 precision) 3))

(check-sat)

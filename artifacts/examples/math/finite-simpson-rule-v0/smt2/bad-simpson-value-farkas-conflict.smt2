(set-logic QF_LRA)
(declare-const simpson_value Real)

; Exact replay computes the single-panel Simpson value as 4.
(assert (= simpson_value 4))

; The malformed source row claims the same value is 7/2.
(assert (= simpson_value (/ 7 2)))

(check-sat)

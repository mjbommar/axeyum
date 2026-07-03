; QF_LRA/Farkas obstruction for finite-rounding-shadow-v0.
;
; Exact replay computes exact_delta = 1/10000.
; Fixed three-decimal rounding replay computes rounded_delta = 0.
; This artifact checks the malformed claim that the two deltas are equal.
(set-logic QF_LRA)
(declare-const exact_delta Real)
(declare-const rounded_delta Real)
(assert (= exact_delta (/ 1 10000)))
(assert (= rounded_delta 0))
(assert (= exact_delta rounded_delta))
(check-sat)

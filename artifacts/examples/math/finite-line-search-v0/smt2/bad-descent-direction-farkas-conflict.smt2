; QF_LRA/Farkas obstruction for finite-line-search-v0.
; Exact replay computes directional_derivative = -4 for the malformed direction row.
(set-logic QF_LRA)
(declare-const directional_derivative Real)
(assert (= directional_derivative (- 4.0)))
(assert (>= directional_derivative 0.0))
(check-sat)

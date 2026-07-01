; QF_LRA/Farkas obstruction for finite-root-finding-v0.
; Exact bisection replay computes width_excess = 1/6 for the malformed width row.
(set-logic QF_LRA)
(declare-const width_excess Real)
(assert (= width_excess (/ 1 6)))
(assert (<= width_excess 0))
(check-sat)

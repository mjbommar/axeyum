; QF_LRA/Farkas obstruction for finite-recurrence-prefix-v0.
; Exact affine recurrence replay computes transition_residual = 1 for the malformed step row.
(set-logic QF_LRA)
(declare-const transition_residual Real)
(assert (= transition_residual 1))
(assert (<= transition_residual 0))
(check-sat)

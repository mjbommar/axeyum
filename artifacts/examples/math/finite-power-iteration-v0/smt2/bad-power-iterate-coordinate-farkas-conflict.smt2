; QF_LRA/Farkas obstruction for finite-power-iteration-v0.
;
; Exact replay computes A^2 * [1,1] = [4,1] for A = diag(2,1).
; This artifact checks the malformed claim that the first coordinate is 3.
(set-logic QF_LRA)
(declare-const power_iterate2_x0 Real)
(assert (= power_iterate2_x0 4))
(assert (= power_iterate2_x0 3))
(check-sat)

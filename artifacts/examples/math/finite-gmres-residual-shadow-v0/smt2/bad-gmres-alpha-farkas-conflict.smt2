(set-logic QF_LRA)
(declare-const gmres_alpha Real)

; Exact one-step GMRES replay computes alpha = 2/5.
(assert (= gmres_alpha (/ 2 5)))

; Malformed resource row claims alpha = 1/2.
(assert (= gmres_alpha (/ 1 2)))

(check-sat)

; Source artifact for finite-principal-components-v0.
; Exact replay gives covariance C = [[2, 0], [0, 1/2]],
; principal vector v = (1, 0), and principal eigenvalue lambda = 2.
; The malformed row claims lambda = 3/2.

(set-logic QF_LRA)

(declare-const vx Real)
(declare-const vy Real)
(declare-const lambda Real)

(assert (= vx 1))
(assert (= vy 0))
(assert (= (* 2 vx) lambda))
(assert (= (* (/ 1 2) vy) 0))
(assert (= lambda (/ 3 2)))

(check-sat)

(set-logic QF_LRA)

(declare-const wx Real)
(declare-const wy Real)

; The finite replay computes S_w = [[2, 0], [0, 2]] and
; mu_B - mu_A = [0, 3], so S_w*w = mu_B - mu_A forces wy = 3/2.
(assert (= (* 2 wx) 0))
(assert (= (* 2 wy) 3))

; Malformed source claim.
(assert (= wy 1))

(check-sat)

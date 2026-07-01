; QF_LRA/Farkas obstruction for finite-operator-v0.
;
; Finite replay computes ||u + v||_1 = 5 for u=(1,2) and v=(3,-1).
; This artifact checks the malformed claim that the same replayed norm is at
; most 4 after replay has reduced the row to exact rational linear arithmetic.
(set-logic QF_LRA)
(declare-const sum_norm Real)
(assert (= sum_norm 5))
(assert (<= sum_norm 4))
(check-sat)

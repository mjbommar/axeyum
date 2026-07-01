; QF_LRA/Farkas obstruction for sequence-limit-shadow-v0.
;
; Exact finite replay computes |1/3 - 0| = 1/3 at index 2 of the reciprocal
; sequence. This artifact checks the malformed claim that the same tail
; distance is strictly below 1/4.
(set-logic QF_LRA)
(declare-const tail_distance Real)
(assert (= tail_distance (/ 1 3)))
(assert (< tail_distance (/ 1 4)))
(check-sat)

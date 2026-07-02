; QF_LRA/Farkas obstruction for finite-newton-step-v0.
;
; Exact replay computes the Newton next x-coordinate as 10/7.
; This artifact checks the malformed claim that the same coordinate is 3/2.
(set-logic QF_LRA)
(declare-const newton_next_x Real)
(assert (= newton_next_x (/ 10 7)))
(assert (= newton_next_x (/ 3 2)))
(check-sat)

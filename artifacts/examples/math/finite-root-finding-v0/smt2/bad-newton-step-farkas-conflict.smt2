; QF_LRA/Farkas obstruction for finite-root-finding-v0.
;
; Exact Newton-step replay for f(x)=x^2-2 from x=3/2 computes next = 17/12.
; The malformed row claims the same next iterate is 4/3.
(set-logic QF_LRA)
(declare-const newton_next Real)
(assert (= newton_next (/ 17 12)))
(assert (= newton_next (/ 4 3)))
(check-sat)

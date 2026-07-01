; QF_LRA/Farkas obstruction for numerical-linear-algebra-v0.
;
; Exact solution-box replay computes x0 = 6/5 for the fixed 2x2 system, while
; the malformed interval claim requires x0 <= 1.
(set-logic QF_LRA)
(declare-const solution_x0 Real)
(assert (= (* 5 solution_x0) 6))
(assert (<= solution_x0 1))
(check-sat)

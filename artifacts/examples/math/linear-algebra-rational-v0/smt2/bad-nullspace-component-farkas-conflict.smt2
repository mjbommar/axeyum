; QF_LRA/Farkas obstruction for linear-algebra-rational-v0.
;
; Exact replay checks A*v = 0 for
; A = [[1,2],[2,4]] and v = [2,-1], so the first component is 2.
; This artifact checks the malformed claim that the same component is 1.
(set-logic QF_LRA)
(declare-const null_v0 Real)
(assert (= null_v0 2))
(assert (= null_v0 1))
(check-sat)

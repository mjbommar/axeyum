; QF_LRA/Farkas obstruction for linear-algebra-rational-v0.
;
; Finite replay multiplies
; L = [[1,0],[2,1]] and U = [[2,1],[0,1]]
; to recover A = [[2,1],[4,3]], so the bottom-right product entry is 3.
; This artifact checks the malformed claim that the same entry is 4.
(set-logic QF_LRA)
(declare-const lu_entry_11 Real)
(assert (= lu_entry_11 3))
(assert (= lu_entry_11 4))
(check-sat)

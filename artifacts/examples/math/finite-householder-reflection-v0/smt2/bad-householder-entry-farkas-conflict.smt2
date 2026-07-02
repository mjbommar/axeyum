; QF_LRA/Farkas obstruction for finite-householder-reflection-v0.
;
; Exact replay computes the top-left Householder entry as -3/5.
; This artifact checks the malformed claim that the same entry is -4/5.
(set-logic QF_LRA)
(declare-const householder_entry_00 Real)
(assert (= householder_entry_00 (- (/ 3 5))))
(assert (= householder_entry_00 (- (/ 4 5))))
(check-sat)

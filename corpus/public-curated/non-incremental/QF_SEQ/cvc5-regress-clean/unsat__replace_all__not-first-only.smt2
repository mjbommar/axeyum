; (seq.replace_all [1,1,1] [1] [2]) = [2,2,2] (all replaced), and
; (seq.replace_all [2,1,1] [1] [3]) = [2,3,3]. The two ground results are distinct
; literals, so asserting them equal is unsatisfiable — a check that replace_all
; really folds every non-overlapping occurrence (a first-only reading of the left
; would give [2,1,1], which still differs from [2,3,3]).
; Oracle: SMT-LIB Sequences (seq.replace_all is all, not first-only).
(set-logic QF_SLIA)
(set-info :status unsat)
(declare-fun unused () (Seq Int))
(assert (= (seq.replace_all (seq.++ (seq.unit 1) (seq.unit 1) (seq.unit 1))
                            (seq.unit 1) (seq.unit 2))
           (seq.replace_all (seq.++ (seq.unit 2) (seq.unit 1) (seq.unit 1))
                            (seq.unit 1) (seq.unit 3))))
(check-sat)

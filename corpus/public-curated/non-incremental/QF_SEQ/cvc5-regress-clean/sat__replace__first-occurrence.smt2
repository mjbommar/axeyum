; (seq.replace [1,3,2,3] [3] [9]) = [1,9,2,3]: FIRST occurrence only (the second
; 3 is kept), length unchanged → sat.
; Oracle: SMT-LIB Sequences (replace first leftmost).
(set-logic QF_SLIA)
(set-info :status sat)
(declare-fun unused () (Seq Int))
(assert (= (seq.replace (seq.++ (seq.unit 1) (seq.unit 3) (seq.unit 2) (seq.unit 3))
                        (seq.unit 3) (seq.unit 9))
           (seq.++ (seq.unit 1) (seq.unit 9) (seq.unit 2) (seq.unit 3))))
(check-sat)

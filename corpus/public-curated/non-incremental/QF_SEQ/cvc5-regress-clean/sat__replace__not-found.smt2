; (seq.replace [1,2] [7] [9]) = [1,2]: `a`=[7] does not occur, so the sequence is
; unchanged → sat.
; Oracle: SMT-LIB Sequences (not found ⇒ unchanged).
(set-logic QF_SLIA)
(set-info :status sat)
(declare-fun unused () (Seq Int))
(assert (= (seq.replace (seq.++ (seq.unit 1) (seq.unit 2)) (seq.unit 7) (seq.unit 9))
           (seq.++ (seq.unit 1) (seq.unit 2))))
(check-sat)

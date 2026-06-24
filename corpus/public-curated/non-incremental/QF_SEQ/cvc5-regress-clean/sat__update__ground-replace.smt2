; (seq.update [1,2] 0 [9]) = [9,2] (in-bounds span replace, length unchanged) → sat.
; Oracle: SMT-LIB Sequences / cvc5 STRING_UPDATE.
(set-logic QF_SLIA)
(set-info :status sat)
(declare-fun unused () (Seq Int))
(assert (= (seq.update (seq.++ (seq.unit 1) (seq.unit 2)) 0 (seq.unit 9))
           (seq.++ (seq.unit 9) (seq.unit 2))))
(check-sat)

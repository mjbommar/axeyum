; (seq.update [1,2] 5 [9]) = [1,2] (out-of-bounds index → unchanged, total) → sat.
; Oracle: cvc5 STRING_UPDATE returns s unchanged when i<0 or i>=len(s).
(set-logic QF_SLIA)
(set-info :status sat)
(declare-fun unused () (Seq Int))
(assert (= (seq.update (seq.++ (seq.unit 1) (seq.unit 2)) 5 (seq.unit 9))
           (seq.++ (seq.unit 1) (seq.unit 2))))
(check-sat)

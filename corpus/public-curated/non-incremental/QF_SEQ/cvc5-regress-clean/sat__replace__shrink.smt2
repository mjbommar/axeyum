; (seq.replace [1,3,3,2] [3,3] [8]) = [1,8,2]: the first [3,3] span (len 2) is
; replaced by [8] (len 1), shrinking the sequence → sat.
; Oracle: SMT-LIB Sequences (multi-element match, length shrink).
(set-logic QF_SLIA)
(set-info :status sat)
(declare-fun unused () (Seq Int))
(assert (= (seq.replace (seq.++ (seq.unit 1) (seq.unit 3) (seq.unit 3) (seq.unit 2))
                        (seq.++ (seq.unit 3) (seq.unit 3)) (seq.unit 8))
           (seq.++ (seq.unit 1) (seq.unit 8) (seq.unit 2))))
(check-sat)

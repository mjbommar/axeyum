; (seq.replace_all [1,1,1] [1] [2]) = [2,2,2]: EVERY [1] becomes [2]. A ground
; fold; a first-only reading would give [2,1,1] ≠ [2,2,2] → sat asserts all.
; Oracle: SMT-LIB Sequences (seq.replace_all replaces all non-overlapping).
(set-logic QF_SLIA)
(set-info :status sat)
(declare-fun unused () (Seq Int))
(assert (= (seq.replace_all (seq.++ (seq.unit 1) (seq.unit 1) (seq.unit 1))
                            (seq.unit 1) (seq.unit 2))
           (seq.++ (seq.unit 2) (seq.unit 2) (seq.unit 2))))
(check-sat)

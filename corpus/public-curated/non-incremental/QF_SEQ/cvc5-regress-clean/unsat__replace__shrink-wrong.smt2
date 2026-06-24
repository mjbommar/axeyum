; (seq.replace [1,3,3,2] [3,3] [8]) = [1,8,2], NOT [1,8,8,2] (the span is removed,
; not kept) → the equality with [1,8,8,2] is unsatisfiable.
; Oracle: SMT-LIB Sequences (the matched span is replaced, not retained).
(set-logic QF_SLIA)
(set-info :status unsat)
(declare-fun unused () (Seq Int))
(assert (= (seq.replace (seq.++ (seq.unit 1) (seq.unit 3) (seq.unit 3) (seq.unit 2))
                        (seq.++ (seq.unit 3) (seq.unit 3)) (seq.unit 8))
           (seq.++ (seq.unit 1) (seq.unit 8) (seq.unit 8) (seq.unit 2))))
(check-sat)

; (seq.replace [1,3,2,3] [3] [9]) replaces ONLY the first 3, so it cannot equal
; [1,9,2,9] (both replaced). A replace-all reading would wrongly satisfy this →
; the equality is unsatisfiable.
; Oracle: SMT-LIB Sequences (replace is first-occurrence, not all).
(set-logic QF_SLIA)
(set-info :status unsat)
(declare-fun unused () (Seq Int))
(assert (= (seq.replace (seq.++ (seq.unit 1) (seq.unit 3) (seq.unit 2) (seq.unit 3))
                        (seq.unit 3) (seq.unit 9))
           (seq.++ (seq.unit 1) (seq.unit 9) (seq.unit 2) (seq.unit 9))))
(check-sat)

; (seq.indexof [1,3,2,3] [3] 2) = 3: at-or-after offset 2 the first [3] is at
; index 3 (the offset-0 occurrence at index 1 is skipped). A symbolic witness s
; ties the result to 3 → sat.
; Oracle: SMT-LIB Sequences (seq.indexof respects the start offset).
(set-logic QF_SLIA)
(set-info :status sat)
(declare-fun s () (Seq Int))
(assert (= s (seq.++ (seq.unit 1) (seq.unit 3) (seq.unit 2) (seq.unit 3))))
(assert (= (seq.indexof s (seq.unit 3) 2) 3))
(check-sat)

; (seq.indexof [1,3,2,3] [3] 0) = 1: the FIRST [3] is at index 1 (a symbolic
; witness s ties it). Length-preserving position search → sat.
; Oracle: SMT-LIB Sequences (seq.indexof first occurrence at-or-after i).
(set-logic QF_SLIA)
(set-info :status sat)
(declare-fun s () (Seq Int))
(assert (= s (seq.++ (seq.unit 1) (seq.unit 3) (seq.unit 2) (seq.unit 3))))
(assert (= (seq.indexof s (seq.unit 3) 0) 1))
(check-sat)

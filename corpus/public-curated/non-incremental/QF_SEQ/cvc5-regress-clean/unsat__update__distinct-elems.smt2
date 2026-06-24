; update [v]@0:=1 and update [v]@0:=2 over the SAME length-1 base, with #x0001 !=
; #x0002, cannot be equal → unsat (seq.update is a function of its arguments).
; Mirrors cvc5's distinct-update regression; BitVec(16) elements keep it pure-BV.
(set-logic QF_SLIA)
(set-info :status unsat)
(declare-fun x () (Seq (_ BitVec 16)))
(assert (= (seq.len x) 1))
(assert (= (seq.update x 0 (seq.unit #x0001)) (seq.update x 0 (seq.unit #x0002))))
(check-sat)

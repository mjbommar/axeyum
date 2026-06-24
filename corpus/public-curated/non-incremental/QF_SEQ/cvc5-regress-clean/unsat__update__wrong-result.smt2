; (seq.update [1,2] 0 [9]) = [1,2] is FALSE (slot 0 becomes 9) → unsat. A no-op
; model of seq.update would wrongly satisfy this. BitVec(16) elements keep it a
; pure-BV problem. Oracle: SMT-LIB Sequences / cvc5 STRING_UPDATE.
(set-logic QF_SLIA)
(set-info :status unsat)
(declare-fun unused () (Seq (_ BitVec 16)))
(assert (= (seq.update (seq.++ (seq.unit #x0001) (seq.unit #x0002)) 0 (seq.unit #x0009))
           (seq.++ (seq.unit #x0001) (seq.unit #x0002))))
(check-sat)

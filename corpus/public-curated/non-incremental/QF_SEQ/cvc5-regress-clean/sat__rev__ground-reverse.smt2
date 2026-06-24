; seq.rev of a ground sequence: rev([1,2,3]) = [3,2,1] (a true identity → sat).
; Oracle: SMT-LIB Sequences / cvc5 STRING_REV (reverse the present elements).
(set-logic QF_SLIA)
(set-info :status sat)
(declare-fun unused () (Seq Int))
(assert (= (seq.rev (seq.++ (seq.unit 1) (seq.++ (seq.unit 2) (seq.unit 3))))
           (seq.++ (seq.unit 3) (seq.++ (seq.unit 2) (seq.unit 1)))))
(check-sat)

; rev([1,2]) = [1,2] is FALSE (reversal is not the identity here) → unsat. A
; zero/no-op model of seq.rev would wrongly satisfy this; the real permutation
; makes it unsatisfiable. BitVec(16) elements keep it a pure-BV (bit-blastable)
; problem. Oracle: SMT-LIB Sequences / cvc5 STRING_REV.
(set-logic QF_SLIA)
(set-info :status unsat)
(declare-fun unused () (Seq (_ BitVec 16)))
(assert (= (seq.rev (seq.++ (seq.unit #x0001) (seq.unit #x0002)))
           (seq.++ (seq.unit #x0001) (seq.unit #x0002))))
(check-sat)

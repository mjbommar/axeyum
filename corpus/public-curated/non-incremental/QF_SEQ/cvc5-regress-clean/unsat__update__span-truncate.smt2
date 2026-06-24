; (seq.update [1,2,3] 2 [8,9]) = [1,2,8] (the 9 overhangs the end and is dropped);
; asserting the WRONG untruncated result [1,2,8,9-shaped] mismatch → unsat. Here
; we assert the wrong result [1,2,9] (slot 2 must be 8, not 9). Pure-BV. Oracle:
; cvc5 STRING_UPDATE (truncate the replacement span to fit within s).
(set-logic QF_SLIA)
(set-info :status unsat)
(declare-fun unused () (Seq (_ BitVec 16)))
(assert (= (seq.update (seq.++ (seq.unit #x0001) (seq.++ (seq.unit #x0002) (seq.unit #x0003)))
                       2 (seq.++ (seq.unit #x0008) (seq.unit #x0009)))
           (seq.++ (seq.unit #x0001) (seq.++ (seq.unit #x0002) (seq.unit #x0009)))))
(check-sat)

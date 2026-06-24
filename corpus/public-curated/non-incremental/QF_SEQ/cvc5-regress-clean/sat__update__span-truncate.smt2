; (seq.update [1,2,3] 2 [8,9]) = [1,2,8] (the replacement span is truncated to fit
; within s — the 9 overhangs and is dropped) → sat. Pure-BV. Oracle: cvc5
; STRING_UPDATE.
(set-logic QF_SLIA)
(set-info :status sat)
(declare-fun unused () (Seq (_ BitVec 16)))
(assert (= (seq.update (seq.++ (seq.unit #x0001) (seq.++ (seq.unit #x0002) (seq.unit #x0003)))
                       2 (seq.++ (seq.unit #x0008) (seq.unit #x0009)))
           (seq.++ (seq.unit #x0001) (seq.++ (seq.unit #x0002) (seq.unit #x0008)))))
(check-sat)

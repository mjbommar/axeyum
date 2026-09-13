; THE ELEMENT-SORT DISCRIMINATOR. `0 < m[i] < 1` is SAT over Real and UNSAT
; over Int, so an `unsat` here means the Real element sort was integralized
; somewhere on the array route. Its Int twin is `r3`.
; z3 4.13.3: sat. cvc5 1.3.4: sat.
(set-logic AUFLIRA)
(declare-fun m () (Array Int Real))
(declare-fun i () Int)
(assert (> (select m i) 0.0))
(assert (< (select m i) 1.0))
(check-sat)

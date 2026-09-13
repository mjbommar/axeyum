; UNSAT: store-then-read at the SAME index returns the written value, and the
; value is pinned to a non-integer rational so an Int-shaped abstraction of the
; element could not produce this refutation by accident.
; z3 4.13.3: unsat. cvc5 1.3.4: unsat.
(set-logic AUFLIRA)
(declare-fun m () (Array Int Real))
(declare-fun i () Int)
(declare-fun v () Real)
(assert (= v (/ 1.0 3.0)))
(assert (not (= (select (store m i v) i) v)))
(check-sat)

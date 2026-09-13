; Read-over-write at distinct symbolic indices, Real element, with the UF
; APPLIED TO THE ARRAY'S INDEX so the EUF+arithmetic combination cannot settle
; the query on its own and the array ladder is the route that has to.
; z3 4.13.3: unsat. cvc5 1.3.4: unsat.
(set-logic AUFLIRA)
(declare-fun m () (Array Int Real))
(declare-fun g (Int) Int)
(declare-fun i () Int)
(declare-fun j () Int)
(declare-fun v () Real)
(assert (= (g i) j))
(assert (not (= (select (store m i v) (g i))
                (ite (= i (g i)) v (select m (g i))))))
(check-sat)

; Negation of F:barber-no-such-barber. Recorded result: `unsat`, but with a BARE
; uncertified evidence object -- see that fact's notes. Not an evidence row.
(set-logic UF)
(declare-sort Person 0)
(declare-fun shaves (Person Person) Bool)
(assert (exists ((b Person)) (forall ((x Person)) (= (shaves b x) (not (shaves x x))))))
(check-sat)

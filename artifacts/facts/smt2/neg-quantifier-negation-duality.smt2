; Negation of F:quantifier-negation-duality. Recorded result: axeyum `unknown`,
; z3 `unsat`. Not an evidence row -- that fact is `open`.
(set-logic UF)
(declare-sort U 0)
(declare-fun P (U) Bool)
(assert (not (and (= (not (forall ((x U)) (P x))) (exists ((x U)) (not (P x))))
                  (= (not (exists ((x U)) (P x))) (forall ((x U)) (not (P x)))))))
(check-sat)

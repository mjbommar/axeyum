; QF_UF quotient-map congruence conflict for equivalence-classes-v0.
;
; If two elements are equal in the quotient carrier, any quotient map q must give
; them equal class labels. The final assertion demands the opposite, so the query
; is unsatisfiable by pure EUF congruence.
(set-logic QF_UF)
(declare-sort Element 0)
(declare-sort Class 0)
(declare-fun a () Element)
(declare-fun c () Element)
(declare-fun q (Element) Class)
(assert (= a c))
(assert (not (= (q a) (q c))))
(check-sat)

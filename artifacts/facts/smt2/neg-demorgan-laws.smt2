; Negation of F:de-morgan-laws -- `unsat` is the result recorded in that fact's
; evidence row. Generated verbatim from the fact's own `formal.statement`,
; so the two cannot drift.
(set-logic QF_UF)
(declare-const p Bool)
(declare-const q Bool)
(assert (not (and (= (not (and p q)) (or (not p) (not q))) (= (not (or p q)) (and (not p) (not q))))))
(check-sat)

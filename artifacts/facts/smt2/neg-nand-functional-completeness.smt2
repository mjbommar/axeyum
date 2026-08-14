; Negation of F:nand-functional-completeness -- `unsat` is the result recorded in that fact's
; evidence row. Generated verbatim from the fact's own `formal.statement`,
; so the two cannot drift.
(set-logic QF_UF)
(declare-const p Bool)
(declare-const q Bool)
(assert (not (and (= (not p) (not (and p p))) (= (and p q) (not (and (not (and p q)) (not (and p q))))) (= (or p q) (not (and (not (and p p)) (not (and q q))))))))
(check-sat)

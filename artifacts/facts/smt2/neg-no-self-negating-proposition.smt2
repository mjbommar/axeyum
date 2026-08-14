; Negation of F:no-self-negating-proposition -- `unsat` is the result recorded in that fact's
; evidence row. Generated verbatim from the fact's own `formal.statement`,
; so the two cannot drift.
(set-logic QF_UF)
(declare-const p Bool)
(assert (not (not (= p (not p)))))
(check-sat)

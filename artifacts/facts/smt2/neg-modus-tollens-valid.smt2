; Negation of F:modus-tollens-valid -- `unsat` is the result recorded in that fact's
; evidence row. Generated verbatim from the fact's own `formal.statement`,
; so the two cannot drift.
(set-logic QF_UF)
(declare-const p Bool)
(declare-const q Bool)
(assert (not (=> (and (=> p q) (not q)) (not p))))
(check-sat)

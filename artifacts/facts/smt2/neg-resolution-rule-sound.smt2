; Negation of F:resolution-rule-sound -- `unsat` is the result recorded in that fact's
; evidence row. Generated verbatim from the fact's own `formal.statement`,
; so the two cannot drift.
(set-logic QF_UF)
(declare-const p Bool)
(declare-const q Bool)
(declare-const r Bool)
(assert (not (=> (and (or p q) (or (not p) r)) (or q r))))
(check-sat)

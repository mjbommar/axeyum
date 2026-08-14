; Negation of F:double-negation-elimination -- `unsat` is the result recorded in that fact's
; evidence row. Generated verbatim from the fact's own `formal.statement`,
; so the two cannot drift.
(set-logic QF_UF)
(declare-const p Bool)
(assert (not (=> (not (not p)) p)))
(check-sat)

; Negation of F:ex-falso-quodlibet -- `unsat` is the result recorded in that fact's
; evidence row. Generated verbatim from the fact's own `formal.statement`,
; so the two cannot drift.
(set-logic QF_UF)
(declare-const p Bool)
(declare-const q Bool)
(assert (not (=> (and p (not p)) q)))
(check-sat)

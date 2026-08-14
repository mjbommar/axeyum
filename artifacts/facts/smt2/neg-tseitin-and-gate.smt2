; Negation of F:tseitin-and-gate -- `unsat` is the result recorded in that fact's
; evidence row. Generated verbatim from the fact's own `formal.statement`,
; so the two cannot drift.
(set-logic QF_UF)
(declare-const a Bool)
(declare-const b Bool)
(declare-const t Bool)
(assert (not (= (and (or (not t) a) (or (not t) b) (or t (not a) (not b))) (= t (and a b)))))
(check-sat)

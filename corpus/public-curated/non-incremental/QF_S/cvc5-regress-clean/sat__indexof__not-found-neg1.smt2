; "z" does not occur in "abc", so (str.indexof "abc" "z" 0) = -1. Asserting it
; equals -1 is satisfiable (the not-found corner).
; Oracle: SMT-LIB UnicodeStrings (str.indexof returns -1 when not found).
(set-logic QF_SLIA)
(set-info :status sat)
(declare-fun unused () String)
(assert (= (str.indexof "abc" "z" 0) (- 1)))
(check-sat)

; (str.replace_all "ababab" "ab" "X") = "XXX": ALL three "ab" are replaced, so it
; cannot equal "Xabab" (a first-only result). The equality to the first-only string
; is unsatisfiable.
; Oracle: SMT-LIB UnicodeStrings (str.replace_all is all, not first-only).
(set-logic QF_S)
(set-info :status unsat)
(declare-fun unused () String)
(assert (= (str.replace_all "ababab" "ab" "X") "Xabab"))
(check-sat)

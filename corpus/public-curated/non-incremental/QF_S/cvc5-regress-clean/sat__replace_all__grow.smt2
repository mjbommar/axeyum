; (str.replace_all "aaa" "a" "bb") = "bbbbbb": every "a" becomes "bb" (the result
; grows). A replace-FIRST reading would give "bbaa" ≠ "bbbbbb", so this asserts the
; all-occurrences semantics → sat.
; Oracle: SMT-LIB UnicodeStrings (str.replace_all replaces all non-overlapping).
(set-logic QF_S)
(set-info :status sat)
(declare-fun unused () String)
(assert (= (str.replace_all "aaa" "a" "bb") "bbbbbb"))
(check-sat)

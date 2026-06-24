; (str.indexof "abcabc" "bc" 2) = 4: the FIRST "bc" at-or-after offset 2 is at
; position 4 (the offset 0 occurrence at 1 is skipped). A symbolic guard ties the
; result to 4 → sat.
; Oracle: SMT-LIB UnicodeStrings (str.indexof first occurrence at-or-after i).
(set-logic QF_SLIA)
(set-info :status sat)
(declare-fun k () Int)
(assert (= k (str.indexof "abcabc" "bc" 2)))
(assert (= k 4))
(check-sat)

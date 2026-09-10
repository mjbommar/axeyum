; Vendored from cvc5 (BSD-3-Clause; (C) the cvc5 authors and contributors).
; Upstream path: test/regress/cli/regress1/strings/issue8944-sygus-inst.smt2
; Upstream commit: 1689f13331f7543801f82d9dcbcaac2f70a26781
; Source: https://github.com/cvc5/cvc5/blob/1689f13331f7543801f82d9dcbcaac2f70a26781/test/regress/cli/regress1/strings/issue8944-sygus-inst.smt2
; :status derived from upstream's own `; EXPECT: sat` test metadata (no `(set-info :status ...)` in the original file).

; COMMAND-LINE: --sygus-inst
; EXPECT: sat
(set-logic QF_SLIA)
(set-info :status sat)
(declare-fun s () String)
(declare-fun y () Int)
(assert (<= y 1))
(assert (distinct 1 (str.len (str.substr s 2 2))))
(assert (= 1 (str.len (str.substr s 1 1))))
(assert (= 1 (str.len (str.substr s 0 1))))
(assert (> (- (str.len s) 4) 0))
(assert (= "0" (str.at (str.substr s 3 (- (str.len s) 3)) 0)))
(assert (distinct 1 (str.len (str.substr s 3 (- (str.len s) 3)))))
(assert (str.in_re s (re.+ (re.range "0" "9"))))
(assert (not (str.is_digit (str.rev (str.replace_all (str.from_code y) "9" s)))))
(assert (= "0" (str.substr s 2 1)))
(check-sat)

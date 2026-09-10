; Vendored from cvc5 (BSD-3-Clause; (C) the cvc5 authors and contributors).
; Upstream path: test/regress/cli/regress1/strings/issue10195.smt2
; Upstream commit: 1689f13331f7543801f82d9dcbcaac2f70a26781
; Source: https://github.com/cvc5/cvc5/blob/1689f13331f7543801f82d9dcbcaac2f70a26781/test/regress/cli/regress1/strings/issue10195.smt2

(set-logic QF_SLIA)
(set-info :status sat)
(declare-fun r () String)
(assert (= (= r "T") (str.contains (str.update "Ty" (- (str.indexof_re r re.allchar (- 1))) (str.update r 0 r)) (str.from_int (- (str.indexof_re (str.replace_re_all r re.allchar r) re.none 0))))))
(check-sat)

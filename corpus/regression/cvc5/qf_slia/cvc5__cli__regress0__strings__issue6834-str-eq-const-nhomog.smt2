; Vendored from cvc5 (BSD-3-Clause; (C) the cvc5 authors and contributors).
; Upstream path: test/regress/cli/regress0/strings/issue6834-str-eq-const-nhomog.smt2
; Upstream commit: 1689f13331f7543801f82d9dcbcaac2f70a26781
; Source: https://github.com/cvc5/cvc5/blob/1689f13331f7543801f82d9dcbcaac2f70a26781/test/regress/cli/regress0/strings/issue6834-str-eq-const-nhomog.smt2

(set-logic QF_SLIA)
(declare-fun a () Int)
(assert (= (str.++ (str.substr "A" 0 a) "B" (str.substr "A" 0 a)) "B"))
(set-info :status sat)
(check-sat)

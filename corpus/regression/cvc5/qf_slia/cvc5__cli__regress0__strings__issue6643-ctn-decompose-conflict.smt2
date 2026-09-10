; Vendored from cvc5 (BSD-3-Clause; (C) the cvc5 authors and contributors).
; Upstream path: test/regress/cli/regress0/strings/issue6643-ctn-decompose-conflict.smt2
; Upstream commit: 1689f13331f7543801f82d9dcbcaac2f70a26781
; Source: https://github.com/cvc5/cvc5/blob/1689f13331f7543801f82d9dcbcaac2f70a26781/test/regress/cli/regress0/strings/issue6643-ctn-decompose-conflict.smt2

; COMMAND-LINE:
(set-logic QF_SLIA)
(declare-fun y () String)
(declare-fun z () String)
(assert (not (= (str.contains y (str.replace "A" "" z)) (str.contains y "A"))))
(set-info :status sat)
(check-sat)

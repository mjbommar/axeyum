; Vendored from cvc5 (BSD-3-Clause; (C) the cvc5 authors and contributors).
; Upstream path: test/regress/cli/regress0/strings/code-sat-neg-one.smt2
; Upstream commit: 1689f13331f7543801f82d9dcbcaac2f70a26781
; Source: https://github.com/cvc5/cvc5/blob/1689f13331f7543801f82d9dcbcaac2f70a26781/test/regress/cli/regress0/strings/code-sat-neg-one.smt2

(set-info :smt-lib-version 2.6)
(set-logic QF_SLIA)
(set-info :status sat)
(declare-fun x () String)
(declare-fun y () String)
(assert (not (= x y)))
(assert (= (str.to_code x) (str.to_code y)))
(check-sat)

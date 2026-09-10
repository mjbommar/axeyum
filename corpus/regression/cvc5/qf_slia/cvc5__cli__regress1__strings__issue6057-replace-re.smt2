; Vendored from cvc5 (BSD-3-Clause; (C) the cvc5 authors and contributors).
; Upstream path: test/regress/cli/regress1/strings/issue6057-replace-re.smt2
; Upstream commit: 1689f13331f7543801f82d9dcbcaac2f70a26781
; Source: https://github.com/cvc5/cvc5/blob/1689f13331f7543801f82d9dcbcaac2f70a26781/test/regress/cli/regress1/strings/issue6057-replace-re.smt2

(set-logic QF_SLIA)
(declare-fun a () String)
(assert (str.suffixof "a" a))
(assert (str.in_re a (re.* (re.union (str.to_re (str.replace_re a (re.++ (re.* (str.to_re "a")) (str.to_re "ba")) "")) (str.to_re "b")))))
(assert (str.in_re a (re.++ (re.* (str.to_re (ite (str.in_re a (re.* (str.to_re "b"))) "" "u"))) (re.* (str.to_re a)))))
(set-info :status sat)
(check-sat)

; Vendored from cvc5 (BSD-3-Clause; (C) the cvc5 authors and contributors).
; Upstream path: test/regress/cli/regress1/strings/issue6203-6-replace-re.smt2
; Upstream commit: 1689f13331f7543801f82d9dcbcaac2f70a26781
; Source: https://github.com/cvc5/cvc5/blob/1689f13331f7543801f82d9dcbcaac2f70a26781/test/regress/cli/regress1/strings/issue6203-6-replace-re.smt2

; COMMAND-LINE:
(set-logic QF_SLIA)
(declare-fun a () String)
(assert (not (str.in_re (str.replace_re a (re.++ (re.* (re.union (str.to_re "a") (str.to_re ""))) (str.to_re "b")) "") (str.to_re ""))))
(assert (ite (str.in_re a (re.diff (re.* (re.union (str.to_re "a") (str.to_re "b"))) (re.range "a" "u")))
    (str.in_re a (re.diff (re.* (re.union (str.to_re "a") (str.to_re "b"))) (re.range "a" "u")))
    (str.<= a "b")))
(set-info :status sat)
(check-sat)

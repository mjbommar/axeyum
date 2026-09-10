; Vendored from cvc5 (BSD-3-Clause; (C) the cvc5 authors and contributors).
; Upstream path: test/regress/cli/regress1/strings/issue6057-replace-re-all-jiwonparc.smt2
; Upstream commit: 1689f13331f7543801f82d9dcbcaac2f70a26781
; Source: https://github.com/cvc5/cvc5/blob/1689f13331f7543801f82d9dcbcaac2f70a26781/test/regress/cli/regress1/strings/issue6057-replace-re-all-jiwonparc.smt2

; COMMAND-LINE:
(set-logic QF_SLIA)
(declare-fun a () String)
; A complicated way of saying a = "b"
(assert (str.in_re a (re.++ (re.* (re.opt (str.to_re a))) (str.to_re "b"))))
; Corresponds to replace_re_all("ab", a*b, "") contains "a"
(assert (str.contains (str.replace_re_all (str.++ "a" a) (re.++ (re.* (str.to_re "a")) (str.to_re "b")) "") "a"))
(set-info :status unsat)
(check-sat)

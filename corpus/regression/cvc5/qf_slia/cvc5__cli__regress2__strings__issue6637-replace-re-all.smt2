; Vendored from cvc5 (BSD-3-Clause; (C) the cvc5 authors and contributors).
; Upstream path: test/regress/cli/regress2/strings/issue6637-replace-re-all.smt2
; Upstream commit: 1689f13331f7543801f82d9dcbcaac2f70a26781
; Source: https://github.com/cvc5/cvc5/blob/1689f13331f7543801f82d9dcbcaac2f70a26781/test/regress/cli/regress2/strings/issue6637-replace-re-all.smt2

; COMMAND-LINE:
(set-logic QF_SLIA)
(declare-fun a () String)
(assert (= (str.len a) 2))
(assert (= (str.len (str.replace_re_all a (str.to_re "A") "B")) 3))
(set-info :status unsat)
(check-sat)

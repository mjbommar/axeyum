; Vendored from cvc5 (BSD-3-Clause; (C) the cvc5 authors and contributors).
; Upstream path: test/regress/cli/regress0/strings/re-in-rewrite.smt2
; Upstream commit: 1689f13331f7543801f82d9dcbcaac2f70a26781
; Source: https://github.com/cvc5/cvc5/blob/1689f13331f7543801f82d9dcbcaac2f70a26781/test/regress/cli/regress0/strings/re-in-rewrite.smt2

(set-logic QF_SLIA)
(set-info :status unsat)
(declare-fun x () String)
(assert (str.in_re x (re.inter (re.comp (re.++ re.allchar (re.* re.allchar))) (re.++ (str.to_re "a") (re.* re.allchar)))))
(check-sat)

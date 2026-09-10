; Vendored from cvc5 (BSD-3-Clause; (C) the cvc5 authors and contributors).
; Upstream path: test/regress/cli/regress1/strings/simple-re-consume.smt2
; Upstream commit: 1689f13331f7543801f82d9dcbcaac2f70a26781
; Source: https://github.com/cvc5/cvc5/blob/1689f13331f7543801f82d9dcbcaac2f70a26781/test/regress/cli/regress1/strings/simple-re-consume.smt2

(set-info :smt-lib-version 2.6)
(set-logic QF_SLIA)
(set-info :status sat)
(declare-fun x () String)
(assert (str.in_re (str.++ "bbbbbbbb" x) (re.* (re.++ (str.to_re "bbbb") (re.* (str.to_re "aaaa"))))))
(check-sat)

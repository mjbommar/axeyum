; Vendored from cvc5 (BSD-3-Clause; (C) the cvc5 authors and contributors).
; Upstream path: test/regress/cli/regress1/strings/str-code-unsat-2.smt2
; Upstream commit: 1689f13331f7543801f82d9dcbcaac2f70a26781
; Source: https://github.com/cvc5/cvc5/blob/1689f13331f7543801f82d9dcbcaac2f70a26781/test/regress/cli/regress1/strings/str-code-unsat-2.smt2

(set-logic QF_SLIA)
(set-info :status unsat)
(declare-fun x () String)
(assert (= (str.len x) 1))
(assert (or (< (str.to_code x) 0) (> (str.to_code x) 10000000000000000000000000000)))
(check-sat)

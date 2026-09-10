; Vendored from cvc5 (BSD-3-Clause; (C) the cvc5 authors and contributors).
; Upstream path: test/regress/cli/regress0/strings/indexof_re-start-index.smt2
; Upstream commit: 1689f13331f7543801f82d9dcbcaac2f70a26781
; Source: https://github.com/cvc5/cvc5/blob/1689f13331f7543801f82d9dcbcaac2f70a26781/test/regress/cli/regress0/strings/indexof_re-start-index.smt2

; COMMAND-LINE:
(set-logic QF_SLIA)
(declare-fun i () Int)
(declare-fun a () String)
(assert (= i (str.indexof_re a (str.to_re "abc") 3)))
(assert (and (>= i 0) (< i 3)))
(set-info :status unsat)
(check-sat)

; Vendored from cvc5 (BSD-3-Clause; (C) the cvc5 authors and contributors).
; Upstream path: test/regress/cli/regress0/seq/seq-nemp.smt2
; Upstream commit: 1689f13331f7543801f82d9dcbcaac2f70a26781
; Source: https://github.com/cvc5/cvc5/blob/1689f13331f7543801f82d9dcbcaac2f70a26781/test/regress/cli/regress0/seq/seq-nemp.smt2

(set-logic QF_SLIA)
(set-info :status sat)
(declare-fun x () (Seq Int))
(assert (not (= x (as seq.empty (Seq Int)))))
(assert (= (seq.len x) 16))
(check-sat)

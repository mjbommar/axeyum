; Vendored from cvc5 (BSD-3-Clause; (C) the cvc5 authors and contributors).
; Upstream path: test/regress/cli/regress0/seq/seq-ex5.smt2
; Upstream commit: 1689f13331f7543801f82d9dcbcaac2f70a26781
; Source: https://github.com/cvc5/cvc5/blob/1689f13331f7543801f82d9dcbcaac2f70a26781/test/regress/cli/regress0/seq/seq-ex5.smt2

(set-logic QF_SLIA)

(set-info :status sat)
(declare-fun z () (Seq Int))
(declare-fun w () (Seq Int))
(declare-fun i () Int)
(assert (> i 777))
(assert (not (= (seq.replace z (seq.unit i) w) z)))
(check-sat)

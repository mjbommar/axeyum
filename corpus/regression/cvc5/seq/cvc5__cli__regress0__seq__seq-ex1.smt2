; Vendored from cvc5 (BSD-3-Clause; (C) the cvc5 authors and contributors).
; Upstream path: test/regress/cli/regress0/seq/seq-ex1.smt2
; Upstream commit: 1689f13331f7543801f82d9dcbcaac2f70a26781
; Source: https://github.com/cvc5/cvc5/blob/1689f13331f7543801f82d9dcbcaac2f70a26781/test/regress/cli/regress0/seq/seq-ex1.smt2

(set-logic QF_UFSLIA)
(set-info :status sat)
(declare-fun x () (Seq Int))
(declare-fun y () (Seq Int))
(declare-fun f ((Seq Int)) (Seq Bool))

(assert (not (= x y)))
(assert (not (= (f x) (f y))))

(check-sat)

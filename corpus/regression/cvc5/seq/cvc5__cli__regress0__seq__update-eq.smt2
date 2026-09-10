; Vendored from cvc5 (BSD-3-Clause; (C) the cvc5 authors and contributors).
; Upstream path: test/regress/cli/regress0/seq/update-eq.smt2
; Upstream commit: 1689f13331f7543801f82d9dcbcaac2f70a26781
; Source: https://github.com/cvc5/cvc5/blob/1689f13331f7543801f82d9dcbcaac2f70a26781/test/regress/cli/regress0/seq/update-eq.smt2

; REQUIRES: unrestricted-mode
; COMMAND-LINE: --seq-array=lazy
(set-logic QF_UFSLIA)
(declare-sort E 0)
(declare-fun x () (Seq E))
(declare-fun y () (Seq E))
(assert (= y (seq.update x 0 (seq.unit (seq.nth x 0)))))
(assert (distinct (seq.nth x 1) (seq.nth y 1)))
(set-info :status unsat)
(check-sat)

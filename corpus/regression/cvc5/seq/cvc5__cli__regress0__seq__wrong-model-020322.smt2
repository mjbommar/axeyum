; Vendored from cvc5 (BSD-3-Clause; (C) the cvc5 authors and contributors).
; Upstream path: test/regress/cli/regress0/seq/wrong-model-020322.smt2
; Upstream commit: 1689f13331f7543801f82d9dcbcaac2f70a26781
; Source: https://github.com/cvc5/cvc5/blob/1689f13331f7543801f82d9dcbcaac2f70a26781/test/regress/cli/regress0/seq/wrong-model-020322.smt2

; REQUIRES: unrestricted-mode
; COMMAND-LINE: --seq-array=lazy
; EXPECT: sat
(set-logic ALL)
(set-info :status sat)
(declare-sort E 0)
(declare-fun k () E)
(declare-fun s () (Seq E))
(declare-fun j () Int)
(assert (distinct (distinct s (str.update s j (seq.unit (seq.nth s 1)))) (distinct s (str.update (str.update s 0 (seq.unit k)) j (seq.unit (seq.nth s 1))))))
(check-sat)

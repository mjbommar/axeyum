; Vendored from cvc5 (BSD-3-Clause; (C) the cvc5 authors and contributors).
; Upstream path: test/regress/cli/regress0/seq/proj-issue653.smt2
; Upstream commit: 1689f13331f7543801f82d9dcbcaac2f70a26781
; Source: https://github.com/cvc5/cvc5/blob/1689f13331f7543801f82d9dcbcaac2f70a26781/test/regress/cli/regress0/seq/proj-issue653.smt2

; COMMAND-LINE: -q
; EXPECT: sat
(set-logic ALL)
(set-info :status sat)
(declare-const x (Set Bool))
(declare-const x1 (Seq (Set Bool)))
(declare-const x4 (Set (Seq (Set Bool))))
(assert (distinct (set.choose x4) (set.choose (set.singleton x1)) (seq.unit (set.minus x (set.singleton false)))))
(check-sat)

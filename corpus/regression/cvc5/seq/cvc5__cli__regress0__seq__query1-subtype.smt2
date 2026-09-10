; Vendored from cvc5 (BSD-3-Clause; (C) the cvc5 authors and contributors).
; Upstream path: test/regress/cli/regress0/seq/query1-subtype.smt2
; Upstream commit: 1689f13331f7543801f82d9dcbcaac2f70a26781
; Source: https://github.com/cvc5/cvc5/blob/1689f13331f7543801f82d9dcbcaac2f70a26781/test/regress/cli/regress0/seq/query1-subtype.smt2
; :status derived from upstream's own `; EXPECT: sat` test metadata (no `(set-info :status ...)` in the original file).

; COMMAND-LINE: --simplification=none
; EXPECT: sat
(set-logic ALL)
(set-info :status sat)
(declare-fun x () (Seq Real))
(declare-fun y () (Seq Real))
(declare-fun a () Real)
(declare-fun b () Real)
(assert
(and (= x (seq.unit b)) (= x (str.update y 2 y)) (= x (str.update y 1 x)) (= x (seq.unit 1.0)) (= x (str.update y 1 (as seq.empty (Seq Real)))))
)
(check-sat)

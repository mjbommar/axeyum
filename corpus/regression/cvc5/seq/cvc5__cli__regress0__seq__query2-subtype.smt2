; Vendored from cvc5 (BSD-3-Clause; (C) the cvc5 authors and contributors).
; Upstream path: test/regress/cli/regress0/seq/query2-subtype.smt2
; Upstream commit: 1689f13331f7543801f82d9dcbcaac2f70a26781
; Source: https://github.com/cvc5/cvc5/blob/1689f13331f7543801f82d9dcbcaac2f70a26781/test/regress/cli/regress0/seq/query2-subtype.smt2
; :status derived from upstream's own `; EXPECT: sat` test metadata (no `(set-info :status ...)` in the original file).

; REQUIRES: unrestricted-mode
; COMMAND-LINE: --simplification=none --strings-fmf
; EXPECT: sat
(set-logic ALL)
(set-info :status sat)
(declare-fun x () (Seq Real))
(declare-fun y () (Seq Real))
(declare-fun a () Real)
(declare-fun b () Real)
(assert
(and (not (= (= x (str.update x 2 (seq.unit 1.0))) (= x (str.update x 2 (str.update x 0 y))))) (not (= b (seq.nth x 2))))
)
(check-sat)

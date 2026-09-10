; Vendored from cvc5 (BSD-3-Clause; (C) the cvc5 authors and contributors).
; Upstream path: test/regress/cli/regress0/seq/issue5543-unit-cmv.smt2
; Upstream commit: 1689f13331f7543801f82d9dcbcaac2f70a26781
; Source: https://github.com/cvc5/cvc5/blob/1689f13331f7543801f82d9dcbcaac2f70a26781/test/regress/cli/regress0/seq/issue5543-unit-cmv.smt2
; :status derived from upstream's own `; EXPECT: sat` test metadata (no `(set-info :status ...)` in the original file).

; COMMAND-LINE:
; EXPECT: sat
(set-logic ALL)
(set-info :status sat)
(declare-fun a () (Seq (Seq Int)))
(declare-fun b () (Seq (Seq Int)))
(declare-fun c () (Seq (Seq Int)))
(declare-fun d () (Seq (Seq Int)))
(declare-fun e () (Seq Int))
(declare-fun f () (Seq Int))
(assert (distinct a (seq.++ (seq.unit e) b)))
(assert (= (seq.++ (seq.unit f) d) a c))
(check-sat)

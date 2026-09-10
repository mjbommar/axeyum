; Vendored from cvc5 (BSD-3-Clause; (C) the cvc5 authors and contributors).
; Upstream path: test/regress/cli/regress1/seq/issue8936-nth-eager-red.smt2
; Upstream commit: 1689f13331f7543801f82d9dcbcaac2f70a26781
; Source: https://github.com/cvc5/cvc5/blob/1689f13331f7543801f82d9dcbcaac2f70a26781/test/regress/cli/regress1/seq/issue8936-nth-eager-red.smt2
; :status derived from upstream's own `; EXPECT: unsat` test metadata (no `(set-info :status ...)` in the original file).

; REQUIRES: no-safe-mode
; COMMAND-LINE: --no-strings-lazy-pp
; EXPECT: unsat
(set-logic ALL)
(set-info :status unsat)
(declare-fun a () (Seq Int))
(declare-fun b () (Seq Int))
(declare-fun c () Int)
(assert (= a b))
(assert (not (= (seq.nth a c) (seq.nth b c))))
(check-sat)

; Vendored from cvc5 (BSD-3-Clause; (C) the cvc5 authors and contributors).
; Upstream path: test/regress/cli/regress1/seq/issue8148-const-mv.smt2
; Upstream commit: 1689f13331f7543801f82d9dcbcaac2f70a26781
; Source: https://github.com/cvc5/cvc5/blob/1689f13331f7543801f82d9dcbcaac2f70a26781/test/regress/cli/regress1/seq/issue8148-const-mv.smt2

; REQUIRES: no-safe-mode
; COMMAND-LINE:
; EXPECT: sat
(set-logic ALL)
(set-info :status sat)
(set-option :re-elim agg)
(declare-fun e!0 () (Seq Bool))
(assert (= e!0 seq.empty))
(assert (seq.nth e!0 0))
(check-sat)

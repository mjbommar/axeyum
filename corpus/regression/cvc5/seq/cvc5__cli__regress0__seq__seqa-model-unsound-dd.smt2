; Vendored from cvc5 (BSD-3-Clause; (C) the cvc5 authors and contributors).
; Upstream path: test/regress/cli/regress0/seq/seqa-model-unsound-dd.smt2
; Upstream commit: 1689f13331f7543801f82d9dcbcaac2f70a26781
; Source: https://github.com/cvc5/cvc5/blob/1689f13331f7543801f82d9dcbcaac2f70a26781/test/regress/cli/regress0/seq/seqa-model-unsound-dd.smt2
; :status derived from upstream's own `; EXPECT: unsat` test metadata (no `(set-info :status ...)` in the original file).

; REQUIRES: unrestricted-mode
; COMMAND-LINE: --seq-array=eager
; EXPECT: unsat
(set-logic ALL)
(set-info :status unsat)
(declare-sort T 0)
(declare-fun t () T)
(declare-fun s (T) (Seq (Seq Int)))
(declare-fun u () (Seq Int))
(assert (= (seq.unit u) (s t)))
(assert (distinct u (seq.nth (s t) (- 1 (seq.len (s t))))))
(check-sat)

; Vendored from cvc5 (BSD-3-Clause; (C) the cvc5 authors and contributors).
; Upstream path: test/regress/cli/regress0/seq/proj-issue665-nested-const.smt2
; Upstream commit: 1689f13331f7543801f82d9dcbcaac2f70a26781
; Source: https://github.com/cvc5/cvc5/blob/1689f13331f7543801f82d9dcbcaac2f70a26781/test/regress/cli/regress0/seq/proj-issue665-nested-const.smt2
; :status derived from upstream's own `; EXPECT: sat` test metadata (no `(set-info :status ...)` in the original file).

; EXPECT: sat
(set-logic ALL)
(set-info :status sat)
(declare-const _x (Seq Bool))
(declare-const x3 (Seq Bool))
(declare-const x (Seq Bool))
(assert (not (seq.contains x x3)))
(declare-const x1 (Seq (Seq (Seq Bool))))
(assert (seq.contains x (seq.replace _x x x3)))
(assert (seq.suffixof x1 (seq.unit (seq.unit (seq.unit false)))))
(check-sat)

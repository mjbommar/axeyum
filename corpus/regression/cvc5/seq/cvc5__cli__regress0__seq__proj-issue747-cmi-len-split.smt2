; Vendored from cvc5 (BSD-3-Clause; (C) the cvc5 authors and contributors).
; Upstream path: test/regress/cli/regress0/seq/proj-issue747-cmi-len-split.smt2
; Upstream commit: 1689f13331f7543801f82d9dcbcaac2f70a26781
; Source: https://github.com/cvc5/cvc5/blob/1689f13331f7543801f82d9dcbcaac2f70a26781/test/regress/cli/regress0/seq/proj-issue747-cmi-len-split.smt2
; :status derived from upstream's own `; EXPECT: sat` test metadata (no `(set-info :status ...)` in the original file).

; EXPECT: sat
(set-logic ALL)
(set-info :status sat)
(declare-const x (Seq Bool))
(declare-const x1 (Seq Bool))
(assert (seq.suffixof (seq.replace_all x1 x (seq.unit (seq.suffixof x1 (seq.++ x1 x1)))) x))
(assert (distinct x (seq.++ x1 x)))
(check-sat)

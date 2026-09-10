; Vendored from cvc5 (BSD-3-Clause; (C) the cvc5 authors and contributors).
; Upstream path: test/regress/cli/regress0/seq/issue5547-seq-len-unit.smt2
; Upstream commit: 1689f13331f7543801f82d9dcbcaac2f70a26781
; Source: https://github.com/cvc5/cvc5/blob/1689f13331f7543801f82d9dcbcaac2f70a26781/test/regress/cli/regress0/seq/issue5547-seq-len-unit.smt2
; :status derived from upstream's own `; EXPECT: sat` test metadata (no `(set-info :status ...)` in the original file).

; COMMAND-LINE:
; EXPECT: sat
(set-logic QF_SLIA)
(set-info :status sat)
(declare-fun seq3 () (Seq Int))
(declare-fun seq10 () (Seq Int))
(declare-fun seq12 () (Seq Int))
(assert (seq.suffixof (seq.++ (seq.unit (seq.len (seq.++ seq12 (seq.rev seq3)))) seq3) seq10))
(check-sat)

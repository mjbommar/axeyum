; Vendored from cvc5 (BSD-3-Clause; (C) the cvc5 authors and contributors).
; Upstream path: test/regress/cli/regress0/seq/array/model-dd-1220.smt2
; Upstream commit: 1689f13331f7543801f82d9dcbcaac2f70a26781
; Source: https://github.com/cvc5/cvc5/blob/1689f13331f7543801f82d9dcbcaac2f70a26781/test/regress/cli/regress0/seq/array/model-dd-1220.smt2

; REQUIRES: unrestricted-mode
; COMMAND-LINE: --seq-array=lazy
; EXPECT: sat
(set-logic ALL)
(set-info :status sat)
(declare-fun v () (Seq Int))
(assert (= 1 (seq.len v)))
(assert (= v (seq.update v 0 (seq.unit 1))))
(check-sat)

; Vendored from cvc5 (BSD-3-Clause; (C) the cvc5 authors and contributors).
; Upstream path: test/regress/cli/regress0/seq/proj-issue559-unit-inj.smt2
; Upstream commit: 1689f13331f7543801f82d9dcbcaac2f70a26781
; Source: https://github.com/cvc5/cvc5/blob/1689f13331f7543801f82d9dcbcaac2f70a26781/test/regress/cli/regress0/seq/proj-issue559-unit-inj.smt2

(set-logic ALL)
(set-info :status unsat)
(declare-const x String)
(declare-const x8 (Seq String))
(assert (ite (seq.prefixof (seq.unit x) x8) false true))
(assert (seq.suffixof (seq.unit true) (seq.unit (seq.prefixof (seq.unit x8) (seq.unit (seq.unit x))))))
(check-sat)

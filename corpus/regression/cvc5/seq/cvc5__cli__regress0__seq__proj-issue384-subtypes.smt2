; Vendored from cvc5 (BSD-3-Clause; (C) the cvc5 authors and contributors).
; Upstream path: test/regress/cli/regress0/seq/proj-issue384-subtypes.smt2
; Upstream commit: 1689f13331f7543801f82d9dcbcaac2f70a26781
; Source: https://github.com/cvc5/cvc5/blob/1689f13331f7543801f82d9dcbcaac2f70a26781/test/regress/cli/regress0/seq/proj-issue384-subtypes.smt2

; REQUIRES: unrestricted-mode
(set-logic ALL)
(set-info :status unsat)
(set-option :global-declarations true)

(assert (let ((_let0 (seq.unit real.pi)))(seq.suffixof _let0 (seq.update _let0 (seq.len _let0) _let0))))
(assert (let ((_let0 real.pi))(let ((_let1 (- _let0)))(let ((_let2 (+ _let1 _let0)))(>= _let1 (* _let2 _let2) _let1)))))
(check-sat)

; Vendored from cvc5 (BSD-3-Clause; (C) the cvc5 authors and contributors).
; Upstream path: test/regress/cli/regress3/strings/issue8926-sygus-inst.smt2
; Upstream commit: 1689f13331f7543801f82d9dcbcaac2f70a26781
; Source: https://github.com/cvc5/cvc5/blob/1689f13331f7543801f82d9dcbcaac2f70a26781/test/regress/cli/regress3/strings/issue8926-sygus-inst.smt2
; :status derived from upstream's own `; EXPECT: sat` test metadata (no `(set-info :status ...)` in the original file).

; COMMAND-LINE: --sygus-inst
; EXPECT: sat
(set-logic QF_SLIA)
(set-info :status sat)
(declare-fun tstr () String)
(assert (ite (str.prefixof "-" (str.substr tstr 0 (- (+ 0 2) 0))) (and (ite (= (- 1) (str.to_int (str.substr (str.substr tstr 0 (- (+ 0 2) 0)) 1 (- (str.len (str.substr tstr 0 (- (+ 0 2) 0))) 1)))) false true) (> (str.len (str.substr tstr 0 (- (+ 0 2) 0))) 1)) (ite (= (- 1) (str.to_int (str.substr tstr 0 (- (+ 0 2) 0)))) false true)))
(assert (not (< (str.len tstr) (str.to_code (str.rev tstr)))))
(assert (>= 3 (str.len tstr)))
(check-sat)

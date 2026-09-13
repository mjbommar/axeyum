; Array EXTENSIONALITY with a Real element sort and a UF present, so the query
; reaches `dispatch_uf_routes` (gate 2) rather than the pure-real branch
; (gate 1). `b = store(a,i,v)` forces `b[i] = v`.
; z3 4.13.3: unsat. cvc5 1.3.4: unsat.
(set-logic AUFLIRA)
(declare-fun a () (Array Int Real))
(declare-fun b () (Array Int Real))
(declare-fun g (Int) Int)
(declare-fun i () Int)
(declare-fun v () Real)
(assert (> (g i) 0))
(assert (= b (store a i v)))
(assert (not (= (select b i) v)))
(check-sat)
